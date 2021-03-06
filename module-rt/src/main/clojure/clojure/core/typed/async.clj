(ns 
  ^{:doc 
    "This namespace contains annotations and helper macros for type
    checking core.async code. Ensure clojure.core.async is require'd
    before performing type checking.
    
    go
      use go

    chan
      use chan

    buffer
      use buffer> (similar for other buffer constructors)
    "}
  clojure.core.typed.async
  (:require [clojure.core.typed :refer [ann ann-datatype defalias inst ann-protocol
                                        AnyInteger tc-ignore Seqable TFn IFn Any I]
             :as t]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.async :as async]
            [clojure.tools.analyzer.jvm :as ana]
            [clojure.core.async.impl.protocols :as impl]
            [clojure.core.async.impl.channels :as channels]
            [clojure.core.async.impl.dispatch :as dispatch]
            [clojure.core.async.impl.ioc-macros :as ioc] 
            )

  (:import (java.util.concurrent Executor)
           (java.util.concurrent.locks Lock)
           (java.util.concurrent.atomic AtomicReferenceArray)
           (clojure.lang IDeref)))

;TODO how do we encode that nil is illegal to provide to Ports/Channels?
;     Is it essential?

;;;;;;;;;;;;;;;;;;;;
;; Protocols

(ann-protocol clojure.core.async.impl.protocols/Channel
              close! [impl/Channel -> nil])

(ann-protocol [[r :variance :covariant]]
              clojure.core.async.impl.protocols/ReadPort
              take! [(impl/ReadPort r) Lock 
                     -> (t/U nil (IDeref (t/U nil r)))])

(ann-protocol [[w :variance :contravariant]]
              clojure.core.async.impl.protocols/WritePort
              put! [(impl/WritePort w) w Lock
                    -> (t/U nil (IDeref nil))])

(ann-protocol [[w :variance :contravariant]
               [r :variance :covariant]]
               clojure.core.async.impl.protocols/Buffer)

(ann-datatype [[w :variance :contravariant]
               [r :variance :covariant]]
              clojure.core.async.impl.channels.ManyToManyChannel 
              []
              :unchecked-ancestors [impl/Channel
                                    (impl/ReadPort r)
                                    (impl/WritePort w)])

;;;;;;;;;;;;;;;;;;;;
;; Aliases

(defalias 
  ^{:forms [(Port2 t t)]}
  Port2
  "A port that can read type p and write type t"
  (TFn [[p :variance :contravariant]
        [t :variance :covariant]]
    (I (impl/ReadPort t) 
       (impl/WritePort p))))

(defalias 
  ^{:forms [(Port t)]}
  Port
  "A port that can read and write type x"
  (TFn [[x :variance :invariant]]
    (Port2 x x)))

(defalias 
  ^{:forms '[(Chan2 t t)]}
  Chan2
  "A core.async channel that can take type w and put type r"
  (TFn [[p :variance :contravariant]
        [t :variance :covariant]]
    (I (Port2 p t)
       impl/Channel)))

(defalias 
  ^{:forms '[(Chan t)]}
  Chan
  "A core.async channel"
  (TFn [[x :variance :invariant]]
    (Chan2 x x)))

(defalias 
  ^{:forms '[(ReadOnlyChan t)]}
  ReadOnlyChan
  "A core.async channel that statically disallows writes."
  (TFn [[r :variance :covariant]]
    (Chan2 t/Nothing r)))

(defalias 
  ^{:forms [(ReadOnlyPort t)]}
  ReadOnlyPort
  "A read-only port that can read type x"
  (TFn [[t :variance :covariant]]
    (Port2 t/Nothing t)))

(defalias 
  ^{:forms [(WriteOnlyPort t)]}
  WriteOnlyPort
  "A write-only port that can write type p"
  (TFn [[p :variance :contravariant]]
    (Port2 p t/Nothing)))

(defalias
  ^{:forms [TimeoutChan]}
  TimeoutChan
  "A timeout channel"
  (Chan Any))

(defalias 
  ^{:forms [(Buffer2 t t)]}
  Buffer2
  "A buffer of type x."
  (TFn [[w :variance :contravariant]
        [r :variance :covariant]]
    (impl/Buffer w r)))

(defalias 
  ^{:forms [(Buffer t)]}
  Buffer
  "A buffer of type x."
  (TFn [[x :variance :invariant]]
    (Buffer2 x x)))

;;;;;;;;;;;;;;;;;;;;
;; Var annotations

(ann ^:no-check clojure.core.async/buffer (t/All [w r] [t/Int :-> (Buffer2 w r)]))
(ann ^:no-check clojure.core.async/dropping-buffer (t/All [w r] [t/Int :-> (Buffer w r)]))
(ann ^:no-check clojure.core.async/sliding-buffer (t/All [w r] [t/Int :-> (Buffer w r)]))

(ann ^:no-check clojure.core.async/thread-call (t/All [x] [[:-> x] :-> (Chan x)]))

(ann ^:no-check clojure.core.async/timeout [t/Int :-> TimeoutChan])

(ann ^:no-check clojure.core.async/chan (t/All [p t]
                                            (IFn [:-> (Chan2 p t)]
                                                 [(t/U (Buffer2 p t) t/Int) :-> (Chan2 p t)])))

(ann ^:no-check clojure.core.async.impl.ioc-macros/aget-object [AtomicReferenceArray t/Int :-> Any])
(ann ^:no-check clojure.core.async.impl.ioc-macros/aset-object [AtomicReferenceArray Any :-> nil])
(ann ^:no-check clojure.core.async.impl.ioc-macros/run-state-machine [AtomicReferenceArray :-> Any])

;FIXME what is 2nd arg?
(ann ^:no-check clojure.core.async.impl.ioc-macros/put! (t/All [x] [t/Int Any (Chan x) x :-> Any]))
(ann ^:no-check clojure.core.async.impl.ioc-macros/return-chan (t/All [x] [AtomicReferenceArray x :-> (Chan x)]))

(ann ^:no-check clojure.core.async/<!! (t/All [t] [(ReadOnlyPort t) :-> (t/U nil t)]))
(ann ^:no-check clojure.core.async/<! (t/All [p t] [(Chan2 p t) :-> (Chan2 p t)]))
(ann ^:no-check clojure.core.async/>!! (t/All [p [a :< p]] [(Port2 p Any) a :-> Any]))
(ann ^:no-check clojure.core.async/>! (t/All [p t [a :< p]] [(Chan2 p t) a :-> (Chan2 p t)]))
(t/ann-many 
  (t/All [x d]
         (IFn [(Seqable (t/U (Port x) '[(Port x) x])) 
               (Seqable (Port x)) 
               & :mandatory {:default d} 
               :optional {:priority (t/U nil true)} 
               :-> (t/U '[d ':default] '[(t/U nil x) (Port x)])]
              [(Seqable (t/U (Port x) '[(Port x) x])) 
               & :optional {:priority (t/U nil true)} 
               :-> '[(t/U nil x) (Port x)]]))
  ^:no-check clojure.core.async/alts!!
  ^:no-check clojure.core.async/alts!)

(ann ^:no-check clojure.core.async/close! [impl/Channel :-> nil])

(ann ^:no-check clojure.core.async.impl.dispatch/run [[:-> (ReadOnlyChan Any)] :-> Executor])
;(ann clojure.core.async.impl.ioc-macros/async-chan-wrapper kV

;;;;;;;;;;;;;;;;;;;;
;; Typed wrappers

(t/tc-ignore
(defn ^:skip-wiki maybe-annotation [args]
  (let [t? (#{:-} (first args))
        t (when t? (second args))
        args (if t? 
               (drop 2 args)
               args)]
    [t? t args]))
)

(defmacro go
  "Like go but with optional annotations. Channel annotation defaults to Any.
  
  eg.
    (let [c (chan :- Str)]
      ;; same as (go :- Any ...)
      (go (a/>! c \"hello\"))
      (assert (= \"hello\" (a/<!! (go :- Str (a/<! c)))))
      (a/close! c))"
  [& body]
  (let [[t? t body] (maybe-annotation body)]
    `(let [c# ((inst async/chan ~@(or (when t? [t t])
                                      [`t/Nothing `t/Any]))
               1)
           captured-bindings# (clojure.lang.Var/getThreadBindingFrame)]
       ~(when vs/*checking*
          ; wrap unexpanded go body in a thunk for type checking.
          ; Will result in the body expanding twice.
          `(t/fn [] 
             ~@body 
             nil))
       ; we don't want to touch this.
       (t/tc-ignore
         (dispatch/run
           (fn []
             (let [f# ~(ioc/state-machine `(do ~@body) 1 (keys &env) ioc/async-custom-terminators)
                   state# (-> (f#)
                              (ioc/aset-all! ioc/USER-START-IDX c#
                                             ioc/BINDINGS-IDX captured-bindings#))]
               (ioc/run-state-machine-wrapped state#)))))
       c#)))

(comment
(t/cf
  (let [c (chan )]
    (go (a/>! c "hello"))
    (prn (a/<!! (go :- t/Str (a/<! c))))
    (a/close! c)))

(t/cf
  (let [c1 (chan :- t/Str)
        c2 (chan :- t/Str)]
    (a/thread (while true
                (let [[v ch] (a/alts!! [c1 c2])]
                  (println "Read" v "from" ch))))
    (a/>!! c1 "hi")
    (a/>!! c2 "there")))

(t/cf
  (let [c1 (chan)
        c2 (chan :- t/Str)]
    (go (while true
          (let [[v ch] (a/alts! [c1 c2])]
            (println "Read" v "from" ch))))
    (go (a/>! c1 "hi"))
    (go (a/>! c2 "there"))))

)

(defmacro chan
  "Like chan but with optional type annotations. Channel annotation defaults to Any.

  (chan :- t ...) creates a buffer that can read and write type t.
  Subsequent arguments are passed directly to clojure.core.async/chan.

  (chan ...) is the same as (chan :- Any ....)
  
  Note: 
    (chan :- t ...) is the same as ((inst async/chan t) ...)"
  [& args]
  (let [[t? t args] (maybe-annotation args)
        a (or (when t? t) `t/Any)]
    `((inst async/chan ~a ~a) ~@args)))

(defmacro buffer
  "Like buffer but with optional type annotations. Buffer annotation defaults to Any.

  (buffer :- t ...) creates a buffer that can read and write type t.
  Subsequent arguments are passed directly to clojure.core.async/buffer.

  (buffer ...) is the same as (buffer :- Any ....)

  Note: (buffer :- t ...) is the same as ((inst buffer t) ...)"
  [& args]
  (let [[t? t args] (maybe-annotation args)
        a (or (when t? t) `t/Any)]
    `((inst async/buffer ~a ~a) ~@args)))

(defmacro sliding-buffer
  "Like sliding-buffer but with optional type annotations. Buffer annotation defaults to Any.

  (sliding-buffer :- t ...) creates a sliding buffer that can read and write type t.
  Subsequent arguments are passed directly to clojure.core.async/sliding-buffer.

  (sliding-buffer ...) is the same as (sliding-buffer :- Any ....)
  
  Note: (sliding-buffer :- t ...) is the same as ((inst sliding-buffer t t) ...)"
  [& args]
  (let [[t? t args] (maybe-annotation args)
        a (or (when t? t) `t/Any)]
    `((inst async/sliding-buffer ~a ~a) ~@args)))

(defmacro dropping-buffer
  "Like dropping-buffer but with optional type annotations. Buffer annotation defaults to Any.
  
  (dropping-buffer :- t ...) creates a dropping buffer that can read and write type t.
  Subsequent arguments are passed directly to clojure.core.async/dropping-buffer.

  (dropping-buffer ...) is the same as (dropping-buffer :- Any ....)
  
  Note: (dropping-buffer :- t ...) is the same as ((inst dropping-buffer t) ...)"
  [t & args]
  (let [[t? t args] (maybe-annotation args)
        a (or (when t? t) `t/Any)]
    `((inst async/dropping-buffer ~a ~a) ~@args)))
