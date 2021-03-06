(ns clojure.core.typed.errors
  {:skip-wiki true
   :core.typed {:collect-only true}}
  (:require [clojure.core.typed.util-vars :refer [*current-env*] :as uvs]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.ast-utils :as ast-u]))

(alter-meta! *ns* assoc :skip-wiki true)

(def int-error-kw ::internal-error)
(def nyi-error-kw ::nyi-error)

(def tc-error-parent ::tc-error-parent)

(defn derive-error [kw]
  (derive kw tc-error-parent))

(derive-error int-error-kw)
(derive-error nyi-error-kw)

;(t/ann ^:no-check env-for-error [Any -> Any])
(defn env-for-error [env]
  ; impl-case probably can't be done here
  (merge (select-keys env [:line :column])
         ;clojure specific
         (let [f (:file env)]
           (when (string? f)
             {:file f}))
         ;cljs specific
         ;FIXME filename?
         (let [n (get-in env [:ns :name])]
           (when (symbol? n)
             {:ns n}))))

(defn int-error
  ([estr] (int-error estr {}))
  ([estr {:keys [use-current-env] :as opt}]
   (let [{:keys [line column file] :as env} *current-env*]
     (throw (ex-info (str "Internal Error "
                          "(" (or file (:ns env)) ":" 
                          (or line "<NO LINE>")
                          (when column
                            (str ":" column))
                          ") "
                          estr)
                     {:type-error int-error-kw
                      :env (or (when (and uvs/*current-expr*
                                          (not use-current-env))
                                 (:env uvs/*current-expr*))
                               (env-for-error *current-env*))})))))

;[Any * -> String]
(defn ^String error-msg 
  [& msg]
  (apply str (when *current-env*
               (str (:line *current-env*) ":"
                    (:col *current-env*)
                    " "))
         (concat msg)))

;errors from check-ns or cf
(defn top-level-error? [{:keys [type-error] :as exdata}]
  (boolean (#{:top-level-error} type-error)))

(defmacro top-level-error-thrown? [& body]
  `(with-ex-info-handlers
     [top-level-error? (constantly true)]
     ~@body
     false))

(defmacro tc-error-thrown? [& body]
  `(with-ex-info-handlers
     [tc-error? (constantly true)]
     ~@body
     false))

(defn tc-error? [exdata]
  (assert (not (instance? clojure.lang.ExceptionInfo exdata)))
  (isa? (:type-error exdata) tc-error-parent))

(defn tc-delayed-error [msg & {:keys [return form] :as opt}]
  (let [e (ex-info msg (merge {:type-error tc-error-parent}
                              (when (or (contains? opt :form)
                                        uvs/*current-expr*)
                                {:form (if (contains? opt :form)
                                         form
                                         (ast-u/emit-form-fn uvs/*current-expr*))})
                              {:env (env-for-error
                                      (or (when uvs/*current-expr*
                                            (:env uvs/*current-expr*))
                                          *current-env*))}))]
    (cond
      ;can't delay here
      (not uvs/*delayed-errors*)
      (throw e)

      :else
      (do
        (if-let [delayed-errors uvs/*delayed-errors*]
          (swap! delayed-errors conj e)
          (throw (Exception. (str "*delayed-errors* not rebound"))))
        (or return (impl/v 'clojure.core.typed.type-rep/-nothing))))))

(defn tc-error
  [estr]
  (let [env *current-env*]
    (throw (ex-info (str "Type Error "
                         "(" (:file env) ":" (or (:line env) "<NO LINE>")
                         (when-let [col (:column env)]
                           (str ":" col))
                         ") "
                         estr)
                    (merge
                      {:type-error tc-error-parent}
                      {:env (env-for-error env)})))))

(defn deprecated-warn
  [msg]
  (let [env *current-env*
        file (:file env)]
    (println 
      (str
        "DEPRECATED SYNTAX "
        "(" 
        (cond
          (and file
               (not= "NO_SOURCE_PATH" file))
          (str (:file env)
               (when-let [line (:line env)]
                 (str ":" (:line env)
                      (when-let [col (:column env)]
                        (str ":" col)))))
          :else "NO_SOURCE_PATH")
        "): "
        msg))
    (flush)))

(defn nyi-error
  [estr]
  (let [env *current-env*]
    (throw (ex-info (str "core.typed Not Yet Implemented Error:"
                           "(" (:file env) ":" (or (:line env) "<NO LINE>")
                           (when-let [col (:column env)]
                             (str ":"col))
                           ") "
                           estr)
                    (merge {:type-error nyi-error-kw}
                           {:env (env-for-error env)})))))

(defmacro with-ex-info-handlers 
  "Handle an ExceptionInfo e thrown in body. The first handler whos left hand
  side returns true, then the right hand side is called passing (ex-info e) and e."
  [handlers & body]
  `(try
     ~@body
     (catch clojure.lang.ExceptionInfo e#
       (let [found?# (atom false)
             result# (reduce (fn [_# [h?# hfn#]]
                               (when (h?# (ex-data e#))
                                 (reset! found?# true)
                                 (reduced (hfn# (ex-data e#) e#))))
                             nil
                             ~(mapv vec (partition 2 handlers)))]
         (if @found?#
           result#
           (throw e#))))))

(defn var-for-impl [sym]
  {:pre [((some-fn string? symbol?) sym)]
   :post [(symbol? %)]}
  (symbol
    (impl/impl-case
      :clojure "clojure.core.typed"
      :cljs "cljs.core.typed")
    (str sym)))

(defn deprecated-plain-op [old & [new]]
  {:pre [(symbol? old)
         ((some-fn symbol? nil?) new)]}
  (deprecated-warn (str old " syntax is deprecated, use " (var-for-impl (or new old)))))

(defn
  print-errors! 
  "Internal use only"
  [errors]
  {:pre [(seq errors)
         (every? #(instance? clojure.lang.ExceptionInfo %) errors)]}
  (binding [*out* *err*]
    (doseq [^Exception e errors]
      (let [{{:keys [file line column] :as env} :env :as data} (ex-data e)]
        (print "Type Error ")
        (print (str "(" (or file 
                            (let [nsym (-> env :ns)]
                              (when (symbol? nsym)
                                nsym))
                            "NO_SOURCE_FILE")
                    (when line
                      (str ":" line
                           (when column
                             (str ":" column))))
                    ") "))
        (print (.getMessage e))
        (println)
        (flush)
        (let [[_ form :as has-form?] (find data :form)]
          (when has-form?
            (print "in: ")
            (binding [*print-length* (when-not uvs/*verbose-forms*
                                       6)
                      *print-level* (when-not uvs/*verbose-forms*
                                      4)]
              (println form))
            (println)
            (println)
            (flush)))
        (flush))))
  (throw (ex-info (str "Type Checker: Found " (count errors) " error" (when (< 1 (count errors)) "s"))
                  {:type-error :top-level-error
                   :errors errors})))

(defn ^:skip-wiki
  -init-delayed-errors 
  "Internal use only"
  []
  (atom [] :validator #(and (vector? %)
                            (every? (fn [a] 
                                      (instance? clojure.lang.ExceptionInfo a))
                                    %))))
