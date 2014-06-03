(ns clojure.core.typed.check.nth
  (:require [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.object-rep :as obj]
            [clojure.core.typed.utils :as u]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.filter-ops :as fo]
            [clojure.core.typed.filter-rep :as fl]
            [clojure.core.typed.path-rep :as pe]
            [clojure.core.typed.object-rep :as obj]
            [clojure.core.typed.check.invoke :as invoke]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed :as t]
            [clojure.core.typed.check.utils :as cu])
  (:import (clojure.lang ISeq Seqable Indexed)))

(defn ^:private expr->type [expr]
  (if expr (-> expr u/expr-type r/ret-t)))

(defn ^:private expr->object [expr]
  (if expr (-> expr u/expr-type r/ret-o)))

(defn ^:private expression? [expr]
  (r/TCResult? (u/expr-type expr)))

(defn ^:private nth-type [types idx default-t]
  {:pre [(every? r/Type? types)
         (con/nat? idx)
         ((some-fn nil? r/Type?) default-t)]
   :post [(r/Type? %)]}
  (apply c/Un
         (doall
          (for [t types]
            (if-let [res-t (cond
                            (r/Nil? t) (or default-t r/-nil)
                            ;; nil on out-of-bounds and no default-t
                            :else (nth (:types t) idx default-t))]
              res-t
              (err/int-error (str "Cannot get index " idx
                                  " from type " (prs/unparse-type t))))))))

(defn ^:private nth-positive-filter-default-truthy [target-o default-o]
  {:pre [(obj/RObject? target-o)
         (obj/RObject? default-o)]
   :post [(fl/Filter? %)]}
  (fo/-and (fo/-filter-at (c/Un r/-nil (c/RClass-of ISeq [r/-any]))
                          target-o)
           (fo/-not-filter-at (c/Un r/-false r/-nil)
                              default-o)))

(defn ^:private nth-positive-filter-default-falsy [target-o default-o idx]
  {:pre [(obj/RObject? target-o)
         (obj/RObject? default-o)
         (con/nat? idx)]
   :post [(fl/Filter? %)]}
  (fo/-and (fo/-filter-at (c/In (c/RClass-of Seqable [r/-any])
                                (r/make-CountRange (inc idx)))
                          target-o)
           (fo/-filter-at (c/Un r/-false r/-nil)
                          default-o)))

(defn ^:private nth-positive-filter-default [target-o default-o idx]
  {:pre [(obj/RObject? target-o)
         (obj/RObject? default-o)
         (con/nat? idx)]
   :post [(fl/Filter? %)]}
  (fo/-or (nth-positive-filter-default-truthy target-o default-o)
          (nth-positive-filter-default-falsy target-o default-o idx)))

(defn ^:private nth-positive-filter-no-default [target-o idx]
  {:pre [(obj/RObject? target-o)
         (con/nat? idx)]
   :post [(fl/Filter? %)]}
  (fo/-filter-at (c/In (c/RClass-of Seqable [r/-any])
                       (r/make-CountRange (inc idx)))
                 target-o))

(defn ^:private nth-filter [target-expr default-expr idx default-t]
  {:pre [(expression? target-expr)
         ((some-fn nil? expression?) default-expr)
         (con/nat? idx)
         ((some-fn nil? r/Type?) default-t)]
   :post [(fl/Filter? %)]}
  (let [target-o (expr->object target-expr)
        default-o (expr->object default-expr)

        filter+ (if default-t
                  (nth-positive-filter-default target-o default-o idx)
                  (nth-positive-filter-no-default target-o idx))]
    (fo/-FS filter+
            ;; not sure if there's anything worth encoding here
            fl/-top)))

(defn ^:private nth-object [target-expr idx]
  {:pre [(expression? target-expr)
         (con/nat? idx)]
   :post [(obj/RObject? %)]}
  (let [target-o (expr->object target-expr)]
    (if (obj/Path? target-o)
      (update-in target-o [:path] concat [(pe/NthPE-maker idx)])
      target-o)))

(defn nth-type-for-idx
  "Same as the normal type for nth except for the case where
  we know we *always* ignore the default (eg. `(nth [1 2] 0 nil) ;=> Int`)
  and where we *only* use the default (eg. `(nth [1 2] 2 nil)` ;=> nil)"
  [idx]
  {:pre [(con/nat? idx)]}
  (let [x 'x
        d 'd
        s-or-i (c/Un (c/-name `t/SequentialSeqable (r/make-F x))
                     (c/RClass-of Indexed [(r/make-F x)]))]
    (c/Poly* [x d]
             [r/no-bounds r/no-bounds]
             (r/make-FnIntersection
              ;; [(U (Indexed x) (SequentialSeqable x)) Int -> x]
              (r/make-Function
               [s-or-i
                (c/-name `t/Int)]
               (r/make-F x))
              ;; [(U (I (CountRange idx++) (U (Seqable x) (Indexed x)))
              ;;     (HSequential [Any*idx x Any *]))
              ;;  Num Any -> x]
              (r/make-Function
               [(c/Un (c/In (r/make-CountRange (inc idx))
                            s-or-i)
                      (r/-hsequential (concat (repeat idx r/-any)
                                              [(r/make-F x)])
                                      :rest r/-any))
                (c/-name `t/Int)
                ;; default is never used
                r/-any]
               (r/make-F x))
              ;; [(U (I (CountRange 0 idx) (U (Seqable x) (Indexed x)))
              ;;      nil)
              ;;  Num d -> d]
              (r/make-Function
               [(c/Un (c/In (r/make-CountRange 0 idx)
                            s-or-i)
                      r/-nil)
                (c/-name `t/Int)
                ;; default is *only* used
                (r/make-F d)]
               (r/make-F d))
              ;; [(U (Indexed x) (SequentialSeqable x) nil) Int d -> (U x d)]
              (r/make-Function
               [(c/Un s-or-i r/-nil)
                (c/-name `t/Int)
                (r/make-F d)]
               (c/Un (r/make-F x)
                     (r/make-F d)))
              ;; [(U (Indexed x) (SequentialSeqable x) nil) Int -> (U x nil)]
              (r/make-Function
               [(c/Un s-or-i r/-nil)
                (c/-name `t/Int)]
               (r/make-F x))))))

(defn invoke-nth [check-fn {:keys [args] :as expr} expected & {:keys [cargs]}]
  {:pre [((some-fn nil? vector?) cargs)]}
  (let [_ (assert (#{2 3} (count args)) (str "nth takes 2 or 3 arguments, actual " (count args)))
        [te ne de :as cargs] (or cargs (mapv check-fn args))
        types (let [ts (c/fully-resolve-type (expr->type te))]
                (if (r/Union? ts)
                  (map c/fully-resolve-type (:types ts))
                  [ts]))
        num-t (expr->type ne)
        default-t (expr->type de)
        idx (if (r/Value? num-t)
              (let [n (:val num-t)]
                (if (con/nat? n)
                  n)))]
    (cond
     (and idx
          (every? (some-fn r/Nil?
                           r/HeterogeneousVector?
                           r/HeterogeneousList?
                           r/HeterogeneousSeq?)
                  types))
     (assoc expr
       :args cargs
       u/expr-type (r/ret (nth-type types idx default-t)
                          (nth-filter te de idx default-t)
                          (nth-object te idx)))

     idx
     (binding [vs/*current-expr* expr]
       (invoke/normal-invoke check-fn
                             expr (:fn expr) args
                             expected
                             :cfexpr (assoc (:fn expr)
                                       u/expr-type (r/ret (nth-type-for-idx idx)))
                             :cargs cargs))

     :else
     cu/not-special)))
