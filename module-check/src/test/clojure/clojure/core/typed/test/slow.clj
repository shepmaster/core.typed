(ns clojure.core.typed.test.slow
  (:require
    [clojure.core.typed :refer [ann defalias loop>
                                NonEmptyVec NilableNonEmptySeq]
     :as t]))

(defalias VersionVector (NonEmptyVec Number))
(ann version-less [(t/U nil VersionVector) (t/U nil VersionVector) -> boolean])
(defn version-less
  "Compare two version vectors."
  [v1 v2]
  (loop> [v1 :- (NilableNonEmptySeq Number) (seq v1)
          v2 :- (NilableNonEmptySeq Number) (seq v2)]
         (let [fv1 (first v1)
               fv2 (first v2)]
           (cond
             (and (not v1) (not v2)) false
             (and v1 (not v2)) false
             (or (and (not v1) v2)
                 (and fv1 fv2 (< fv1 fv2))) true
             (and fv1 fv2 (> fv1 fv2)) false
             :else (recur (next v1) (next v2))))))

