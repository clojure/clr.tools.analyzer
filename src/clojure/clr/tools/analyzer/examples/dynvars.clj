(ns clojure.clr.tools.analyzer.examples.dynvars
  (:require [clojure.clr.tools.analyzer :as analyze]))

(defn earmuffed? [sym]
  (let [s (name sym)]
    (and (< 2 (count s))
         (.startsWith s "*")
         (.endsWith s "*"))))

(defn check-def [expr]
  (let [v (:var expr)
        s (.sym v)]
    (when (and (earmuffed? s)
               (not (:is-dynamic expr)))
      (println "WARNING: Should" v "be marked dynamic?"))))

(defn find-and-check-defs [expr]
  (when (= :def (:op expr))
    (check-def expr))
  (doseq [child-expr (:children expr)]
    (find-and-check-defs child-expr)))

(comment

(do
  (reset! analyze/CHILDREN true)

  (find-and-check-defs
    (analyze/analyze-one {:ns {:name 'user} :context :eval}
                         '(def *a* 1))))

(def analyzed
  (doall (map analyze/analyze-ns
              '[clojure.test
                clojure.set
                clojure.java.io
                clojure.stacktrace
                clojure.pprint
                clojure.walk
                clojure.string
                clojure.repl
                clojure.core.protocols
                clojure.template])))

(doseq [exprs analyzed
        exp exprs]
  (find-and-check-defs exp))
  )
