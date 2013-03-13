(ns clojure.clr.tools.analyzer.examples.nsforms
  (:require [clojure.clr.tools.analyzer :as analyze]))

(defn warn-on-naked-use [use-expr]
  (doseq [s (map :val (:args use-expr))
          :when (symbol? s)]
    (println "Warning: Naked use of" (name s) "in" (-> use-expr :env :ns :name))))

(defn use? [expr]
  (and (= :invoke (:op expr))
       (= :var (-> expr :fexpr :op))
       (= 'use (-> expr :fexpr :var meta :name))))

(defn find-and-analyze-use-forms [expr]
  (when (use? expr)
    (warn-on-naked-use expr))
  (doseq [child-expr (:children expr)]
    (find-and-analyze-use-forms child-expr)))

(comment

  (reset! analyze/CHILDREN true)

  (find-and-analyze-use-forms
    (analyze/ast
      (ns sjfis (:use [clojure.set :only [union]]
                      clojure.repl))))


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
    (find-and-analyze-use-forms exp))
  )
