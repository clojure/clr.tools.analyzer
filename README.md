# Interface to ClojureCLR's Analyzer

ClojureCLR's analysis compilation phase holds rich information about Clojure forms, like type/reflection information.

_analyze_ provides an interface to this phase, callable a la carte. The output is similar to ClojureScript's analyzer.

Supports ClojureCLR 1.4.1 or later.

# Contributing

Pull requests accepted from registered Clojure contributers

http://clojure.org/contributing

# Usage

## Generating AST from syntax

```clojure

clojure.clr.tools.analyzer=> (ast [1])
{:op :constant, :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}}, :val [1]}

clojure.clr.tools.analyzer=> (-> (ast (if true 1 2)) clojure.pprint/pprint)
{:op :if,
 :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
 :test
 {:op :boolean,
  :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
  :val true},
 :then
 {:op :number,
  :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
  :val 1},
 :else
 {:op :number,
  :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
  :val 2}}
nil

clojure.clr.tools.analyzer=> (-> (ast (fn [x] (+ x 1))) clojure.pprint/pprint)
{:op :meta,
 :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
 :meta
 {:op :map,
  :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
  :keyvals
  ({:op :keyword,
    :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
    :val :source-span}
   {:op :map,
    :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
    :keyvals
    ({:op :keyword,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val :start-line}
     {:op :number,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val 12}
     {:op :keyword,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val :start-column}
     {:op :number,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val 10}
     {:op :keyword,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val :end-line}
     {:op :number,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val 12}
     {:op :keyword,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val :end-column}
     {:op :number,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :val 25})})},
 :expr
 {:name clojure.clr.tools.analyzer$fn__3171,
  :op :fn-expr,
  :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
  :methods
  ({:op :fn-method,
    :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
    :body
    {:op :do,
     :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
     :exprs
     ({:op :static-method,
       :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
       :class clojure.lang.Numbers,
       :method
       {:name add,
        :return-type System.Object,
        :declaring-class clojure.lang.Numbers,
        :parameter-types [System.Object System.Int64],
        :flags #{:hide-by-sig :reuse-slot :static :public}},
       :args
       ({:op :host-arg,
         :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
         :expr
         {:op :local-binding-expr,
          :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
          :local-binding
          {:op :local-binding,
           :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
           :sym x,
           :tag nil,
           :init nil},
          :tag nil}}
        {:op :host-arg,
         :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
         :expr
         {:op :number,
          :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
          :val 1}}),
       :tag nil})},
    :required-params
    ({:op :local-binding,
      :env {:locals {}, :ns {:name clojure.clr.tools.analyzer}},
      :sym x,
      :tag nil,
      :init nil}),
    :rest-param nil}),
  :variadic-method nil,
  :tag nil}}
nil
```

## Syntax from AST


```clojure
clojure.jvm.tools.analyzer=> (require '[clojure.jvm.tools.analyzer.emit-form :as e])
nil
clojure.jvm.tools.analyzer=> (-> (ast 1) e/emit-form)
1
clojure.jvm.tools.analyzer=> (-> (ast [(+ 1 2)]) e/emit-form)
[(clojure.lang.Numbers/add 1 2)]
```

# Known Issues

## Evaluating forms

Currently the analyzer evaluates each form after it is analyzed.

## Incorrect handling of Var mappings within the same form

`analyze` is a thin wrapper over `clojure.lang.Compiler`, so to get our
hands on analysis results some compromises are made.

The following form normally evaluates to the Var `clojure.set/intersection`, but
analyses to `clojure.core/require`.


```clojure
;normal evaluation
(eval
 '(do 
    (require '[clojure.set])
    (refer 'clojure.set 
           :only '[intersection] 
           :rename '{intersection require})
    require))
;=> #'clojure.set/intersection

;analysis result
(-> (ast 
      (do (require '[clojure.set])
        (refer 'clojure.set 
               :only '[intersection] 
               :rename '{intersection require})
        require))
  :exprs last :var)
;=> #'clojure.core/require
```

# Todo

- analyze a leiningen `project.clj` file
- analyze `clojure.core`
- use :locals if necessary

# Examples

See `clojure.jvm.tools.analyzer.examples.*` namespaces.

# Contributors

- Jonas Enlund (jonase)
- Nicola Mometto (Bronsa)
- Chris Gray (chrismgray)
