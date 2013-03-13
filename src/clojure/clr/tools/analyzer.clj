(set! *warn-on-reflection* true)

(ns clojure.clr.tools.analyzer
  "Interface to Compiler's analyze.
  Entry point `analyze-path` and `analyze-one`"
  (:require [clojure.reflect :as reflect]
            [clojure.clr.io :as io]
            [clojure.repl :as repl]
            [clojure.string :as string]
            [clojure.set :as set]
            [clojure.clr.tools.analyzer.util])
  (:import (System.IO TextReader)
           (System.Reflection BindingFlags)
           (clojure.lang RT Compiler LineNumberingTextReader)
           (clojure.lang.CljCompiler.Ast
             DefExpr LocalBinding BindingInit LetExpr
             LetFnExpr MethodExpr StaticMethodExpr InstanceMethodExpr StaticFieldExpr
             NewExpr EmptyExpr VectorExpr MonitorEnterExpr
             MonitorExitExpr ThrowExpr InvokeExpr TheVarExpr VarExpr
             UnresolvedVarExpr ObjExpr NewInstanceMethod FnMethod FnExpr
             NewInstanceExpr MetaExpr BodyExpr ImportExpr AssignExpr
             TryExpr+CatchClause TryExpr LocalBindingExpr RecurExpr
             MapExpr IfExpr KeywordInvokeExpr InstanceFieldExpr InstanceOfExpr
             CaseExpr Expr SetExpr MethodParamExpr KeywordExpr
             ConstantExpr NumberExpr NilExpr BooleanExpr StringExpr
             ObjMethod ParserContext RHC HostArg)
           (clojure.reflect Field)))

(def CHILDREN (atom false))
(def JAVA-OBJ (atom false))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Interface

(declare analyze-one)

(defn analyze-form-in-ns [nsym form]
  (analyze-one {:ns {:name nsym} :context :eval}
               form))

(defn analyze-form [form]
  (analyze-form-in-ns (ns-name *ns*) form))

(defmacro ast-in-ns
  "Returns the abstract syntax tree representation of the given form,
  evaluated in the given namespace"
  [nsym form]
  `(analyze-form-in-ns '~nsym '~form))

(defmacro ast 
  "Returns the abstract syntax tree representation of the given form,
  evaluated in the current namespace"
  [form]
  `(analyze-form '~form))

;;;;;;;;;;;;;;;;;;;;;;;
;; Utils

(defmacro field 
  "Call a private field, must be known at compile time. Throws an error
  if field is already publicly accessible."
  ([class-obj field] `(field ~class-obj ~field nil))
  ([class-obj field obj]
   (assert (symbol? class-obj))
   (assert (resolve class-obj) (str "Class " class-obj " cannot be resolved"))
   (let [{class-flags :flags :keys [members]} (reflect/reflect (resolve class-obj))
         field-flags (when-let [^Field f (some #(and (when (instance? Field %) (= (.name ^Field %) field)) %) members)]
                       ;FIXME it doesn't seem like ClojureCLR lets me use :flags here. Needs investigation.
                       (.flags f))]
     (assert field-flags
             (str "Class " (resolve class-obj) " does not have field " field))
     (assert (not (and (:public class-flags)
                       (:public field-flags)))
             (str "Class " (resolve class-obj) " and field " field " is already public")))
   `(field-accessor ~class-obj '~field ~obj)))

(def reflect-flag->BindingFlags
  {:private BindingFlags/NonPublic
   :public BindingFlags/Public
   :static BindingFlags/Static})

(defn- field-accessor [^Type class-obj field-sym obj]
  (let [^Field
        clj-field (->> (reflect/reflect class-obj)
                    :members
                    (filter #(when (instance? Field %) (= (.name ^Field %) field-sym)))
                    first)
        _ (assert clj-field)
        reflect-flags (.flags clj-field)
        binding-flags (set/union (set (->> reflect-flags
                                        (map reflect-flag->BindingFlags)
                                        (remove nil?)))
                                 #{BindingFlags/NonPublic BindingFlags/Public})
        binding-flags (if (:static reflect-flags)
                        binding-flags
                        (conj binding-flags BindingFlags/Instance))

        bfs-bit-or (apply enum-or binding-flags)

        ^System.Reflection.FieldInfo 
        field (.GetField class-obj (name field-sym) bfs-bit-or)]
    (if field
      (.GetValue field obj)
      (throw (Exception. (str "Class " class-obj " does not contain field " field-sym))))))

#_(defn- method-accessor [^Class class-obj method obj types & args]
  (let [^java.lang.reflect.Method 
        method (.getDeclaredMethod class-obj (name method) (into-array Class types))]
    (.setAccessible method true)
    (.invoke method obj (object-array args))))

(defn- when-column-map [expr]
  (let [field (try (field-accessor (class expr) '_column expr)
                (catch Exception e))]
    (when field
      {:column (field-accessor (class expr) '_column expr)})))

(defn- when-line-map [expr]
  (let [field (try (field-accessor (class expr) '_line expr)
                (catch Exception e))]
    (when field
      {:line (field-accessor (class expr) '_line expr)})))

(defn- when-source-map [expr]
  (let [field (try (field-accessor (class expr) '_source expr)
                (catch Exception e))]
    (when field
      {:source (field-accessor (class expr) '_source expr)})))

(defn- env-location [env expr]
  (merge env
         (when-line-map expr)
         (when-column-map expr)
         (when-source-map expr)))

(defn- inherit-env [expr env]
  (merge env
         (when-let [line (-> expr :env :line)]
           {:line line})
         (when-let [column (-> expr :env :column)]
           {:column column})
         (when-let [source (-> expr :env :source)]
           {:source source})))

(defprotocol AnalysisToMap
  (analysis->map [aobj env]
    "Recursively converts the output of the Compiler's analysis to a map"))

;; Literals extending abstract class LiteralExpr and have public value fields

(defmacro literal-dispatch [disp-class op-keyword]
  `(extend-protocol AnalysisToMap
     ~disp-class
     (~'analysis->map
       [expr# env#]
       (let []
         (merge
           {:op ~op-keyword
            :env env#
            :val (.Eval expr#)}
           (when @JAVA-OBJ
             {:Expr-obj expr#}))))))

(literal-dispatch KeywordExpr :keyword)
(literal-dispatch ConstantExpr :constant)
(literal-dispatch NumberExpr :number)
(literal-dispatch StringExpr :string)
(literal-dispatch NilExpr :nil)
(literal-dispatch BooleanExpr :boolean)

(extend-protocol AnalysisToMap

  ;; def
  DefExpr
  (analysis->map
    [expr env]
    (let [init (analysis->map (field DefExpr _init expr) env)
          meta (when-let [meta (field DefExpr _meta expr)]
                 (analysis->map meta env))]
      (merge 
        {:op :def
         :env (env-location env expr)
         :var (field DefExpr _var expr)
         :meta meta
         :init init
         :init-provided (field DefExpr _initProvided expr)
         :is-dynamic (field DefExpr _isDynamic expr)}
        (when @CHILDREN
          {:children [meta init]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; let
  LocalBinding
  (analysis->map
    [lb env]
    (let [init (when-let [init (.Init lb)]
                 (analysis->map init env))]
      (merge
        {:op :local-binding
         :env (inherit-env init env)
         :sym (.Symbol lb)
         :tag (.Tag lb)
         :init init}
        (when @CHILDREN
          {:children (when init [init])})
        (when @JAVA-OBJ
          {:LocalBinding-obj lb}))))

  BindingInit
  (analysis->map
    [bi env]
    (let [local-binding (analysis->map (.Binding bi) env)
          init (analysis->map (.Init bi) env)]
      (merge
        {:op :binding-init
         :env (inherit-env init env)
         :local-binding local-binding
         :init init}
        (when @CHILDREN
          {:children [local-binding init]})
        (when @JAVA-OBJ
          {:BindingInit-obj bi}))))

  LetExpr
  (analysis->map
    [expr env]
    (let [body (analysis->map (field LetExpr _body expr) env)
          binding-inits (map analysis->map (field LetExpr _bindingInits expr) (repeat env))]
      (merge
        {:op :let
         :env (inherit-env body env)
         :binding-inits binding-inits
         :body body
         :is-loop (field LetExpr _isLoop expr)}
        (when @CHILDREN
          {:children (conj (vec binding-inits) body)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; letfn
  LetFnExpr
  (analysis->map
    [expr env]
    (let [body (analysis->map (field LetFnExpr _body expr) env)
          binding-inits (map analysis->map (field LetFnExpr _bindingInits expr) (repeat env))]
      (merge
        {:op :letfn
         :env (inherit-env body env)
         :body body
         :binding-inits binding-inits}
        (when @CHILDREN
          {:children (conj (vec binding-inits) body)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; LocalBindingExpr
  LocalBindingExpr
  (analysis->map
    [expr env]
    (let [local-binding (analysis->map (field LocalBindingExpr _b expr) env)]
      (merge
        {:op :local-binding-expr
         :env (inherit-env local-binding env)
         :local-binding local-binding
         :tag (field LocalBindingExpr _tag expr)}
        (when @CHILDREN
          {:children [local-binding]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; Methods
  StaticMethodExpr
  (analysis->map
    [expr env]
    (let [args (map analysis->map (field MethodExpr _args expr) (repeat env))]
      (merge
        {:op :static-method
         :env (env-location env expr)
         :class (field StaticMethodExpr _type expr)
         ;:method-name (field StaticMethodExpr methodName expr)
         :method (when-let [method (field MethodExpr _method expr)]
                   (@#'reflect/method->map method))
         :args args
         :tag (field MethodExpr _tag expr)}
        (when @CHILDREN
          {:children args})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  InstanceMethodExpr
  (analysis->map
    [expr env]
    (let [target (analysis->map (field InstanceMethodExpr _target expr) env)
          args (map analysis->map (field MethodExpr _args expr) (repeat env))]
      (merge
        {:op :instance-method
         :env (env-location env expr)
         :target target
         :method-name (field MethodExpr _methodName expr)
         :method (when-let [method (field MethodExpr _method expr)]
                   (@#'reflect/method->map method))
         :args args
         :tag (field MethodExpr _tag expr)}
        (when @CHILDREN
          {:children (cons target args)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; Fields
  StaticFieldExpr
  (analysis->map
    [expr env]
    (let []
      (merge
        {:op :static-field
         :env (env-location env expr)
         ;:class (field clojure.lang.CljCompiler.Ast.StaticFieldOrPropertyExpr _type expr)
         ;:field-name (field StaticFieldExpr _fieldName expr)
         ;:field (when-let [field (field StaticFieldExpr _tinfo expr)]
         ;         (@#'reflect/field->map field))
         ;:tag (field StaticFieldExpr tag expr)
         }
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  InstanceFieldExpr
  (analysis->map
    [expr env]
    (let [#_target #_(analysis->map (field InstanceFieldOrPropertyExpr _target expr) env)]
      (merge
        {:op :instance-field
         :env (env-location env expr)
;         :target target
;         :target-class (field InstanceFieldExpr _targetType expr)
;         :field (when-let [field (field InstanceFieldExpr field expr)]
;                  (@#'reflect/field->map field))
;         :field-name (field InstanceFieldExpr fieldName expr)
;         :tag (field InstanceFieldExpr tag expr)
         }
        (when @CHILDREN
          {:children [#_target]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  NewExpr
  (analysis->map
    [expr env]
    (let [args (map analysis->map (field NewExpr _args expr) (repeat env))]
      (merge
        {:op :new
         :env env 
              ; should be there but isn't
              ;(assoc env
        ;             :line (.line expr)
        ;             )
         :ctor (when-let [ctor (field NewExpr _ctor expr)]
                 (@#'reflect/constructor->map ctor))
         :class (.ClrType expr)
         :args args}
        (when @CHILDREN
          {:children args})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  EmptyExpr
  (analysis->map
    [expr env]
    (merge
      {:op :empty-expr
       :env env
       :coll (field EmptyExpr _coll expr)}
      (when @JAVA-OBJ
        {:Expr-obj expr})))

  ;; set literal
  SetExpr
  (analysis->map
    [expr env]
    (let [keys (map analysis->map (field SetExpr _keys expr) (repeat env))]
      (merge
        {:op :set
         :env env
         :keys keys}
        (when @CHILDREN
          {:children keys})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; vector literal
  VectorExpr
  (analysis->map
    [expr env]
    (let [args (map analysis->map (field VectorExpr _args expr) (repeat env))]
      (merge
        {:op :vector
         :env env
         :args args}
        (when @CHILDREN
          {:children args})
        (when @JAVA-OBJ 
          {:Expr-obj expr}))))

  ;; map literal
  MapExpr
  (analysis->map
    [expr env]
    (let [keyvals (map analysis->map (.KeyVals expr) (repeat env))]
      (merge
        {:op :map
         :env env
         :keyvals keyvals}
        (when @CHILDREN
          {:children keyvals})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; Untyped
  MonitorEnterExpr
  (analysis->map
    [expr env]
    (let [target (analysis->map (field MonitorEnterExpr _target expr) env)]
      (merge
        {:op :monitor-enter
         :env env
         :target target}
        (when @CHILDREN
          {:children [target]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  MonitorExitExpr
  (analysis->map
    [expr env]
    (let [target (analysis->map (field MonitorExitExpr _target expr) env)]
      (merge
        {:op :monitor-exit
         :env env
         :target target}
        (when @CHILDREN
          {:children [target]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ThrowExpr
  (analysis->map
    [expr env]
    (let [exception (analysis->map (field ThrowExpr _excExpr expr) env)]
      (merge
        {:op :throw
         :env env
         :exception exception}
        (when @CHILDREN
          {:children [exception]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; Invokes
  InvokeExpr
  (analysis->map
    [expr env]
    (let [fexpr (analysis->map (field InvokeExpr _fexpr expr) env)
          args (map analysis->map (field InvokeExpr _args expr) (repeat env))]
      (merge
        {:op :invoke
         :env (env-location env expr)
         :fexpr fexpr
         :tag (field InvokeExpr _tag expr)
         :args args
         :is-protocol (field InvokeExpr _isProtocol expr)
         ;:is-direct (field InvokeExpr isDirect expr)
         :site-index (field InvokeExpr _siteIndex expr)
         :protocol-on (field InvokeExpr _protocolOn expr)}
        (when-let [m (field InvokeExpr _onMethod expr)]
          {:method (@#'reflect/method->map m)})
        (when @CHILDREN
          {:children (cons fexpr args)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  KeywordInvokeExpr
  (analysis->map
    [expr env]
    (let [target (analysis->map (field KeywordInvokeExpr _target expr) env)
          kw (analysis->map (field KeywordInvokeExpr _kw expr) env)]
      (merge
        {:op :keyword-invoke
         :env (env-location env expr)
         :kw kw
         :tag (field KeywordInvokeExpr _tag expr)
         :target target}
        (when @CHILDREN
          {:children [target]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; TheVarExpr
  TheVarExpr
  (analysis->map
    [expr env]
    (merge
      {:op :the-var
       :env env
       :var (field TheVarExpr _var expr)}
      (when @JAVA-OBJ
        {:Expr-obj expr})))

  ;; VarExpr
  VarExpr
  (analysis->map
    [expr env]
    (merge
      {:op :var
       :env env
       :var (.Var expr)
       :tag (.Tag expr)}
      (when @JAVA-OBJ
        {:Expr-obj expr})))

  ;; UnresolvedVarExpr
  UnresolvedVarExpr
  (analysis->map
    [expr env]
    (let []
      (merge
        {:op :unresolved-var
         :env env
         :sym (field UnresolvedVarExpr _symbol expr)}
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; ObjExprs
  ObjExpr
  (analysis->map
    [expr env]
    (merge
      {:op :obj-expr
       :env env
       :tag (field ObjExpr _tag expr)}
      (when @JAVA-OBJ
        {:Expr-obj expr})))

  ;; FnExpr (extends ObjExpr)
  NewInstanceMethod
  (analysis->map
    [obm env]
    (let [body (analysis->map (field ObjMethod _body obm) env)]
      (merge
        {:op :new-instance-method
         :env (env-location env obm)
         :name (symbol (field NewInstanceMethod _name obm))
;         :required-params (map analysis->map 
;                               (concat [((field ObjMethod indexlocals obm) 0)]
;                                       (field ObjMethod argLocals obm))
;                               (repeat env))
         :body body}
        (when @CHILDREN
          {:children [body]})
        (when @JAVA-OBJ
          {:ObjMethod-obj obm}))))

  FnMethod
  (analysis->map
    [obm env]
    (let [body (analysis->map (field ObjMethod _body obm) env)
          required-params (map analysis->map (field FnMethod _reqParms obm) (repeat env))]
      (merge
        {:op :fn-method
         :env env
         :body body
         ;; Map LocalExpr@xx -> LocalExpr@xx
         ;;:locals (map analysis->map (keys (.locals obm)) (repeat env))
         :required-params required-params
         :rest-param (let [rest-param (field FnMethod _restParm obm)]
                       (if rest-param
                         (analysis->map rest-param env)
                         rest-param))}
        (when @CHILDREN
          {:children [body]})
        (when @JAVA-OBJ
          {:ObjMethod-obj obm}))))

  FnExpr
  (analysis->map
    [expr env]
    (let [methods (map analysis->map (field ObjExpr _methods expr) (repeat env))]
      (merge
        {:op :fn-expr
         :env (env-location env expr)
         :methods methods
         :variadic-method (when-let [variadic-method (field FnExpr _variadicMethod expr)]
                            (analysis->map variadic-method env))
         :tag (field ObjExpr _tag expr)}
        (when-let [nme (.Name expr)]
          {:name (symbol nme)})
        (when @CHILDREN
          {:children methods})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; NewInstanceExpr
;FIXME find vector of interfaces this implements (I think it's in mmap + IType)
  NewInstanceExpr
  (analysis->map
    [expr env]
    (let [methods (map analysis->map (field ObjExpr _methods expr) (repeat env))]
      (merge
        {:op :deftype*
         :name (symbol (.Name expr))
         :env (env-location env expr)
         :methods methods
         ;:mmap (field NewInstanceExpr mmap expr)

         ;:compiled-class (.compiledClass expr)
         ;:internal-name (.internalName expr)
         ;:this-name (.thisName expr)

         ;(IPersistentSet LocalBinding)
         ;:fields (set (for [[k v] (field ObjExpr fields expr)]
         ;               (analysis->map v env)))
         
         ;:covariants (field NewInstanceExpr covariants expr)

         :tag (field ObjExpr _tag expr)}
        (when @CHILDREN
          {:children methods})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; InstanceOfExpr
  InstanceOfExpr
  (analysis->map
    [expr env]
    (let [exp (analysis->map (field InstanceOfExpr _expr expr) env)]
      (merge
        {:op :instance-of
         :env env
         :class (field InstanceOfExpr _t expr)
         :the-expr exp}
        (when @CHILDREN
          {:children [exp]})
        (when @JAVA-OBJ 
          {:Expr-obj expr}))))

  ;; MetaExpr
  MetaExpr
  (analysis->map
    [expr env]
    (let [meta (analysis->map (field MetaExpr _meta expr) env)
          the-expr (analysis->map (field MetaExpr _expr expr) env)]
      (merge
        {:op :meta
         :env env
         :meta meta
         :expr the-expr}
        (when @CHILDREN
          {:children [meta the-expr]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; do
  BodyExpr
  (analysis->map
    [expr env]
    (let [exprs (map analysis->map (field BodyExpr _exprs expr) (repeat env))]
      (merge
        {:op :do
         :env (inherit-env (last exprs) env)
         :exprs exprs}
        (when @CHILDREN
          {:children exprs})
        (when @JAVA-OBJ 
          {:Expr-obj expr}))))

  ;; if
  IfExpr
  (analysis->map
    [expr env]
    (let [test (analysis->map (field IfExpr _testExpr expr) env)
          then (analysis->map (field IfExpr _thenExpr expr) env)
          else (analysis->map (field IfExpr _elseExpr expr) env)]
      (merge
        {:op :if
         :env (env-location env expr)
         :test test
         :then then
         :else else}
        (when @CHILDREN
          {:children [test then else]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; case
  ;; (from Compiler.java)
  ;;  //(case* expr shift mask default map<minhash, [test then]> table-type test-type skip-check?)
  CaseExpr
  (analysis->map
    [expr env]
    (let [the-expr (analysis->map (field CaseExpr _expr expr) env)
          tests (map analysis->map (vals (field CaseExpr _tests expr)) (repeat env))
          thens (map analysis->map (vals (field CaseExpr _thens expr)) (repeat env))
          default (analysis->map (field CaseExpr _defaultExpr expr) env)]
      (merge
        {:op :case*
         :env (env-location env expr)
         :the-expr the-expr
         :tests tests
         :thens thens
         :default default
         :tests-hashes (keys (field CaseExpr _tests expr))
         :shift (field CaseExpr _shift expr)
         :mask (field CaseExpr _mask expr)
         :test-type (field CaseExpr _testType expr)
         :switch-type (field CaseExpr _switchType expr)
         :skip-check (field CaseExpr _skipCheck expr)}
        (when @CHILDREN
          {:children (concat [the-expr] tests thens [default])})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))


  ;; ImportExpr
  ImportExpr
  (analysis->map
    [expr env]
    (merge
      {:op :import*
       :env env
       :class-str (field ImportExpr _c expr)}
       (when @JAVA-OBJ
         {:Expr-obj expr})))

  ;; AssignExpr (set!)
  AssignExpr
  (analysis->map
    [expr env]
    (let [target (analysis->map (field AssignExpr _target expr) env)
          val (analysis->map (field AssignExpr _val expr) env)]
      (merge
        {:op :set!
         :env env
         :target target
         :val val}
        (when @CHILDREN
          {:children [target val]})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;;TryExpr
  TryExpr+CatchClause
  (analysis->map
    [ctch env]
    (let [local-binding (analysis->map (field TryExpr+CatchClause _lb ctch) env)
          handler (analysis->map (field TryExpr+CatchClause _handler ctch) env)]
      (merge
        {:op :catch
         :env env
         :class (.Type ctch)
         :local-binding local-binding
         :handler handler}
        (when @CHILDREN
          {:children [local-binding handler]})
        (when @JAVA-OBJ
          {:CatchClause-obj ctch}))))

  TryExpr
  (analysis->map
    [expr env]
    (let [try-expr (analysis->map (field TryExpr _tryExpr expr) env)
          finally-expr (when-let [finally-expr (field TryExpr _finallyExpr expr)]
                         (analysis->map finally-expr env))
          catch-exprs (map analysis->map (field TryExpr _catchExprs expr) (repeat env))]
      (merge
        {:op :try
         :env env
         :try-expr try-expr
         :finally-expr finally-expr
         :catch-exprs catch-exprs
         ;:ret-local (.retLocal expr)
         ;:finally-local (.finallyLocal expr)
         }
        (when @CHILDREN
          {:children (concat [try-expr] (when finally-expr [finally-expr]) catch-exprs)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  ;; RecurExpr
  RecurExpr
  (analysis->map
    [expr env]
    (let [loop-locals (map analysis->map (field RecurExpr _loopLocals expr) (repeat env))
          args (map analysis->map (field RecurExpr _args expr) (repeat env))]
      (merge
        {:op :recur
         :env (env-location env expr)
         :loop-locals loop-locals
         :args args}
        (when @CHILDREN
          {:children (concat loop-locals args)})
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  MethodParamExpr
  (analysis->map
    [expr env]
    (let []
      (merge
        {:op :method-param
         :env env
         :class (.ClrType expr)
         :can-emit-primitive (.CanEmitPrimitive expr)}
        (when @JAVA-OBJ
          {:Expr-obj expr}))))

  HostArg
  (analysis->map
    [expr env]
    (let []
      (merge
        {:op :host-arg
         :env env
         :expr (analysis->map (.ArgExpr expr) env)}
        (when @JAVA-OBJ
          {:Expr-obj expr})))))

(defn- analyze*
  "Must be called after binding the appropriate Compiler and RT dynamic Vars."
  [env form]
  (letfn [(invoke-analyze [context form]
            (Compiler/Analyze context form))]
    (let [context (->
                    (case (:context env)
                      :statement RHC/Statement
                      :expression RHC/Expression
                      :return RHC/Return
                      :eval RHC/Eval)
                    ParserContext.)
          expr-ast (try
                     (invoke-analyze context form)
                     (catch Exception e
                       (throw (repl/root-cause e))))]
      (analysis->map expr-ast (merge-with conj (dissoc env :context) {:locals {}})))))

(defn analyze-one
  "Analyze a single form"
  [env form]
  (analyze* env #_(find-ns (-> env :ns :name)) form))

#_(defn forms-seq
  "Lazy seq of forms in a Clojure or ClojureScript file."
  [^java.io.PushbackReader rdr]
  (let [eof (reify)]
    (lazy-seq
      (let [form (read rdr nil eof)]
        (when-not (identical? form eof)
          (lazy-seq (cons form (forms-seq rdr))))))))
       
(defn file-name-for-ns 
  "Returns a file name representing the namespace"
  [ns-sym]
  (-> (@#'clojure.core/root-resource ns-sym)
    (str ".clj")))

(defn ^LineNumberingTextReader
  make-text-reader-for-ns
  "Returns a LineNumberingTextReader for namespace ns-sym"
  [ns-sym]
  (let [file-name (file-name-for-ns ns-sym)]
    (LineNumberingTextReader. (io/text-reader file-name))))

(defonce ^:private Compiler-members (set (map :name (:members (reflect/type-reflect RT)))))
(defonce ^:private RT-members (set (map :name (:members (reflect/type-reflect RT)))))

;FIXME this is probably missing some things
(defmacro ^:private thrd-bindings [source-path source-nsym pushback-reader]
  `(merge
     {;Compiler/LOADER (RT/makeClassLoader)

      ;FIXME can't access these?
      (field Compiler ~'SourcePathVar) (str ~source-path)
      (field Compiler ~'SourceVar) (str ~source-nsym)

      ;Compiler/METHOD nil
      ;Compiler/LOCAL_ENV nil
      ;Compiler/LOOP_LOCALS nil
      ;Compiler/NEXT_LOCAL_NUM 0
      RT/CurrentNSVar @RT/CurrentNSVar
;      Compiler/LINE_BEFORE (.getLineNumber ~pushback-reader)
;      Compiler/LINE_AFTER (.getLineNumber ~pushback-reader)
      RT/UncheckedMathVar @RT/UncheckedMathVar}
     ~(when (RT-members 'WarnOnReflection)
        `{(field RT ~'WarnOnReflection) @(field RT ~'WarnOnReflection)})
;     ~(when (Compiler-members 'COLUMN_BEFORE)
;        `{Compiler/COLUMN_BEFORE (.getColumnNumber ~pushback-reader)})
;     ~(when (Compiler-members 'COLUMN_AFTER)
;        `{Compiler/COLUMN_AFTER (.getColumnNumber ~pushback-reader)})
     ~(when (RT-members 'DataReadersVar)
        `{RT/DataReadersVar @RT/DataReadersVar})
     ))

(defn analyze-ns
  "Takes a LineNumberingTextReader and a namespace symbol.
  Returns a vector of maps, with keys :op, :env. If expressions
  have children, will have :children entry.
  Optionally can use 

  eg. (analyze-path 'my-ns)"
  ([source-nsym] (analyze-ns (make-text-reader-for-ns source-nsym) source-nsym source-nsym))
  ([rdr source-path source-nsym]
   (let [eof (reify)
         ^LineNumberingTextReader 
         pushback-reader (if (instance? LineNumberingTextReader rdr)
                           rdr
                           (LineNumberingTextReader. rdr))]
     (do
       (push-thread-bindings (thrd-bindings source-path source-nsym pushback-reader))
       (try
         (let [eof (reify)]
           (loop [form (read pushback-reader nil eof)
                  out []]
             (if (identical? form eof)
               out
               ;; FIXME shouldn't be source-nsym here
               (let [env {:ns {:name source-nsym} :context :eval :locals {}}
                     m (analyze* env form)
                     _ (eval form)]
                 (recur (read pushback-reader nil eof) (conj out m))))))
         (finally
           (pop-thread-bindings)))))))

(comment
  (ast 
    (try (throw (Exception.)) 
      (catch Exception e (throw e)) 
      (finally 33)))

  (ast
    (let [b 1] 
      (fn [& a] 1)))

  (ast (Integer. (+ 1 1)))

  (ast (map io/file [1 2]))

  (ast (do 
         (require '[clojure.repl :refer [pst]])
         (pst)))
  (ast (deftype A [a b]
         Object
         (toString [this]))))
