#lang plai-typed
(require "ps4-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval-base should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;

;; See ps4-ast.rkt and README.md for more information.

;; Note that as in the previous problem set you probably want to implement a version
;; of eval that can return more general values and takes an environment / store as arguments.
;; Your eval-base would then be a wrapper around this more general eval that tries to conver the value
;; to a BaseValue, and fails if it cannot be converted.
;;
;; For grading, the test cases all result in values that can be converted to base values.

(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closV (env : Env) (x : symbol) (e : Expr)]
  [objV (delegate : (optionof Value))
        (fields : (listof (symbol * Location)))
        (methods : (listof (symbol * Method)))])

(define-type Method
  [method (md : MethodDecl) (env : Env)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)

(define-type Result
  [res (v : Value) (s : Store)])

(define-type-alias Location number)
(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type-alias Store (listof Storage))
(define empty-store empty)
(define override-store cons)

(define-type EvaluatedFields
  [evaluated-fields (fields : (listof (symbol * Location))) (sto : Store)])

(define-type EvaluatedArguments
  [evaluated-arguments (args : (listof Value)) (sto : Store)])

(define (lookup (x : symbol) (env : Env)) : Value
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))

(define (fetch (l : Location) (sto : Store)) : Value
  (cond
    [(cons? sto)
     (if (equal? (cell-location (first sto)) l)
         (cell-val (first sto))
         (fetch l (rest sto)))]
    [else (error 'fetch "No location found")]))

(define (parse-field (f : s-expression)) : (symbol * Expr)
  (let ([l (s-exp->list f)])
    (pair (s-exp->symbol (first l))
          (parse (second l)))))

(define (parse-method (m : s-expression)) : MethodDecl
  (let ([l (s-exp->list m)])
    (method-decl (s-exp->symbol (first l))
                 (map s-exp->symbol (s-exp->list (second l)))
                 (parse (third l)))))

(define create-location
  (let ([counter (box 0)])
    (lambda ()
      (let ([ctr (unbox counter)])
        (begin (set-box! counter (+ 1 ctr)) ctr)))))

(define (evaluate-fields(fields : (listof (symbol * Expr))) (env : Env) (sto : Store)) :  EvaluatedFields
  (if (empty? fields) (evaluated-fields empty sto)
      (let* ([field (first fields)]
             [name (fst field)]
             [expr (snd field)]
             [result (eval-env env sto expr)]
             [value (res-v result)]
             [new-sto (res-s result)]
             [location (create-location)]
             [combined-sto (override-store (cell location value) new-sto)]
             [rest-result (evaluate-fields (rest fields) env combined-sto)]
             [rest-fields (evaluated-fields-fields rest-result)]
             [final-sto (evaluated-fields-sto rest-result)])
        (evaluated-fields (cons (pair name location) rest-fields) final-sto)))
  )

(define (build-methods (methods : (listof MethodDecl)) (env : Env)) : (listof (symbol * Method))
  (map (lambda (md) (pair (method-decl-name md) (method md env))) methods))

(define (method-assoc (name : symbol) (methods : (listof (symbol * Method)))) : (optionof (symbol * Method))
  (cond
    [(empty? methods) (none)]
    [(equal? (fst (first methods)) name) (some (first methods))]
    [else (method-assoc name (rest methods))]))

(define (find-method (o : Value) (name : symbol)) : (optionof Method)
  (type-case Value o
    [objV (delegate fields methods)
          (let ([method-opt (method-assoc name methods)])
            (type-case (optionof (symbol * Method)) method-opt
              [some (method) (some (snd method))]
              [none ()
                    (type-case (optionof Value) delegate
                      [some (delegate-expr) (find-method delegate-expr name)]
                      [none () (none)])]))]
    [else (error 'find-method "Expected objV")]))

(define (find-location (o : Value) (name : symbol)) : (optionof Location)
  (type-case Value o
    [objV (delegate fields methods)
          (let ([location-opt (find-field name fields)])
            (type-case (optionof Location) location-opt
              [some (location) (some location)]
              [none ()
                    (type-case (optionof Value) delegate
                      [some (delegate-expr) (find-location delegate-expr name)]
                      [none () (none)])]))]
    [else (none)]))

(define (find-field (name : symbol) (fields : (listof (symbol * Location)))) : (optionof Location)
  (cond
    [(empty? fields) (none)]
    [(equal? (fst (first fields)) name) (some (snd (first fields)))]
    [else (find-field name (rest fields))]))

(define (bind-function (f : (symbol Value -> Binding)) (symbols : (listof symbol)) (values : (listof Value))) : (listof Binding)
  (if (or (empty? symbols) (empty? values)) empty
      (cons (f (first symbols) (first values))
            (bind-function f (rest symbols) (rest values)))))

(define (evaluate-arguments (args : (listof Expr)) (env : Env) (sto : Store)) : EvaluatedArguments
  (if (empty? args) (evaluated-arguments empty sto)
      (let* ([result (eval-env env sto (first args))]
             [value (res-v result)]
             [new-sto (res-s result)]
             [rest-result (evaluate-arguments (rest args) env new-sto)]
             [rest-values (evaluated-arguments-args rest-result)]
             [final-sto (evaluated-arguments-sto rest-result)])
        (evaluated-arguments (cons value rest-values) final-sto))))

(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([l (s-exp->list s)])
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(+) (plusC (parse (second l)) (parse (third l)))]
            [(*) (timesC (parse (second l)) (parse (third l)))]
            [(equal?) (equal?C (parse (second l)) (parse (third l)))]
            [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
            [(lambda) (lambdaC (s-exp->symbol (second l)) (parse (third l)))]
            [(begin) (beginC (map parse (rest l)))]
            [(object)
             (objectC (none)
                      (map parse-field (s-exp->list (second l)))
                      (map parse-method (s-exp->list (third l))))]
            [(object-del)
             (objectC (some (parse (second l)))
                      (map parse-field (s-exp->list (third l)))
                      (map parse-method (s-exp->list (fourth l))))]
            [(msg) (msgC (parse (second l)) (s-exp->symbol (third l)) (map parse (rest (rest (rest l)))))]
            [(get-field) (get-fieldC (s-exp->symbol (second l)))]
            [(set-field!) (set-field!C (s-exp->symbol (second l)) (parse (third l)))]
            [else (appC (parse (first l)) (parse (second l)))]
            )]
         [(s-exp-list? (first l)) (appC (parse (first l)) (parse (first (rest l))))]
         ))]))


(define (eval-env (env : Env) (sto : Store) (e : Expr)) : Result
  (type-case Expr e

    [numC (n) (res (numV n) sto)]

    [boolC (b) (res (boolV b) sto)]

    [plusC (e1 e2)
           (let* ([result1 (eval-env env sto e1)]
                  [v1 (res-v result1)]
                  [s1 (res-s result1)]
                  [result2 (eval-env env s1 e2)]
                  [v2 (res-v result2)]
                  [s2 (res-s result2)])
             (res (numV (+ (numV-n v1) (numV-n v2))) s2))]

    [timesC (e1 e2)
            (let* ([result1 (eval-env env sto e1)]
                   [v1 (res-v result1)]
                   [s1 (res-s result1)]
                   [result2 (eval-env env s1 e2)]
                   [v2 (res-v result2)]
                   [s2 (res-s result2)])
              (res (numV (* (numV-n v1) (numV-n v2))) s2))]

    [equal?C (e1 e2)
             (let* ([result1 (eval-env env sto e1)]
                    [v1 (res-v result1)]
                    [s1 (res-s result1)]
                    [result2 (eval-env env s1 e2)]
                    [v2 (res-v result2)]
                    [s2 (res-s result2)])
               (res (boolV (equal? v1 v2)) s2))]

    [ifC (guard e1 e2)
         (let* ([result1 (eval-env env sto guard)]
                [v1 (res-v result1)]
                [s1 (res-s result1)])
           (if (boolV-b v1)
               (eval-env env s1 e1)
               (eval-env env s1 e2)))]

    [idC (x) (res (lookup x env) sto)]

    [letC (x e1 e2)
          (let* ([result1 (eval-env env sto e1)]
                 [v1 (res-v result1)]
                 [s1 (res-s result1)]
                 [env1 (extend-env (bind x v1) env)])
            (eval-env env1 s1 e2))]

    [lambdaC (x e)
             (res (closV env x e) sto)]

    [appC (e1 e2)
          (let* ([result1 (eval-env env sto e1)]
                 [v1 (res-v result1)]
                 [s1 (res-s result1)]
                 [result2 (eval-env env s1 e2)]
                 [v2 (res-v result2)]
                 [s2 (res-s result2)])
            (type-case Value v1
              [closV (clos-env parameter body)
                     (eval-env (extend-env (bind parameter v2) clos-env) s2 body)]
              [else (error 'appC "Expected closure")]))]

    [beginC (es)
            (letrec ([loop (lambda (es current-sto last-result)
                             (if (empty? es)
                                 (res last-result current-sto)
                                 (let* ([result (eval-env env current-sto (first es))]
                                        [new-val (res-v result)]
                                        [new-sto (res-s result)])
                                   (loop (rest es) new-sto new-val))))])
              (loop es sto (boolV #f)))]

    [objectC (delegate fields methods)
             (type-case (optionof Expr) delegate
               [none ()
                     (let* ([field-evals (evaluate-fields fields env sto)]
                            [field-values (evaluated-fields-fields field-evals)]
                            [new-sto (evaluated-fields-sto field-evals)]
                            [built-methods (build-methods methods env)]
                            [obj (objV (none) field-values built-methods)])
                       (res obj new-sto))]
               [some (delegate-expr)
                     (let* ([result (eval-env env sto delegate-expr)]
                            [delegate-value (res-v result)]
                            [new-sto (res-s result)])
                       (type-case Value delegate-value
                         [objV (delegate-fields delegate-methods delegate-delegate)
                               (let* ([field-evals (evaluate-fields fields env new-sto)]
                                      [field-values(evaluated-fields-fields field-evals)]
                                      [final-sto (evaluated-fields-sto field-evals)]
                                      [built-methods (build-methods methods env)]
                                      [obj (objV (some delegate-value) field-values built-methods)])
                                 (res obj final-sto))]
                         [else (error 'objectC "delegate is not an objV")]))])]

    [msgC (o method args)
          (type-case Result (eval-env env sto o)
            [res (obj initial-sto)
                 (type-case Value obj
                   [objV (delegate fields methods)
                         (let* ([arg-evals (evaluate-arguments args env initial-sto)]
                                [arg-values (evaluated-arguments-args arg-evals)]
                                [new-sto (evaluated-arguments-sto arg-evals)]
                                [method-opt (find-method obj method)])
                           (type-case (optionof Method) method-opt
                             [some (method)
                                   (let* ([method-decl (method-md method)]
                                          [declared-args (method-decl-args method-decl)]
                                          [expected-args (length declared-args)]
                                          [actual-args(+ 1 (length args))]
                                          [bindings (bind-function bind declared-args (cons obj arg-values))]
                                          [updated-env (append bindings (method-env method))])
                                     (eval-env updated-env new-sto (method-decl-body method-decl)))]
                             [none () (error 'msgC (string-append "Method not found: " (symbol->string method)))]))]
                   [else (error 'msgC "Expected objectV")])])]

    [get-fieldC (name)
                (let ([o (lookup 'self env)])
                  (let ([location-opt (find-location o name)])
                    (cond
                      [(none? location-opt) (error 'get-fieldC (string-append "Field not found: " (symbol->string name)))]
                      [(some? location-opt)
                       (type-case (optionof Location) location-opt
                         [some (location) (res (fetch location sto) sto)]
                         [none () (error 'get-fieldC "Unexpected none in location")])]
                      [else (error 'get-fieldC "Unexpected none in location")])))]

    [set-field!C (name e)
                 (type-case Result (eval-env env sto e)
                   [res (value sto)
                        (let ([o (lookup 'self env)])
                          (let ([location-opt (find-location o name)])
                            (cond
                              [(none? location-opt) (error 'set-field!C (string-append "Field not found: " (symbol->string name)))]
                              [(some? location-opt)
                               (type-case (optionof Location) location-opt
                                 [some (location) (res value (override-store (cell location value) sto))]
                                 [none () (error 'set-field!C "Unexpected none in location")])]
                              [else (error 'set-field!C "Unexpected none in location")])
                            ))])]
    ))


(define (value->base (v : Value)) : BaseValue
  (type-case Value v
    [numV (n) (numBV n)]
    [boolV (b) (boolBV b)]
    [closV (param body env) (error 'value->base "Cannot convert closure")]
    [objV (delegate fields methods) (error 'value->base "Cannot convert object")]))


(define (eval-base (e : Expr)) : BaseValue
  (let ([value (eval-env empty-env empty-store e)])
    (value->base (res-v value))))

