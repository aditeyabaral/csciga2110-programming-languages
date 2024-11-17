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
        (methods : (listof MethodDecl))])

(define-type Binding
  [bind (name : symbol) (val : Value)])


(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)


(define (lookup (x : symbol) (env : Env)) : Value
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))


(define-type Result
  [res (v : Value) (s : Store)])


(define-type-alias Location number)
(define-type Storage
  [cell (location : Location) (val : Value)])


(define-type-alias Store (listof Storage))
(define empty-store empty)
(define override-store cons)


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
            [(msg) (msgC (parse (second l)) (s-exp->symbol (third l)) (map parse (rest (rest l))))]
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

