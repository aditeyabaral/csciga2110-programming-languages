#lang plai-typed

(require "ps2-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;
;; See ps2-ast.rkt and README.md for more information.


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
    [else (error 'lookup "No binding found.")]))


(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (valC (numV (s-exp->number s)))]
    [(s-exp-boolean? s) (valC (boolV (s-exp->boolean s)))]
    [(s-exp-list? s)
     (let ([l (s-exp->list s)])
       (if (s-exp-list? (first l))
           ;; If the first element is a list, treat it as a list expression
           (listC (map parse l))
           ;; Otherwise, process based on the first symbol
           (case (s-exp->symbol (first l))

             ;; (+ e1 e2)
             [(+) (plusC (parse (second l)) (parse (third l)))]

             ;; (* e1 e2)
             [(*) (timesC (parse (second l)) (parse (third l)))]

             ;; (equal? e1 e2)
             [(equal?) (equal?C (parse (second l)) (parse (third l)))]

             ;; (if guard e1 e2)
             [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]

             ;; (list e1 e2 ... en)
             [(list) (listC (map parse (rest l)))]

             ;; (cons e1 e2)
             [(cons) (consC (parse (second l)) (parse (third l)))]

             ;; (first e)
             [(first) (firstC (parse (second l)))]

             ;; (rest e)
             [(rest) (restC (parse (second l)))]

             ;; (natrec e1 e2 (x y e3))
             [(natrec) 
              (natrecC (parse (second l)) 
                       (parse (third l)) 
                       (s-exp->symbol (first (s-exp->list (fourth l))))
                       (s-exp->symbol (second (s-exp->list (fourth l))))
                       (parse (third (s-exp->list(fourth l)))))]

             ;; (listrec e1 e2 (hd rest res e3))
             [(listrec) 
              (listrecC (parse (second l)) 
                        (parse (third l)) 
                        (s-exp->symbol (first (s-exp->list (fourth l))))
                        (s-exp->symbol (second (s-exp->list (fourth l))))
                        (s-exp->symbol (third (s-exp->list (fourth l)))) 
                        (parse (fourth (s-exp->list(fourth l)))))]

             ;; (let ([x1 e1] [x2 e2] ... [xn en]) e)
             [(let)
              (letC
               (map (lambda (binding)
                      (pair (s-exp->symbol (first (s-exp->list binding)))
                            (parse (second (s-exp->list binding)))))
                    (s-exp->list (second l)))
                    (parse (third l)))]

             ;; (let* ([x1 e1] [x2 e2] ... [xn en]) e)
             [(let*) 
              (let*C
               (map (lambda (binding)
                      (pair (s-exp->symbol (first (s-exp->list binding))) 
                            (parse (second (s-exp->list binding)))))
                    (s-exp->list (second l)))
               (parse (third l)))]

             ;; (unpack (x1 x2 ... xn) e1 e2)
             [(unpack)
              (unpackC (map s-exp->symbol (s-exp->list (second l)))
                       (parse (third l))
                       (parse (fourth l)))]

             ;; Variable identifiers
             [else (idC (s-exp->symbol (first l)))]
           )
       )
     )]

    ;; Default case for variables
    [else (idC (s-exp->symbol s))]
  )
)


(define (eval-env (e : Expr) (env : Env)) : Value
  (type-case Expr e
    ;; Handle value case
    [valC (v) v]

    ;; Handle addition
    [plusC (e1 e2)
           (numV (+ (numV-n (eval-env e1 env)) (numV-n (eval-env e2 env))))]

    ;; Handle multiplication
    [timesC (e1 e2)
            (numV (* (numV-n (eval-env e1 env)) (numV-n (eval-env e2 env))))]

    ;; Handle equality check
    [equal?C (e1 e2)
             (boolV (equal? (eval-env e1 env) (eval-env e2 env)))]

    ;; Handle if expression
    [ifC (guard e1 e2)
         (if (boolV-b (eval-env guard env))
             (eval-env e1 env)
             (eval-env e2 env))]

    ;; Handle list creation
    [listC (es)
           (listV (map (lambda (e) (eval-env e env)) es))]

    ;; Handle cons
    [consC (e1 e2)
           (let ([v1 (eval-env e1 env)]
                 [v2 (listV-vs (eval-env e2 env))])
             (listV (cons v1 v2)))]

    ;; Handle first
    [firstC (e)
            (first (listV-vs (eval-env e env)))]

    ;; Handle rest
    [restC (e)(listV (rest (listV-vs (eval-env e env))))]

    ;; Handle natrec
    [natrecC (e1 e2 x y e3)
             (let ([n (numV-n (eval-env e1 env))])
               (if (zero? n)
                   (eval-env e2 env)
                   (let ([v (eval-env (natrecC (valC (numV (- n 1))) e2 x y e3) env)])
                      (eval-env (letC (list (pair x (valC (numV (- n 1))))
                                            (pair y (valC v)))
                                        e3) env))))]

    ;; Handle listrec
    [listrecC (e1 e2 hd restS res e3)
     (let ([v (listV-vs (eval-env e1 env))])
       (if (empty? v)
           (eval-env e2 env)
           (let ([vrec (eval-env (listrecC (valC (listV (rest v))) e2 hd restS res e3) env)])
             (eval-env (letC (list (pair hd (valC (first v)))
                                   (pair restS (valC (listV (rest v))))
                                   (pair res (valC vrec)))
                              e3) env))))]

    ;; Handle let
    [letC (bindings e)
          (let ([new-env (foldl (lambda (binding env)
                                  (let ([var (fst binding)]
                                        [value (eval-env (snd binding) env)])
                                    (extend-env (bind var value) env)))
                                env
                                bindings)])
            (eval-env e new-env))]

    ;; Handle let*
    [let*C (bindings e)
          (let ([new-env (foldl (lambda (binding env)
                                  (let ([var (fst binding)]
                                        [value (eval-env (snd binding) env)])
                                    (extend-env (bind var value) env)))
                                env
                                bindings)])
            (eval-env e new-env))]


    ;; Handle unpack
    ; (unpack (x1 x2 ... xn) e1 e2)
    ; would be parsed as (unpackC (list x1 x2 ... xn) e1 e2)
    ; Evaluates e1, which can be assumed to yield a list l of the form (v1 v2 ... vn)
    ; Then returns the result of evaluating e2 with x1 bound to v1, x2 bound to v2, ..., xn bound to vn.
    ; It is assumed that the list l has the same length as the length of the 'vars' argument.
    [unpackC (vars e1 e2)
        (let ([l (listV-vs (eval-env e1 env))])
          (eval-env e2 (foldl (lambda (binding env)
                                (let ([var (fst binding)]
                                      [value (snd binding)])
                                  (extend-env (bind var value) env))) env list 

    ;; Handle variable identifiers
    [idC (x) (lookup x env)]
 )
  )



(define (eval (e : Expr)) : Value
  (eval-env e empty-env))

(define l '(let ((x 5)) (let ((x (* x 2)) (y x)) (+ x y))))
(define ll (parse l))
(define evaluated (eval ll))
