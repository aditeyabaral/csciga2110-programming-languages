#lang plai-typed
(require "ps5-ast.rkt")

(define (parse-ty (s : s-expression)) : Type
  (cond
    [(s-exp-symbol? s)
     (case (s-exp->symbol s)
       [(boolT) (boolT)]
       [(voidT) (voidT)]
       [(numT) (numT)])]
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(funT) (funT (parse-ty (second l)) (parse-ty (third l)))]
            [(pairT) (pairT (parse-ty (second l)) (parse-ty (third l)))]
            [(boxT) (boxT (parse-ty (second l)))]
            [(listT) (listT (parse-ty (second l)))]
            )]))]))

(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(+) (plusC (parse (second l)) (parse (third l)))]
            [(*) (timesC (parse (second l)) (parse (third l)))]
            [(pair) (pairC (parse (second l)) (parse (third l)))]
            [(equal?) (equal?C (parse (second l)) (parse (third l)))]
            [(cons) (consC (parse (second l)) (parse (third l)))]
            [(is-empty?) (is-empty?C (parse (second l)))]
            [(empty) (emptyC (parse-ty (second l)))]
            [(first) (firstC (parse (second l)))]
            [(rest) (restC (parse (second l)))]
            [(fst) (fstC (parse (second l)))]
            [(snd) (sndC (parse (second l)))]
            [(box) (boxC (parse (second l)))]
            [(unbox) (unboxC (parse (second l)))]
            [(set-box!) (set-box!C (parse (second l)) (parse (third l)))]
            [(lambda) (lambdaC (s-exp->symbol (second l)) (parse-ty (third l)) (parse (fourth l)))]
            [(rec) (recC (s-exp->symbol (second l)) (s-exp->symbol (third l)) (parse-ty (fourth l))
                         (parse-ty (list-ref l 4)) (parse (list-ref l 5)))]
            [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
            [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [else (appC (parse (first l)) (parse (second l)))]
            )]
         [else (appC (parse (first l)) (parse (second l)))]
         ))]
    ))



(define-type (Binding 'a)
  [bind (name : symbol) (val : 'a)])

(define-type-alias TyEnv (listof (Binding Type)))
(define empty-env empty)
(define extend-env cons)

(define (lookup (x : symbol) (env : (listof (Binding 'a)))) : 'a
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))


; TODO: you must implement this.
; It if e has type t under environment env, then
; (tc-env env e) should return t.
; Otherwise, if e is not well-typed (i.e. does not type check), tc-env should raise an exception
; of some form using the 'error' construct in plai-typed.

(define (tc-env (env : TyEnv) (e : Expr)) : Type
  (cond
    [(numC? e) (numT)]

    [(voidC? e) (voidT)]

    [(boolC? e) (boolT)]

    [(pairC? e)
     (pairT (tc-env env (pairC-e1 e)) (tc-env env (pairC-e2 e)))]

    [(fstC? e)
     (let ([pair-type  (tc-env env (fstC-e e))])
       (cond
         [(pairT? pair-type) (pairT-t1 pair-type)]
         [else (error 'tc-env "fst requires a pair type")]))]

    [(sndC? e)
     (let ([pair-type (tc-env env (sndC-e e))])
       (cond
         [(pairT? pair-type ) (pairT-t2 pair-type )]
         [else (error 'tc-env "snd requires a pair type")]))]

    [(plusC? e)
     (let ([t1 (tc-env env (plusC-e1 e))]
           [t2 (tc-env env (plusC-e2 e))])
       (if (and (numT? t1) (numT? t2))
           (numT)
           (error 'tc-env "plus requires numeric types")))]

    [(timesC? e)
     (let ([t1 (tc-env env (timesC-e1 e))]
           [t2 (tc-env env (timesC-e2 e))])
       (if (and (numT? t1) (numT? t2))
           (numT)
           (error 'tc-env "times requires numeric types")))]

    [(equal?C? e)
     (let ([t1 (tc-env env (equal?C-e1 e))]
           [t2 (tc-env env (equal?C-e2 e))])
       (if (equal? t1 t2)
           (boolT)
           (error 'tc-env "equal requires equal types")))]

    [(letC? e)
     (let ([e1-type (tc-env env (letC-e1 e))])
       (tc-env (extend-env (bind (letC-x e) e1-type) env) (letC-e2 e)))]

    [(lambdaC? e)
     (let ([body-type (tc-env (extend-env (bind (lambdaC-x e) (lambdaC-argT e)) env)
                              (lambdaC-e e))])
       (funT (lambdaC-argT e) body-type))]

    [(appC? e)
     (let ([f-type (tc-env env (appC-e1 e))]
           [arg-type (tc-env env (appC-e2 e))])
       (cond
         [(funT? f-type)
          (if (equal? arg-type (funT-arg f-type))
              (funT-ret f-type)
              (error 'tc-env "function argument type mismatch"))]
         [else (error 'tc-env "cannot apply non-function type")]))]

    [(idC? e)
     (lookup (idC-x e) env)]

    [(ifC? e)
     (let ([guard-type (tc-env env (ifC-e e))]
           [then-type (tc-env env (ifC-e1 e))]
           [else-type (tc-env env (ifC-e2 e))])
       (if (boolT? guard-type)
           (if (equal? then-type else-type)
               then-type
               (error 'tc-env "if branches must have same type"))
           (error 'tc-env "Iif condition must return boolean")))]

    [(emptyC? e) (listT (emptyC-t e))]

    [(consC? e)
     (let ([e1-type (tc-env env (consC-e1 e))]
           [e2-type (tc-env env (consC-e2 e))])
       (cond
         [(listT? e2-type)
          (if (equal? e1-type (listT-t e2-type))
              e2-type
              (error 'tc-env "cons requires matching list element type"))]
         [else (error 'tc-env "cons second argument must be a list")]))]

    [(firstC? e)
     (let ([list-type (tc-env env (firstC-e e))])
       (cond
         [(listT? list-type) (listT-t list-type)]
         [else (error 'tc-env "first requires list type")]))]

    [(restC? e)
     (let ([list-type (tc-env env (restC-e e))])
       (cond
         [(listT? list-type) list-type]
         [else (error 'tc-env "rest requires list type")]))]

    [(is-empty?C? e)
     (let ([list-type (tc-env env (is-empty?C-e e))])
       (cond
         [(listT? list-type) (boolT)]
         [else (error 'tc-env "is-empty? requires list type")]))]

    [(recC? e)
     (let ([env-with-rec (extend-env (bind (recC-f e)
                                           (funT (recC-argT e) (recC-retT e)))
                                     env)])
       (let ([body-type (tc-env (extend-env (bind (recC-x e) (recC-argT e))
                                            env-with-rec)
                                (recC-e e))])
         (if (equal? body-type (recC-retT e))
             (funT (recC-argT e) (recC-retT e))
             (error 'tc-env "rec function body type mismatch"))))]

    [(boxC? e)
     (let ([e-type (tc-env env (boxC-e e))])
       (boxT e-type))]

    [(unboxC? e)
     (let ([box-type (tc-env env (unboxC-e e))])
       (cond
         [(boxT? box-type) (boxT-t box-type)]
         [else (error 'tc-env "unbox requires box type")]))]

    [(set-box!C? e)
     (let ([box-type (tc-env env (set-box!C-e1 e))]
           [val-type (tc-env env (set-box!C-e2 e))])
       (cond
         [(boxT? box-type)
          (if (equal? (boxT-t box-type) val-type)
              (voidT)
              (error 'tc-env "set-box! requires matching type"))]
         [else (error 'tc-env "set-box! first argument must be a box")]))]

    [else (error 'tc-env "unknown expression type")]

    )
  )

(define (tc (e : Expr))
  (tc-env empty-env e))

