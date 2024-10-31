#lang plai-typed
(require "ps3-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval-base should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;

;; See ps3-ast.rkt and README.md for more information.

;; Note that as in lecture 6, you probably want to implement a version
;; of eval that returns a result that can be an arbitrary value (not just
;; a BaseValue) and also returns a store.  Your eval-base would then be a
;; wrapper around this more general eval that tries to conver the value
;; to a BaseValue, and fails if it cannot be.
;;
;; For grading, the test cases all result in values that can be converted to base values.

(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [pairV (value1 : Value) (value2 : Value)]
  [closV (env : Env) (x : symbol) (e : Expr)]
  [boxV (l : Location)]
  [vectorV (elements : (listof Value))]
  [subvectorV (original : Location) (offset : number) (length : number)])


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


(define new-loc
  (let ([counter (box 0)])
    (lambda ()
      (let ([l (unbox counter)])
        (begin (set-box! counter (+ 1 l))
               l)))))


(define (list->replace elements idx new-value)
  (build-list (length elements)
              (lambda (current-idx) (if (= current-idx idx) new-value
                                        (list-ref elements current-idx)))))

(define (store->eval-idx-update env s1 e1 e2 elements loc offset)
  (let* ([idx (eval-env env s1 e1)]
         [s2 (res-s idx)]
         [idx2 (numV-n (res-v idx))]
         [value(eval-env env s2 e2)]
         [new-value (res-v value)]
         [s3 (res-s value)]
         [index-updated (+ idx2 offset)]
         [new-elements (list->replace elements index-updated new-value)]
         [new-store (override-store (cell loc (vectorV new-elements)) s3)])
    (res new-value new-store)))


(define (store->vector vref sto)
  (type-case Value vref
    [boxV (loc)
          (type-case Value (fetch loc sto)
            [vectorV (elements) elements]
            [else (error 'eval-env "Expected Value")])]
    [subvectorV (orig-loc offset len)
                (type-case Value (fetch orig-loc sto)
                  [vectorV (elements) elements]
                  [else (error 'eval-env "Expected subvectorV")])]
    [else (error 'eval-env "Expected boxV")]))


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
            [(pair) (pairC (parse (second l)) (parse (third l)))]
            [(fst) (fstC (parse (second l)))]
            [(snd) (sndC (parse (second l)))]
            [(+) (plusC (parse (second l)) (parse (third l)))]
            [(*) (timesC (parse (second l)) (parse (third l)))]
            [(equal?) (equal?C (parse (second l)) (parse (third l)))]
            [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
            [(lambda) (lambdaC (s-exp->symbol (second l)) (parse (third l)))]
            [(box) (boxC (parse (second l)))]
            [(unbox) (unboxC (parse (second l)))]
            [(set-box!) (setboxC (parse (second l)) (parse (third l)))]
            [(vector) (vectorC (map parse (rest l)))]
            [(vector-length) (vector-lengthC (parse (second l)))]
            [(vector-ref) (vector-refC (parse (second l)) (parse (third l)))]
            [(vector-set!) (vector-set!C (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(vector-make) (vector-makeC (parse (second l)) (parse (third l)))]
            [(subvector) (subvectorC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(begin) (beginC (map parse (rest l)))]
            [(transact) (transactC (parse (second l)))]
            [else (appC (parse (first l)) (parse (second l)))]
            )]
         [(s-exp-list? (first l)) (appC (parse (first l)) (parse (first (rest l))))]
         ))]))


(define (eval-env (env : Env) (sto : Store) (e : Expr)) : Result
  (type-case Expr e

    [numC (n) (res (numV n) sto)]

    [boolC (b) (res (boolV b) sto)]

    [pairC (e1 e2)
           (let* ([result1 (eval-env env sto e1)]
                  [v1 (res-v result1)]
                  [s1 (res-s result1)]
                  [result2 (eval-env env s1 e2)]
                  [v2 (res-v result2)]
                  [s2 (res-s result2)])
             (res (pairV v1 v2) s2))]

    [fstC (e)
          (let* ([result (eval-env env sto e)]
                 [v (res-v result)]
                 [s (res-s result)])
            (res (pairV-value1 v) s))]

    [sndC (e)
          (let* ([result (eval-env env sto e)]
                 [v (res-v result)]
                 [s (res-s result)])
            (res (pairV-value2 v) s))]

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

    [boxC (e)
          (let* ([result (eval-env env sto e)]
                 [v (res-v result)]
                 [s (res-s result)]
                 [l (new-loc)])
            (res (boxV l) (override-store (cell l v) s)))]

    [unboxC (e)
            (let* ([result (eval-env env sto e)]
                   [v (res-v result)]
                   [s (res-s result)])
              (type-case Value v
                [boxV (l) (res (fetch l s) s)]
                [else (error 'unboxC "Expected boxV")]))]

    [setboxC (e1 e2)
             (let* ([result1 (eval-env env sto e1)]
                    [v1 (res-v result1)]
                    [s1 (res-s result1)]
                    [result2 (eval-env env s1 e2)]
                    [v2 (res-v result2)]
                    [s2 (res-s result2)])
               (type-case Value v1
                 [boxV (l)
                       (res v2 (override-store (cell l v2) s2))]
                 [else (error 'setboxC "Expected boxV")]))]

    [vectorC (e1)
             (letrec ([eval-vec
                       (lambda (elements acc current-sto)
                         (if (empty? elements)
                             (let* ([loc (new-loc)]
                                    [vec (vectorV (reverse acc))]
                                    [cell (cell loc vec)]
                                    [new-sto (override-store cell current-sto)])
                               (res (boxV loc) new-sto))
                             (type-case Result (eval-env env current-sto (first elements))
                               [res (val new-sto)
                                    (eval-vec (rest elements)
                                              (cons val acc)
                                              new-sto)])))])
               (eval-vec e1 empty sto))]

    [vector-lengthC (e)
                    (let* ([result (eval-env env sto e)]
                           [vref (res-v result)]
                           [s1 (res-s result)])
                      (type-case Value vref
                        [boxV (loc)
                              (res (numV (length (store->vector vref s1))) s1)]
                        [subvectorV (orig-loc offset len)
                                    (res (numV len) s1)]
                        [else (error 'eval-env "Not vref")]))]

    [vector-refC (e1 e2)
                 (type-case Result (eval-env env sto e1)
                   [res (v-ref sto-1)
                        (type-case Result (eval-env env sto-1 e2)
                          [res (n sto-2)
                               (type-case Value n
                                 [numV (index)
                                       (let* ([elements (store->vector v-ref sto-2)]
                                              [offset (if (boxV? v-ref)
                                                          0
                                                          (subvectorV-offset v-ref))])
                                         (res (list-ref elements (+ offset index)) sto-2))]
                                 [else (error 'eval-env "not a number")])])])]
    [vector-set!C (e1 e2 e3)
                  (type-case Result (eval-env env sto e1)
                    [res (v-ref sto-1)
                         (let* ([elements (store->vector v-ref sto-1)]
                                [loc (if (boxV? v-ref)
                                         (boxV-l v-ref)
                                         (subvectorV-original v-ref))]
                                [offset (if (boxV? v-ref)
                                            0
                                            (subvectorV-offset v-ref))])
                           (store->eval-idx-update env sto-1 e2 e3 elements loc offset))])]
    [vector-makeC (e1 e2)
                  (type-case Result (eval-env env sto e1)
                    [res (n sto-1)
                         (type-case Value n
                           [numV (length)
                                 (if (>= length 0)
                                     (type-case Result (eval-env env sto-1 e2)
                                       [res (v sto-2)
                                            (let* ([loc (new-loc)]
                                                   [vec (vectorV (build-list length (lambda (_) v)))]
                                                   [new-sto (override-store (cell loc vec) sto-2)])
                                              (res (boxV loc) new-sto))])
                                     (error 'eval-env "length should be positive"))]
                           [else (error 'eval-env "not a numberr")])])]
    [subvectorC (e offset len)
                (type-case Result (eval-env env sto e)
                  [res (v-ref sto-1)
                       (let ([elements (store->vector v-ref sto-1)])
                         (type-case Result (eval-env env sto-1 offset)
                           [res (n sto-2)
                                (type-case Value n
                                  [numV (start)
                                        (type-case Result (eval-env env sto-2 len)
                                          [res (l sto-3)
                                               (type-case Value l
                                                 [numV (sublen)
                                                       (if (and (>= start 0)
                                                                (<= start (length elements))
                                                                (>= sublen 0)
                                                                (<= (+ start sublen) (length elements)))
                                                           (res (subvectorV (if (boxV? v-ref)
                                                                                (boxV-l v-ref)
                                                                                (subvectorV-original v-ref))
                                                                            start sublen) sto-3)
                                                           (error 'eval-env "invaild bound"))]
                                                 [else (error 'eval-env "expected number")])])]
                                  [else (error 'eval-env "expected number")])]))])]

    [beginC (es)
            (letrec ([loop (lambda (es current-sto last-result)
                             (if (empty? es)
                                 (res last-result current-sto)
                                 (let* ([result (eval-env env current-sto (first es))]
                                        [new-val (res-v result)]
                                        [new-sto (res-s result)])
                                   (loop (rest es) new-sto new-val))))])
              (loop es sto (boolV #f)))]

    [transactC (e)
               (type-case Result (eval-env env sto e)
                 [res (v sto-1)
                      (type-case Value v
                        [pairV (commit? result)
                               (type-case Value commit?
                                 [boolV (b) (res result (if b sto-1 sto))]
                                 [else (error 'transactC "expected bool")])]
                        [else (error 'transactC "expected pair")])])]
    ))


(define (value->base (v : Value)) : BaseValue
  (type-case Value v
    [numV (n) (numBV n)]
    [boolV (b) (boolBV b)]
    [pairV (value1 value2)
           (let ([v1 (value->base value1)]
                 [v2 (value->base value2)])
             (pairBV v1 v2))]
    [else (error 'value->base "Conversion error")]
    ))


(define (eval-base (e : Expr)) : BaseValue
  (let ([value (eval-env empty-env empty-store e)])
    (value->base (res-v value))))
