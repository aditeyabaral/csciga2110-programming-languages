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
  [pairV (v1 : Value) (v2 : Value)]
  [closV (env : Env) (x : symbol) (e : Expr)]
  [boxV (l : Location)]
  [vectorV (elements : (vectorof Value))]
  [subvectorV (original : Value) (offset : number) (length : number)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type Result
  [res (v : Value) (s : Store)])

(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)

(define-type-alias Location number)
(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type-alias Store (listof Storage))
(define empty-store empty)
(define override-store cons)

(define (fetch (l : Location) (sto : Store)) : Value
  (cond
    [(empty? sto) (error 'fetch "No location found")]
    [(= l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

(define new-loc
  (let ([counter (box 0)])
    (lambda ()
      (let ([l (unbox counter)])
        (begin (set-box! counter (+ l 1)) l)))))

(define (lookup (x : symbol) (env : Env)) : Value
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))

(define (sublist->left lst n)
  (if (or (<= n 0) (empty? lst))
      empty
      (cons (first lst) (sublist->left (rest lst) (- n 1)))))

(define (sublist->right lst n)
  (if (or (<= n 0) (empty? lst))
      lst
      (sublist->right (rest lst) (- n 1))))

(define (vector->list vec)
  (letrec ([loop (lambda (i acc)
                   (if (>= i (vector-length vec))
                       (reverse acc)
                       (loop (+ i 1) (cons (vector-ref vec i) acc))))])
    (loop 0 empty)))

(define (list->vector lst)
  (let ([vec (make-vector (length lst) (boolV #f))])  ; Initialize vector with `#f`
    (letrec ([loop (lambda (i lst)
                     (if (empty? lst)
                         vec
                         (begin
                           (vector-set! vec i (first lst))
                           (loop (+ i 1) (rest lst)))))])
      (loop 0 lst))))

(define (copy-vector val)
  (type-case Value val
    [vectorV (elements) (vectorV (list->vector (vector->list elements)))]
    [else val]))

(define (restore-original-store (sto : Store) (original-values : (listof Value))) : Store
  (if (empty? sto)
      empty
      (let ([entry (first sto)]
            [orig-val (first original-values)]
            [rest-sto (rest sto)]
            [rest-vals (rest original-values)])
        (cons (if (vectorV? (cell-val entry))
                  (cell (cell-location entry) orig-val)  ; Restore original vector value
                  entry)                                ; Keep non-vector cells as is
              (restore-original-store rest-sto rest-vals)))))

(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let* ([l (s-exp->list s)]
            [op (first l)]
            [args (rest l)])
       (cond
         [(s-exp-symbol? op)
          (case (s-exp->symbol op)
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
            [else (appC (parse op) (parse (second l)))]
            )]
         [(s-exp-list? op) (appC (parse op) (parse (first args)))]
         ))]))

(define (eval-env (env : Env) (sto : Store) (e : Expr)) : Result
  (type-case Expr e

    [numC (n) (res (numV n) sto)]

    [boolC (b) (res (boolV b) sto)]

    [pairC (e1 e2)
           (let ([result1 (eval-env env sto e1)])
             (let ([v1 (res-v result1)]
                   [s1 (res-s result1)])
               (let ([result2 (eval-env env s1 e2)])
                 (let ([v2 (res-v result2)]
                       [sto2 (res-s result2)])
                   (res (pairV v1 v2) sto2)))))]

    [fstC (e)
          (let* ([result (eval-env env sto e)]
                 [v (res-v result)]
                 [s (res-s result)])
            (res (pairV-v1 v) s))]

    [sndC (e)
          (let* ([result (eval-env env sto e)]
                 [v (res-v result)]
                 [s (res-s result)])
            (res (pairV-v2 v) s))]

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

    [vectorC (es)
             (letrec ([loop (lambda (elements current-sto evaluated-items)
                              (if (empty? elements)
                                  (res (vectorV (list->vector (reverse evaluated-items))) current-sto)
                                  (let* ([result (eval-env env current-sto (first elements))]
                                         [v (res-v result)]
                                         [next-sto (res-s result)])
                                    (loop (rest elements) next-sto (cons v evaluated-items)))))])
               (loop es sto empty))]
    [vector-lengthC (e)
                    (let* ([result (eval-env env sto e)]
                           [vec (res-v result)]
                           [current-sto (res-s result)])
                      (type-case Value vec
                        [vectorV (elements)
                                 (res (numV (vector-length elements)) current-sto)]
                        [subvectorV (original offset length)
                                    (res (numV length) current-sto)]  ; Return the specified subvector length
                        [else
                         (error 'vector-lengthC "Expected a vectorV or subvectorV")]))]

    [vector-refC (e1 e2)
                 (let* ([result1 (eval-env env sto e1)]
                        [vec (res-v result1)]
                        [sto1 (res-s result1)]
                        [result2 (eval-env env sto1 e2)]
                        [idx (numV-n (res-v result2))]
                        [sto2 (res-s result2)])
                   (cond
                     [(vectorV? vec)
                      (res (vector-ref (vectorV-elements vec) idx) sto2)]
                     [(subvectorV? vec)
                      (let ([orig-elements (vectorV-elements (subvectorV-original vec))]
                            [offset (subvectorV-offset vec)])
                        (res (vector-ref orig-elements (+ offset idx)) sto2))]
                     [else (error 'vector-refC "Expected a vectorV or subvectorV")]))]
    [vector-set!C (e1 e2 e3)
                  (let* ([result1 (eval-env env sto e1)]
                         [vec (res-v result1)]
                         [sto1 (res-s result1)]
                         [result2 (eval-env env sto1 e2)]
                         [idx (numV-n (res-v result2))]
                         [sto2 (res-s result2)]
                         [result3 (eval-env env sto2 e3)]
                         [val (res-v result3)]
                         [sto3 (res-s result3)])
                    (type-case Value vec
                      [vectorV (elements)
                               (if (and (>= idx 0) (< idx (vector-length elements)))
                                   (begin
                                     (vector-set! elements idx val)  ; Directly mutate the vector
                                     (res vec sto3))
                                   (error 'vector-set!C "Index out of bounds"))]
                      [subvectorV (original offset length)
                                  (let ([orig-elements (vectorV-elements original)])
                                    (if (and (>= (+ offset idx) offset)
                                             (< (+ offset idx) (+ offset length)))
                                        (begin
                                          (vector-set! orig-elements (+ offset idx) val)
                                          (res vec sto3))
                                        (error 'vector-set!C "Index out of bounds in subvector")))]
                      [else (error 'vector-set!C "Expected a vectorV or subvectorV")]))]
    [vector-makeC (e1 e2)
                  (let* ([result1 (eval-env env sto e1)]
                         [size (numV-n (res-v result1))]
                         [sto1 (res-s result1)]
                         [result2 (eval-env env sto1 e2)]
                         [val (res-v result2)]
                         [sto2 (res-s result2)]
                         [values (make-vector size val)])  ;; Create a vector of `size`, filled with `val`
                    (res (vectorV values) sto2))]

    ; Subvectors and transactions
    [subvectorC (e offset len)
                (let* ([result1 (eval-env env sto e)]
                       [vec (res-v result1)]
                       [sto1 (res-s result1)]
                       [result2 (eval-env env sto1 offset)]
                       [off (numV-n (res-v result2))]
                       [sto2 (res-s result2)]
                       [result3 (eval-env env sto2 len)]
                       [ln (numV-n (res-v result3))]
                       [sto3 (res-s result3)])
                  ;; Return a subvectorV referencing the original vector with offset and length
                  (res (subvectorV vec off ln) sto3))]
    [transactC (e)
               (let* ([original-sto sto]
                      ;; Capture original values: copy vectors, retain others
                      [original-values (map (lambda (entry)
                                              (copy-vector (cell-val entry)))
                                            sto)]
                      [result (eval-env env sto e)]
                      [p (res-v result)]
                      [new-sto (res-s result)])
                 (if (boolV-b (pairV-v1 p))
                     ;; Transaction successful, retain the new store
                     (res (pairV-v2 p) new-sto)
                     ;; Transaction failed, restore the original store
                     (res (pairV-v2 p) (restore-original-store sto original-values))))]

    [beginC (es)
            (letrec ([loop (lambda (es current-sto last-result)
                             (if (empty? es)
                                 (res last-result current-sto)  ;; Wrap last-result in res with current-sto
                                 (let* ([result (eval-env env current-sto (first es))]
                                        [new-val (res-v result)]
                                        [new-sto (res-s result)])
                                   (loop (rest es) new-sto new-val))))])
              (loop es sto (boolV #f)))]
    ))

;; The main eval-base function
(define (eval-base (e : Expr)) : BaseValue
  (let* ([initial-store empty-store]  ;; Define an initial empty store
         [result (eval-env empty-env initial-store e)])  ;; Call `eval-env` with environment, store, and expression
    (value->basevalue (res-v result) (res-s result))))

(define (list-to-pairbv elements sto)
  (if (empty? elements)
      (boolBV #f)  ; End of list
      (pairBV (value->basevalue (first elements) sto)
              (list-to-pairbv (rest elements) sto))))


;; Function to convert Value to BaseValue for base evaluation
(define (value->basevalue (v : Value) (sto : Store)) : BaseValue
  (type-case Value v
    [numV (n) (numBV n)]
    [boolV (b) (boolBV b)]
    [pairV (v1 v2)
           (pairBV (value->basevalue v1 sto) (value->basevalue v2 sto))]
    [boxV (l)
          (value->basevalue (fetch l sto) sto)]  ; Use `fetch` with location to get the value from the store
    [vectorV (elements)
             (list-to-pairbv (vector->list elements) sto)]  ; Convert vector to list before processing
    [subvectorV (original offset length)
                ;; For a subvector, convert it to a list representation and process as a pair
                (let ([elements (vector->list (vectorV-elements original))])
                  (list-to-pairbv (sublist->left (sublist->right elements offset) length) sto))]
    [closV (env x e)
           (error 'value->basevalue "Cannot convert closure to BaseValue")]))