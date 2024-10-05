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

    ;; Default case for variables (identifiers)
    [else (idC (s-exp->symbol s))]
  )
)


;;; (define (eval (e : Expr)) : Value
;;; (type-case Expr e
;;;             [valC (v) v]
;;;             [plusC (e1 e2) (numV (+ (numV->number (eval e1)) (numV->number (eval e2))))]
;;;             [timesC (e1 e2) (numV (* (numV->number (eval e1)) (numV->number (eval e2))))]
;;;             [equal?C (e1 e2) (boolV (equal? (eval e1) (eval e2)))]
;;;             [ifC (guard e1 e2) (if (boolV->boolean (eval guard)) (eval e1) (eval e2))]
;;;             [listC (es) (listV (map eval es))]
;;; )
;;; )   
