#lang plai-typed/untyped
(require rackunit)
(require "ps3-ast.rkt")
(require "ps3.rkt")

; Note that not all of these tests are actually used in grading, but you probably
; want to use them anyway while testing your solution.

(define ex0 '(let v (+ 1 1) (+ v v)))
(test-equal? "ex0" (eval-base (parse ex0)) (numBV 4))

(define ex1 '(begin (+ 1 1) (+ 2 2)))
(test-equal? "ex1" (eval-base (parse ex1)) (numBV 4))

(define ex2 '(let b (box 0) (set-box! b 1)))
(test-equal? "ex2" (eval-base (parse ex2)) (numBV 1))


(define ex3 '(let b (box 0) (unbox b)))
(test-equal? "ex3" (eval-base (parse ex3)) (numBV 0))


(define ex4 '(let b (box 0) (begin (begin (set-box! b 1)
                                          (set-box! b (+ 1 (unbox b))))
                                   (unbox b))))
(test-equal? "ex4" (eval-base (parse ex4)) (numBV 2))


(define ex5
  '(let a (box 1)
     (let f (lambda x (+ x (unbox a)))
       (begin
         (set-box! a 2)
         (f 10)))))
(test-equal? "ex5" (eval-base (parse ex5)) (numBV 12))

(define ex6
  '(let v (vector 1 2 3)
     (begin (vector-set! v 0 11)
            (vector-set! v 1 12)
            (vector-set! v 2 13)
            (vector-ref v 1))))
(test-equal? "ex6" (eval-base (parse ex6)) (numBV 12))

(define ex7
  '(let v (vector 1 2 3)
     (let x
       (transact
        (begin (vector-set! v 0 11)
               (vector-set! v 1 12)
               (vector-set! v 2 13)
               (pair #false (vector-ref v 1))))
       (pair x (vector-ref v 1)))
     ))
(test-equal? "ex7" (eval-base (parse ex7)) (pairBV (numBV 12) (numBV 2)))

(define ex7b
  '(let v (vector 1 2 3)
     (let x
       (transact
        (begin (vector-set! v 0 11)
               (vector-set! v 1 12)
               (vector-set! v 2 13)
               (pair #true (vector-ref v 1))))
       (pair x (vector-ref v 1)))
     ))
(test-equal? "ex7b" (eval-base (parse ex7b)) (pairBV (numBV 12) (numBV 12)))

(define ex8
  '(let b (box 1) (pair (begin (set-box! b 2) 3) (unbox b))))
(test-equal? "ex8" (eval-base (parse ex8)) (pairBV (numBV 3) (numBV 2)))

(define ex8a
  '(let b (box 1) (fst (pair (begin (set-box! b 2) 3) (unbox b)))))
(test-equal? "ex8a" (eval-base (parse ex8a)) (numBV 3))

(define ex8b
  '(let b (box 1) (snd (pair (begin (set-box! b 2) 3) (unbox b)))))
(test-equal? "ex8b" (eval-base (parse ex8b)) (numBV 2))

(define ex9a
  '(vector-length (vector 1 2 3 4 5)))
(test-equal? "ex9a" (eval-base (parse ex9a)) (numBV 5))

(define ex11
  '(let v (vector (box 1) (box 2) (box 3) (box 4) (box 5))
     (unbox (vector-ref v 4))))
(test-equal? "ex11" (eval-base (parse ex11)) (numBV 5))

(define ex12
  '(let v (vector-make 5 1) (vector-ref v 3)))
(test-equal? "ex12" (eval-base (parse ex12)) (numBV 1))

(define ex12b
  '(let v (vector-make 5 (box 2)) (begin (set-box! (vector-ref v 3) 10)
                                         (unbox (vector-ref v 0))
                                         )))
(test-equal? "ex12b" (eval-base (parse ex12b)) (numBV 10))

(define ex13
  '(let v (vector 1 2 3 4 5)
     (let v2 (subvector v 2 1)
       (vector-ref v2 0))))
(test-equal? "ex13" (eval-base (parse ex13)) (numBV 3))

(define ex14
  '(let v (vector 1 2 3 4 5)
     (let v2 (subvector v 2 2)
       (begin (vector-set! v2 1 10)
              (vector-ref v 3)))))
(test-equal? "ex14" (eval-base (parse ex14)) (numBV 10))

(define ex14b
  '(let v (vector 1 2 3 4 5)
     (let v2 (subvector v 2 2)
       (begin (vector-set! v2 1 10)
              (vector-ref v 2)))))
(test-equal? "ex14b" (eval-base (parse ex14b)) (numBV 3))

(define ex15
  '(let v (vector 1 2 3 4 5)
     (let v2 (subvector v 2 2)
       (vector-length v2))))
(test-equal? "ex15" (eval-base (parse ex15)) (numBV 2))

(define ex16
  '(let fact (vector -1)
     (let fact-fun
       (lambda n
         (if (equal? 0 n)
             1
             (* n ((vector-ref fact 0) (+ n -1)))))
       (begin
         (vector-set! fact 0 fact-fun)
         ((vector-ref fact 0) 5)))))
(test-equal? "ex16" (eval-base (parse ex16)) (numBV 120))

(define ex17
  '(let sumvec (box -1)
     (let fun
       (lambda vt
         (lambda n
           (if (equal? n (vector-length vt))
               0
               (+ (vector-ref vt n) (((unbox sumvec) vt) (+ n 1))))))
       (begin
         (set-box! sumvec fun)
         (((unbox sumvec) (vector 1 2 3 4 5)) 0)))))
(test-equal? "ex17" (eval-base (parse ex17)) (numBV 15))

(define ex18
  '(let doublevec (box -1)
     (let fun
       (lambda vt
         (lambda n
           (if (equal? n (vector-length vt))
               0
               (let x (vector-ref vt n)
                 (begin (vector-set! vt n (* 2 x))
                        (((unbox doublevec) vt) (+ n 1)))))))
       (let myvec (vector 1 2 3 4 5)
         (let myvec2 (subvector myvec 1 3)
           (begin
             (set-box! doublevec fun)
             (((unbox doublevec) myvec2) 0)
             (pair (pair (vector-ref myvec 0) (vector-ref myvec 2)) (vector-ref myvec 4))
             ))))))
(test-equal? "ex18" (eval-base (parse ex18)) (pairBV (pairBV (numBV 1) (numBV 6)) (numBV 5)))
