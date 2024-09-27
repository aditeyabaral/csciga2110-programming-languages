#lang plai-typed/untyped
(require rackunit)
(require "ps2-ast.rkt")
(require "ps2.rkt")
(require "ps2-test-util.rkt")

(define test-examples
  (list
    '(+ 27 (let [(x 5)] (+ x x)))
    '(let [(x 5)] (let [(y 6)] (+ x y)))
    '(let [(x 5)] (let [(x 6)] (+ x x)))
    '(let [(x 5)] (let [(x (* x 2))] (+ x x)))
    '(let [(x 5)] (let [(x (* x 2)) (y x)] (+ x y)))
    '(let [(x 5)] (let* [(x (* x 2)) (y x)] (+ x y)))
    '(list (+ 1 1) (+ 2 2) (+ 3 3) 4)
    '(list (+ 1 1) (+ 2 2) (+ 3 3) (list (* 1 1) (* 2 2) (* 3 3)))
    '(cons (+ 0 1) (list (+ 1 1) (+ 2 2) (+ 3 3) 4))
    '(equal? (list 2 4 6) (list (+ 1 1) (+ 2 2) (+ 3 3)))
    '(if (equal? 1 1) (+ 1 1) (+ 3 6))
    '(if (equal? 1 2) (+ 1 1) (+ 3 6))
    '(if (equal? (list 1) (list 1)) (+ 1 1) (+ 3 6))
    '(if (equal? (list 1) (list)) (+ 1 1) (+ 3 6))                             
    '(natrec 5 0 (x y (+ y 2)))
    '(natrec 5 0 (x y x))
    '(natrec 5 7 (x y (+ 1 y)))
    '(natrec 5 7 (x y (+ y -1)))
    '(natrec 4 #t (x y (if y #f #t)))
    '(natrec 5 #t (x y (if y #f #t)))
    '(first (list 5 4 3 2 1))
    '(rest (list 5 4 3 2 1))
    '(natrec 6 (list) (x y (cons x y)))
    '(listrec (list 1 2 3 4 5) 0 (hd tl res (+ hd res)))
    '(listrec (list 1 2 3 4 5) 1 (hd tl res (* hd res)))
    '(listrec (list 1 2 3 4 5) 0 (hd tl res (+ 1 res)))
    '(listrec (list 1 2 3 4 5 6 7 8 9 10 11 12 13)
              (list)
              (hd tl res (if (natrec hd #f (x y (if y #f #t)))
                             (cons hd res)
                             res)))
    '(let* [(n 9)
            (ns (natrec n (list) (x y (cons (+ n (* -1 x)) y))))]
       (listrec ns 0 (hd tl res (+ (* hd hd) res))))
    '(let* [(ns (natrec 15 (list) (x res (cons (list x (+ 15 (* -1 x))) res))))]
       (listrec ns 0 (hd tl res (let [(hdsum (+ (first hd) (first (rest hd))))]
                                  (+ hdsum res)))))
    '(unpack (x y z) (list 1 2 3) (+ x (+ y z)))
    '(unpack (x y z) (list 1 10 100) (unpack (x y) (list x x) (+ x (+ y z))))
    '(unpack (x y z) (list 1 10 100) (let* [(x y) (y x) (z y)] (+ x (+ y z))))
    '(listrec (natrec 4 (list) (x rec (cons (list x (* 2 x)) rec)))
              0
              (hd tl rec (unpack (x1 x2) hd (+ (+ x1 x2) rec))))
    )
  )


(define test-asts
(list
 (plusC (valC (numV 27)) (letC (list (pair 'x (valC (numV 5)))) (plusC (idC 'x) (idC 'x))))
 (letC (list (pair 'x (valC (numV 5)))) (letC (list (pair 'y (valC (numV 6)))) (plusC (idC 'x) (idC 'y))))
 (letC (list (pair 'x (valC (numV 5)))) (letC (list (pair 'x (valC (numV 6)))) (plusC (idC 'x) (idC 'x))))
 (letC
  (list (pair 'x (valC (numV 5))))
  (letC (list (pair 'x (timesC (idC 'x) (valC (numV 2))))) (plusC (idC 'x) (idC 'x))))
 (letC
  (list (pair 'x (valC (numV 5))))
  (letC (list (pair 'x (timesC (idC 'x) (valC (numV 2)))) (pair 'y (idC 'x))) (plusC (idC 'x) (idC 'y))))
 (letC
  (list (pair 'x (valC (numV 5))))
  (let*C (list (pair 'x (timesC (idC 'x) (valC (numV 2)))) (pair 'y (idC 'x))) (plusC (idC 'x) (idC 'y))))
 (listC
  (list
   (plusC (valC (numV 1)) (valC (numV 1)))
   (plusC (valC (numV 2)) (valC (numV 2)))
   (plusC (valC (numV 3)) (valC (numV 3)))
   (valC (numV 4))))
 (listC
  (list
   (plusC (valC (numV 1)) (valC (numV 1)))
   (plusC (valC (numV 2)) (valC (numV 2)))
   (plusC (valC (numV 3)) (valC (numV 3)))
   (listC
    (list
     (timesC (valC (numV 1)) (valC (numV 1)))
     (timesC (valC (numV 2)) (valC (numV 2)))
     (timesC (valC (numV 3)) (valC (numV 3)))))))
 (consC
  (plusC (valC (numV 0)) (valC (numV 1)))
  (listC
   (list
    (plusC (valC (numV 1)) (valC (numV 1)))
    (plusC (valC (numV 2)) (valC (numV 2)))
    (plusC (valC (numV 3)) (valC (numV 3)))
    (valC (numV 4)))))
 (equal?C
  (listC (list (valC (numV 2)) (valC (numV 4)) (valC (numV 6))))
  (listC
   (list
    (plusC (valC (numV 1)) (valC (numV 1)))
    (plusC (valC (numV 2)) (valC (numV 2)))
    (plusC (valC (numV 3)) (valC (numV 3))))))
 (ifC
  (equal?C (valC (numV 1)) (valC (numV 1)))
  (plusC (valC (numV 1)) (valC (numV 1)))
  (plusC (valC (numV 3)) (valC (numV 6))))
 (ifC
  (equal?C (valC (numV 1)) (valC (numV 2)))
  (plusC (valC (numV 1)) (valC (numV 1)))
  (plusC (valC (numV 3)) (valC (numV 6))))
 (ifC
  (equal?C (listC (list (valC (numV 1)))) (listC (list (valC (numV 1)))))
  (plusC (valC (numV 1)) (valC (numV 1)))
  (plusC (valC (numV 3)) (valC (numV 6))))
 (ifC
  (equal?C (listC (list (valC (numV 1)))) (listC (list )))
  (plusC (valC (numV 1)) (valC (numV 1)))
  (plusC (valC (numV 3)) (valC (numV 6))))
 (natrecC (valC (numV 5)) (valC (numV 0)) 'x 'y (plusC (idC 'y) (valC (numV 2))))
 (natrecC (valC (numV 5)) (valC (numV 0)) 'x 'y (idC 'x))
 (natrecC (valC (numV 5)) (valC (numV 7)) 'x 'y (plusC (valC (numV 1)) (idC 'y)))
 (natrecC (valC (numV 5)) (valC (numV 7)) 'x 'y (plusC (idC 'y) (valC (numV -1))))
 (natrecC (valC (numV 4)) (valC (boolV #t)) 'x 'y (ifC (idC 'y) (valC (boolV #f)) (valC (boolV #t))))
 (natrecC (valC (numV 5)) (valC (boolV #t)) 'x 'y (ifC (idC 'y) (valC (boolV #f)) (valC (boolV #t))))
 (firstC (listC (list (valC (numV 5)) (valC (numV 4)) (valC (numV 3)) (valC (numV 2)) (valC (numV 1)))))
 (restC (listC (list (valC (numV 5)) (valC (numV 4)) (valC (numV 3)) (valC (numV 2)) (valC (numV 1)))))
 (natrecC (valC (numV 6)) (listC (list )) 'x 'y (consC (idC 'x) (idC 'y)))
 (listrecC
  (listC (list (valC (numV 1)) (valC (numV 2)) (valC (numV 3)) (valC (numV 4)) (valC (numV 5))))
  (valC (numV 0))
  'hd
  'tl
  'res
  (plusC (idC 'hd) (idC 'res)))
 (listrecC
  (listC (list (valC (numV 1)) (valC (numV 2)) (valC (numV 3)) (valC (numV 4)) (valC (numV 5))))
  (valC (numV 1))
  'hd
  'tl
  'res
  (timesC (idC 'hd) (idC 'res)))
 (listrecC
  (listC (list (valC (numV 1)) (valC (numV 2)) (valC (numV 3)) (valC (numV 4)) (valC (numV 5))))
  (valC (numV 0))
  'hd
  'tl
  'res
  (plusC (valC (numV 1)) (idC 'res)))
 (listrecC
  (listC
   (list
    (valC (numV 1))
    (valC (numV 2))
    (valC (numV 3))
    (valC (numV 4))
    (valC (numV 5))
    (valC (numV 6))
    (valC (numV 7))
    (valC (numV 8))
    (valC (numV 9))
    (valC (numV 10))
    (valC (numV 11))
    (valC (numV 12))
    (valC (numV 13))))
  (listC (list))
  'hd
  'tl
  'res
  (ifC
   (natrecC (idC 'hd) (valC (boolV #f)) 'x 'y (ifC (idC 'y) (valC (boolV #f)) (valC (boolV #t))))
   (consC (idC 'hd) (idC 'res))
   (idC 'res)))
 (let*C
  (list
   (pair 'n (valC (numV 9)))
   (pair
    'ns
    (natrecC (idC 'n) (listC (list)) 'x 'y (consC (plusC (idC 'n) (timesC (valC (numV -1)) (idC 'x))) (idC 'y)))))
  (listrecC (idC 'ns) (valC (numV 0)) 'hd 'tl 'res (plusC (timesC (idC 'hd) (idC 'hd)) (idC 'res))))
 (let*C
  (list
   (pair
    'ns
    (natrecC
     (valC (numV 15))
     (listC (list))
     'x
     'res
     (consC (listC (list (idC 'x) (plusC (valC (numV 15)) (timesC (valC (numV -1)) (idC 'x))))) (idC 'res)))))
  (listrecC
   (idC 'ns)
   (valC (numV 0))
   'hd
   'tl
   'res
   (letC
    (list (pair 'hdsum (plusC (firstC (idC 'hd)) (firstC (restC (idC 'hd))))))
    (plusC (idC 'hdsum) (idC 'res)))))
 (unpackC
  (list 'x 'y 'z)
  (listC (list (valC (numV 1)) (valC (numV 2)) (valC (numV 3))))
  (plusC (idC 'x) (plusC (idC 'y) (idC 'z))))
 (unpackC
  (list 'x 'y 'z)
  (listC (list (valC (numV 1)) (valC (numV 10)) (valC (numV 100))))
  (unpackC (list 'x 'y) (listC (list (idC 'x) (idC 'x))) (plusC (idC 'x) (plusC (idC 'y) (idC 'z)))))
 (unpackC
  (list 'x 'y 'z)
  (listC (list (valC (numV 1)) (valC (numV 10)) (valC (numV 100))))
  (let*C
   (list (pair 'x (idC 'y)) (pair 'y (idC 'x)) (pair 'z (idC 'y)))
   (plusC (idC 'x) (plusC (idC 'y) (idC 'z)))))
 (listrecC
  (natrecC
   (valC (numV 4))
   (listC (list))
   'x
   'rec
   (consC (listC (list (idC 'x) (timesC (valC (numV 2)) (idC 'x)))) (idC 'rec)))
  (valC (numV 0))
  'hd
  'tl
  'rec
  (unpackC (list 'x1 'x2) (idC 'hd) (plusC (plusC (idC 'x1) (idC 'x2)) (idC 'rec))))
 )
)


(define test-results
  (list
   (numV 37)
   (numV 11)
   (numV 12)
   (numV 20)
   (numV 15)
   (numV 20)
   (listV (list (numV 2) (numV 4) (numV 6) (numV 4)))
   (listV (list (numV 2) (numV 4) (numV 6) (listV (list (numV 1) (numV 4) (numV 9)))))
   (listV (list (numV 1) (numV 2) (numV 4) (numV 6) (numV 4)))
   (boolV #t)
   (numV 2)
   (numV 9)
   (numV 2)
   (numV 9)
   (numV 10)
   (numV 4)
   (numV 12)
   (numV 2)
   (boolV #t)
   (boolV #f)
   (numV 5)
   (listV (list (numV 4) (numV 3) (numV 2) (numV 1)))
   (listV (list (numV 5) (numV 4) (numV 3) (numV 2) (numV 1) (numV 0)))
   (numV 15)
   (numV 120)
   (numV 5)
   (listV (list (numV 1) (numV 3) (numV 5) (numV 7) (numV 9) (numV 11) (numV 13)))
   (numV 285)
   (numV 225)
   (numV 6)
   (numV 102)
   (numV 30)
   (numV 18))
  )

(define (parse-test-case-name input)
  (string-append "Testing parse on input: " (make-string input)))

(define (eval-test-case-name input)
  (string-append "Testing eval on reference AST generated from: " (make-string (fst input))))

(define parsing-test-suite
  (make-test-suite "Parsing Tests"
                   (map2 (lambda (input expected)
                           (test-equal? (parse-test-case-name input) (parse input) expected))
                         test-examples
                         test-asts))
  )

(define eval-test-suite
  (make-test-suite "Evaluation Tests"
                   (map2 (lambda (input expected) (test-equal? (eval-test-case-name input) (eval (snd input))
                                                               expected))
                         (map2 (lambda (x y) (pair x y)) test-examples test-asts)
                         test-results))
  )

