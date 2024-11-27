#lang plai-typed/untyped
(require rackunit)
(require "ps5-ast.rkt")
(require "ps5.rkt")

(define ex0 '(let x 2
                (let addx (lambda y numT (+ y x))
                  (let x 6
                       (addx 3)))))
(test-equal? "ex0" (tc (parse ex0)) (numT))

(define ex0b '(let x 5 (let y 6 (+ x y))))
(test-equal? "ex0b" (tc (parse ex0b)) (numT))

(define ex0c '(let y #f
                (let add3 (lambda y numT (+ y 3))
                  (let x (add3 3)
                       #t))))
(test-equal? "ex0c" (tc (parse ex0c)) (boolT))

(define ex1 '(lambda x numT (+ 2 x)))
(test-equal? "ex1" (tc (parse ex1)) (funT (numT) (numT)))

(define ex2 '((lambda x numT (+ 2 x)) 1))
(test-equal? "ex2" (tc (parse ex2)) (numT))

(define ex3 '(lambda f (funT numT numT) (f 3)))
(test-equal? "ex3" (tc (parse ex3)) (funT (funT (numT) (numT)) (numT)))

(define ex4 '((lambda f (funT numT numT) (f 3)) (lambda x numT (+ x 3))))
(test-equal? "ex4" (tc (parse ex4)) (numT))

(define ex5 '(if (equal? 1 0) (+ 1 2) (+ 2 3)))
(test-equal? "ex5" (tc (parse ex5)) (numT))

(define ex6 '(rec f x numT numT
                 (if (equal? x 0)
                     1
                     (* x (f (+ x -1))))))
(test-equal? "ex6" (tc (parse ex6)) (funT (numT) (numT)))

(define ex7 '(rec f g (funT numT numT) (funT numT numT)
                 (lambda x numT (if (equal? x 0)
                                    1
                                    ((f g) (g x))))))
(test-equal? "ex7" (tc (parse ex7)) (funT (funT (numT) (numT)) (funT (numT) (numT))))


(define ex8 '(empty boolT)) 
(test-equal? "ex8" (tc (parse ex8)) (listT (boolT)))

(define ex9 '(cons #f (empty boolT)))
(test-equal? "ex9" (tc (parse ex9)) (listT (boolT)))
(define ex9b '(cons 1 (empty boolT)))
(test-exn "ex9b"  (lambda (x) #t) (lambda () (tc (parse ex9b))))

(define ex10 '(cons (cons #f (empty boolT)) (empty (listT boolT))))
(test-equal? "ex10" (tc (parse ex10)) (listT (listT (boolT))))
(define ex10b '(cons (cons #f (empty boolT)) (empty boolT)))
(test-exn "ex10b"  (lambda (x) #t) (lambda () (tc (parse ex10b))))
                                       
(define ex11 '(lambda x (listT boolT) (first x)))
(test-equal? "ex11" (tc (parse ex11)) (funT (listT (boolT)) (boolT)))

(define ex12 '(lambda x (listT boolT) (rest x)))
(test-equal? "ex12" (tc (parse ex12)) (funT (listT (boolT)) (listT (boolT))))

(define ex13 '(lambda x (listT numT) (is-empty? x)))
(test-equal? "ex13" (tc (parse ex13)) (funT (listT (numT)) (boolT)))

(define ex14 '(lambda x (listT numT) (equal? (first x) 0)))
(test-equal? "ex14" (tc (parse ex14)) (funT (listT (numT)) (boolT)))

(define ex15 '(lambda x (listT numT) (+ (first x) (first (rest x)))))
(test-equal? "ex15" (tc (parse ex15)) (funT (listT (numT)) (numT)))

(define ex16 '(lambda x (pairT boolT numT) (pair (snd x) (fst x))))
(test-equal? "ex16" (tc (parse ex16)) (funT (pairT (boolT) (numT)) (pairT (numT) (boolT))))

(define ex17 '((lambda x (pairT boolT numT) (pair (snd x) (fst x))) (pair #f 2)))
(test-equal? "ex17" (tc (parse ex17)) (pairT (numT) (boolT)))

(define ex18 '(lambda x (boxT boolT) (set-box! x #f)))
(test-equal? "ex18" (tc (parse ex18)) (funT (boxT (boolT)) (voidT)))
(define ex18b '(lambda x (boxT boolT) (set-box! x #f)))

(define ex19 '(lambda x (boxT boolT) (unbox x)))
(test-equal? "ex19" (tc (parse ex19)) (funT (boxT (boolT)) (boolT)))

(define ex20  '((lambda x (boxT boolT) (unbox x)) (box #f)))
(test-equal? "ex20" (tc (parse ex20)) (boolT))

(define ex21 '(rec f x (listT numT) (listT boolT)
                 (if (is-empty? x)
                     (empty boolT)
                     (cons (equal? 0 (first x)) (f (rest x))))))
(test-equal? "ex21" (tc (parse ex21)) (funT (listT (numT)) (listT (boolT))))

(define ex21b '(rec f x (listT numT) numT
                 (if (is-empty? x)
                     (empty boolT)
                     (cons (equal? 0 (first x)) (f (rest x))))))
(test-exn "ex21b" (lambda (x) #t) (lambda () (tc (parse ex21b))))

(define ex22 '(rec f x (listT numT) (listT (boxT numT))
                 (if (is-empty? x)
                     (empty (boxT numT))
                     (cons (box (first x)) (f (rest x))))))
(test-equal? "ex22" (tc (parse ex22)) (funT (listT (numT)) (listT (boxT (numT)))))

(define ex23 '(rec f x (listT (boxT numT)) (listT voidT)
                 (if (is-empty? x)
                     (empty voidT)
                     (cons (set-box! (first x) 1) (f (rest x))))))
(test-equal? "ex23" (tc (parse ex23)) (funT (listT (boxT (numT))) (listT (voidT))))
