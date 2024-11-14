#lang plai-typed/untyped
(require rackunit)
(require "ps4-ast.rkt")
(require "ps4.rkt")


(define ex0
  '(let o (object () ([get (self) 1]))
     (msg o get)))
(test-equal? "ex0" (eval-base (parse ex0)) (numBV 1))

(define ex1
  '(let o (object () ([plus (self x y) (+ x y)]))
     (msg o plus 10 5)))
(test-equal? "ex1" (eval-base (parse ex1)) (numBV 15))

(define ex2
  '(let o (object () ([plus (self x y) (+ x y)]
                      [minus (self x y) (+ x (* y -1))]))
     (msg o minus (msg o plus 10 5) 8)))
(test-equal? "ex2" (eval-base (parse ex2)) (numBV 7))

(define ex3
  '(let o (object () ([plus (self a b c d e f g h) (+ a (+ b (+ c (+ d (+ e (+ f (+ g h)))))))]))
     (msg o plus 1 2 3 4 5 6 7 8)))
(test-equal? "ex3" (eval-base (parse ex3)) (numBV 36))

(define ex4
  '(let o (object () ([get1 (self) 1]
                      [get2 (self) 2]
                      [combine (self) (+ (msg self get1) (msg self get2))]))
     (msg o combine)))
(test-equal? "ex4" (eval-base (parse ex4)) (numBV 3))

(define ex5
  '(let o (object ([x1 1] [x2 0])
                  ([setf (self v) (set-field! x1 v)]
                   [getf (self) (get-field x1)]))
     (begin (msg o setf 10)
            (msg o getf))))
(test-equal? "ex5" (eval-base (parse ex5)) (numBV 10))

(define ex6
  '(let myfun (lambda init
                (object ([x init])
                  ([setf (self v) (set-field! x v)]
                   [getf (self) (get-field x)])))
     (let o1 (myfun 10)
       (let o2 (myfun 11)
         (+ (msg o1 getf) (msg o2 getf))))))
(test-equal? "ex6" (eval-base (parse ex6)) (numBV 21))

(define ex7
  '(let o (object ([x 0])
                  ([incr (self) (set-field! x (+ 1 (get-field x)))]
                   [decr (self) (set-field! x (+ -1 (get-field x)))]
                   [get  (self) (get-field x)]))
     (begin (msg o incr)
            (msg o decr)
            (msg o incr)
            (msg o incr)
            (msg o get))))
(test-equal? "ex7" (eval-base (parse ex7)) (numBV 2))

(define ex8
  '(let parent
       (object () ([test1 (self) 1]))
     (let child
         (object-del parent () ([test2 (self) 5]))
       (+ (msg child test1) (msg child test2)))))
(test-equal? "ex8" (eval-base (parse ex8)) (numBV 6))

(define ex9
  '(let adder
       (object () ([val1 (self) 1]
                   [val2 (self) 2]
                   [add (self) (+ (msg self val1) (msg self val2))]))
     (let adder2
         (object-del adder () ([val1 (self) 10]))
       (msg adder2 add))))

(test-equal? "ex9" (eval-base (parse ex9)) (numBV 12))

(define ex10a
  '(let toggle
       (object ([status #f])
               ([switch (self) (set-field! status (if (get-field status) #f #t))]
                [get (self) (get-field status)]))
        (begin (msg toggle switch)
               (msg toggle switch)
               (msg toggle switch)
               (if (msg toggle get) 12 11))))
(test-equal? "ex10a" (eval-base (parse ex10a)) (numBV 12))

(define ex10b
  '(let mytrue
       (object () ([ifThen (self t f) t]))
    (let myfalse
        (object () ([ifThen (self t f) f]))
      (let toggle
          (object ([status myfalse])
                  ([switch (self) (set-field! status (msg (get-field status) ifThen myfalse mytrue))]
                   [get (self) (get-field status)]))
        (begin (msg toggle switch)
               (msg toggle switch)
               (msg toggle switch)
               (msg (msg toggle get) ifThen 2 1))))))
(test-equal? "ex10b" (eval-base (parse ex10b)) (numBV 2))

(define ex11
  '(let mk1Dpoint
       (lambda initx
         (object ([x initx])
                 ([set-x (self v) (set-field! x v)]
                  [get-x (self) (get-field x)]
                  )))
     (let mk2Dpoint
         (lambda initx
           (lambda inity
             (object-del (mk1Dpoint initx) ([y inity])
                     ([set-y (self v) (set-field! y v)]
                      [get-y (self) (get-field y)]))))
       (let p ((mk2Dpoint 1) 2)
         (begin (msg p set-x 127)
                (+ (msg p get-x) (msg p get-y)))))))

(test-equal? "ex11" (eval-base (parse ex11)) (numBV 129))


(define ex12
  '(let mkLeaf
       (lambda v
         (object () ([sum (self) v])))
     (let mkNode
         (lambda t1
           (lambda t2
             (object () ([sum (self) (+ (msg t1 sum) (msg t2 sum))]))))
       (let t1
           ((mkNode (mkLeaf 1)) (mkLeaf 2))
         (let t2
             ((mkNode (mkLeaf 10)) (mkLeaf 20))
           (let t
               ((mkNode t1) t2)
             (msg t sum)))))))
(test-equal? "ex12" (eval-base (parse ex12)) (numBV 33))

(define ex13
  '(let mkLeaf
       (lambda v
         (object ([val v]) ([sum (self) (get-field val v)]
                            [incr (self) (set-field! val (+ 1 (get-field val)))]
                            )))
     (let mkNode
         (lambda t1
           (lambda t2
             (object () ([sum (self) (+ (msg t1 sum) (msg t2 sum))]
                         [incr (self) (begin (msg t1 incr) (msg t2 incr))]
                         ))))
       (let t1
           ((mkNode (mkLeaf 1)) (mkLeaf 2))
         (let t2
             ((mkNode (mkLeaf 10)) (mkLeaf 20))
           (let t
               ((mkNode t1) t2)
             (begin (msg t incr)
                    (msg t incr)
                    (msg t sum))))))))
(test-equal? "ex13" (eval-base (parse ex13)) (numBV 41))

(define ex14
  '(let objectMaker
       (object ([numObj 1])
               ([mkObj (self)
                       (let count (get-field numObj)
                         (let o (object () ([getVal (self) count]))
                           (begin (set-field! numObj (+ 1 count))
                                  o)))]))
     (let o1 (msg objectMaker mkObj)
       (let o2 (msg objectMaker mkObj)
         (let o3 (msg objectMaker mkObj)
           (+ (msg o2 getVal) (msg o3 getVal)))))))
(test-equal? "ex14" (eval-base (parse ex14)) (numBV 5))

(define ex15
  '(let o
       (object ([f (lambda x x)])
               ([setf (self v) (set-field! f v)]
                [do1 (self v) ((get-field f) v)]
                [do2 (self v) ((get-field f) ((get-field f) v))]))
     (begin (msg o setf (lambda x (+ 1 x)))
            (+ (msg o do1 5) (msg o do2 10)))))
                
(test-equal? "ex15" (eval-base (parse ex15)) (numBV 18))

(define ex16
  '(let o
       (object ()
               ([doN (self f n v)
                     (if (equal? n 0)
                         v
                         (msg self doN f (+ -1 n) (f v)))]))
     (msg o doN (lambda x (* 2 x)) 4 1)))
                
(test-equal? "ex16" (eval-base (parse ex16)) (numBV 16))
