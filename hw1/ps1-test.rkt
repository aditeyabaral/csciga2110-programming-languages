#lang racket
(require rackunit)
(require "ps1.rkt")

;;;;;;;;; Problem 1 ;;;;;;;;;

(define palindrome-string1 "Madam Rotator was a level headed kayak enthusiast. She loved to paddle her kayak, a sleek vessel named Civic. One day, she decided to paddle past the radar station. After a few hours, Madam Rotator decided to retrace her route. As she paddled back, she noticed a peculiar sight: a group of people standing on the shore, staring at her. Curious, she paddled closer. One of the people, a man named Refer, called out to her, 'Madam, your kayak is deified!'")
(define palindrome-string2 "Madam Radar was puzzled. She had never seen a rotator level so high. Civic officials were referring to it as a never before seen phenomenon. The noon sun reflected off the kayak in the civic pond, casting a strange glow. 'It's like a level up,' she muttered.")
(define palindrome-string3 "Mom looked at the noon sun. She had to repaper the wall.")
(define palindrome-string4 "Radar detected the rotator, a civic duty to report.")
(define palindrome-string5 "Eve and Ana were level as they crossed the kayak race finish line.")
(define palindrome-string6 "The nun had a noon prayer that was a deified tenet of her faith.")
(define palindrome-string7 "Bob and Dud were surprised by the level of the flood.")
(define palindrome-string8 "The pup knew the puppeteer was a puppet master.")
(define palindrome-string9 "The gig was a gag, a joke.")
(define palindrome-string10 "His dad had a radar that detected metal.")

(define palindrome-res1
  '("madam" "rotator" "a" "level" "kayak" "kayak" "a" "civic" "radar" "a" "madam" "rotator" "a" "a" "a" "refer" "madam" "kayak" "deified"))
(define palindrome-res2
  '("madam" "radar" "a" "rotator" "level" "civic" "a" "noon" "kayak" "civic" "a" "a" "level"))
(define palindrome-res3
  '("mom" "noon" "repaper"))
(define palindrome-res4
  '("radar" "rotator" "a" "civic"))
(define palindrome-res5
  '("eve" "ana" "level" "kayak"))
(define palindrome-res6
  '("nun" "a" "noon" "a" "deified" "tenet"))
(define palindrome-res7
  '("bob" "dud" "level"))
(define palindrome-res8
  '("pup" "a"))
(define palindrome-res9
  '("gig" "a" "gag" "a"))
(define palindrome-res10
  '("dad" "a" "radar"))

(test-equal? "palindrome-1"  (palindrome-list palindrome-string1) palindrome-res1)
(test-equal? "palindrome-2"  (palindrome-list palindrome-string2) palindrome-res2)
(test-equal? "palindrome-3"  (palindrome-list palindrome-string3) palindrome-res3)
(test-equal? "palindrome-4"  (palindrome-list palindrome-string4) palindrome-res4)
(test-equal? "palindrome-5"  (palindrome-list palindrome-string5) palindrome-res5)
(test-equal? "palindrome-6"  (palindrome-list palindrome-string6) palindrome-res6)
(test-equal? "palindrome-7"  (palindrome-list palindrome-string7) palindrome-res7)
(test-equal? "palindrome-8"  (palindrome-list palindrome-string8) palindrome-res8)
(test-equal? "palindrome-9"  (palindrome-list palindrome-string9) palindrome-res9)
(test-equal? "palindrome-10" (palindrome-list palindrome-string10) palindrome-res10)

;;;;;;;;; Problem 2 ;;;;;;;;;

(define et-t1 (plus-node (int-leaf 1) (int-leaf 2)))
(define et-t2 (times-node (int-leaf 2) et-t1))
(define et-t3 (times-node et-t2 et-t2))
(define et-t4 (plus-node (int-leaf 10) et-t2))
(define et-t5 (times-node et-t4 et-t1))
(define et-t6 (times-node (int-leaf 0) et-t5))
(define et-t7 (plus-node et-t4 et-t5))
(define et-t8 (plus-node et-t2 et-t3))
(define et-t9 (times-node (times-node (int-leaf 5) (int-leaf 5)) et-t2))
(define et-t10 (plus-node et-t9 et-t8))

(test-equal? "et-1"  (eval-tree et-t1) 3)
(test-equal? "et-2"  (eval-tree et-t2) 6)
(test-equal? "et-3"  (eval-tree et-t3) 36)
(test-equal? "et-4"  (eval-tree et-t4) 16)
(test-equal? "et-5"  (eval-tree et-t5) 48)
(test-equal? "et-6"  (eval-tree et-t6) 0)
(test-equal? "et-7"  (eval-tree et-t7) 64)
(test-equal? "et-8"  (eval-tree et-t8) 42)
(test-equal? "et-9"  (eval-tree et-t9) 150)
(test-equal? "et-10" (eval-tree et-t10) 192)

; ;;;;;;;;; Problem 3 ;;;;;;;;;

(define bt-t1 (bt-node 5 (bt-leaf 1) (bt-leaf 6)))
(define bt-t2 (bt-node 7 bt-t1 (bt-leaf 6)))
(define bt-t3 (bt-node 2 bt-t1 (bt-leaf 1)))
(define bt-t4 (bt-node 8 bt-t1 (bt-empty)))
(define bt-t5 (bt-empty))
(define bt-t6 (bt-leaf 1))
(define bt-t7 (bt-node 10 (bt-node 5 (bt-leaf 1) (bt-leaf 7)) (bt-leaf 12)))
(define bt-t8 (bt-node 10 (bt-node 5 (bt-leaf 1) (bt-leaf 11)) (bt-leaf 12)))
(define bt-t9 (bt-node 1 (bt-leaf 1) (bt-leaf 2)))
(define bt-t10 (bt-node 100 bt-t7 (bt-leaf 110)))

(test-equal? "bt-t1" (check-bt bt-t1) #t)
(test-equal? "bt-t2" (check-bt bt-t2) #f)
(test-equal? "bt-t3" (check-bt bt-t3) #f)
(test-equal? "bt-t4" (check-bt bt-t4) #t)
(test-equal? "bt-t5" (check-bt bt-t5) #t)
(test-equal? "bt-t6" (check-bt bt-t6) #t)
(test-equal? "bt-t7" (check-bt bt-t7) #t)
(test-equal? "bt-t8" (check-bt bt-t8) #f)
(test-equal? "bt-t9" (check-bt bt-t9) #f)
(test-equal? "bt-t10" (check-bt bt-t10) #t)

; ;;;;;;;;; Problem 4 ;;;;;;;;;;;;

; (define ml-1 (list 1 2 3 4 2 3 4 3 2 1))
; (define ml-2 (list 1 2 3 4 5))
; (define ml-3 (list 9 8 6 7 2 1))
; (define ml-4 (list 1 1 1 2 2 2 3 3 1  4))
; (define ml-5 (list 1 1 5 5 6))
; (define ml-6 (list 1 2 3 2 1))
; (define ml-7 (list 9 8 7 6 1 2 3 2 1))
; (define ml-8 (list 1 2 1 2 1 2 1 2 1))
; (define ml-9 (list 1 2 3 2 1 2 3 2 1))
; (define ml-10 (list 4 5 6 4 5 6 1 2))

; (test-equal? "ml-1" (ml-split ml-1) '((1 2 3 4) (2 3 4) (3 2 1)))
; (test-equal? "ml-2" (ml-split ml-2) '((1 2 3 4 5)))
; (test-equal? "ml-3" (ml-split ml-3) '((9 8 6) (7 2 1)))
; (test-equal? "ml-4" (ml-split ml-4) '((1) (1) (1 2) (2) (2 3) (3 1) (4)))
; (test-equal? "ml-5" (ml-split ml-5) '((1) (1 5) (5 6)))
; (test-equal? "ml-6" (ml-split ml-6) '((1 2 3) (2 1)))
; (test-equal? "ml-7" (ml-split ml-7) '((9 8 7 6 1) (2 3) (2 1)))
; (test-equal? "ml-8" (ml-split ml-8) '((1 2) (1 2) (1 2) (1 2) (1)))
; (test-equal? "ml-9" (ml-split ml-9) '((1 2 3) (2 1) (2 3) (2 1)))
; (test-equal? "ml-10" (ml-split ml-10) '((4 5 6) (4 5 6) (1 2)))

; ;;;;;;;;; Problem 5 ;;;;;;;;;;;;

; (test-equal? "pi-t1" (piles-insert '((3)) 4) '((3) (4)))
; (test-equal? "pi-t2" (piles-insert '() 3) '((3)))
; (test-equal? "pi-t3" (piles-insert '((4) (5)) 3) '((3 4) (5)))
; (test-equal? "pi-t4" (piles-insert '((2) (6)) 4) '((2) (4 6)))
; (test-equal? "pi-t5" (piles-insert '((2) (6) (10)) 8) '((2) (6) (8 10)))
; (test-equal? "pi-t6" (piles-insert '((2) (3 6) (10)) 3) '((2) (3 3 6) (10)))
; (test-equal? "pi-t7" (piles-insert '((2) (3) (4) (5) (6)) 4) '((2) (3) (4 4) (5) (6)))
; (test-equal? "pi-t8" (piles-insert '((2) (6) (10)) 12) '((2) (6) (10) (12)))
; (test-equal? "pi-t9" (piles-insert '((2) (3) (10)) 3) '((2) (3 3) (10)))
; (test-equal? "pi-10" (piles-insert '((1) (2) (3)) 0) '((0 1) (2) (3)))
