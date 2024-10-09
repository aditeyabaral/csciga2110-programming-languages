#lang plai-typed

; (let ([x e1] [y e2] [z e3]) e) --> ((lambda (x) ((lambda (y) ((lambda (z) e) e1)) e2)) e3)
((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) 2)) 3)) 4) ; 9
((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) 2)) x)) y) ; error

; (let* ([x e1] [y e2] [z e3]) e) --> ((lambda (x) ((lambda (y) ((lambda (z) e) e3)) e2)) e1)
((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) 4)) 3)) 2) ; 9
((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) y)) x)) 2) ; 6

; --------------------------------------------

; (lambda (x y z)
; (z (lambda (x y) (z x)) y))

; (lambda 3
; ((: 0 2) (lambda 2 ((: 1 2) (: 0 0))) (: 0 1)))

; --------------------------------------------

; (lambda 1
; (lambda 1
;   (: 1 0)))

; (lambda (x)
;   (lambda (y)
;     x))