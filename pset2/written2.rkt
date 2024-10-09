#lang plai-typed


; let -> ((lambda (z) ((lambda (y) ((lambda (x) e) e1)) e2)) e3)

((lambda (z) ((lambda (y) ((lambda (x) (+ x (+ y z))) 2)) 3)) 4) ; x = 2, y = 3, z = 4 -> 9
; ((lambda (z) ((lambda (y) ((lambda (x) (+ x (+ y z))) 2)) x)) y) ; x = 2, y = x, z = y -> error

; let* -> ((lambda (x) ((lambda (y) ((lambda (z) e) e3)) e2)) e1)

((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) 4)) 3)) 2) ; x = 2, y = 3, z = 4 -> 9
((lambda (x) ((lambda (y) ((lambda (z) (+ x (+ y z))) y)) x)) 2) ; x = 2, y = x, z = y -> 6