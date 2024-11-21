#lang racket

(define counter 0)

(define (make-incrementing-object)
  (set! counter (+ counter 1))
  (lambda (m)
    (case m
      [(get-counter) (lambda (self) counter)]
      [(identity) (lambda (self x) x)])))

;; Function implementation
(define (msg/self-func o m . a)
  (apply (o m) o a))

;; Macro implementation
(define-syntax (msg/self-macro stx)
  (syntax-case stx ()
    [(msg/self-macro o m a ...)
     #'((o m) o a ...)]))

;; Using function implementation
(display "Function implementation:\n")
(display (msg/self-func (make-incrementing-object) 'get-counter)) ; 1
(newline)
(display counter) ; 1
(newline)

;; Reset counter
(set! counter 0)

;; Using macro implementation
(display "Macro implementation:\n")
(display (msg/self-macro (make-incrementing-object) 'get-counter)) ; 2
(newline)
(display counter) ; 2
(newline)