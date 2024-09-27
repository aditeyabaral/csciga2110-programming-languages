#lang racket
(provide make-string)

(define (make-string e)
  (~a e))
