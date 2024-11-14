#lang plai-typed
(require "ps4-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval-base should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;

;; See ps4-ast.rkt and README.md for more information.

;; Note that as in the previous problem set you probably want to implement a version
;; of eval that can return more general values and takes an environment / store as arguments.
;; Your eval-base would then be a wrapper around this more general eval that tries to conver the value
;; to a BaseValue, and fails if it cannot be converted.
;;
;; For grading, the test cases all result in values that can be converted to base values.

(define (parse (s : s-expression)) : Expr
  (error 'parse "Not yet implemented.")
  )

(define (eval-base (e : Expr)) : BaseValue
  (error 'eval-base "Not yet implemented.")
  )


