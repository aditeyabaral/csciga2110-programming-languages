#lang plai-typed

(require "ps2-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;
;; See ps2-ast.rkt and README.md for more information.

(define (parse (s : s-expression)) : Expr
  (error 'parse "Not yet implemented.")
  )

(define (eval (e : Expr)) : Value
  (error 'eval "Not yet implemented.")
  )
