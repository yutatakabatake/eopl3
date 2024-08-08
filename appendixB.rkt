#lang eopl

(define-datatype statement statement? 
  (compound-statement
  (stmt1 statement?)
    (stmt2 statement?))
  (while-statement
    (test expression?)
    (body statement?))
  (assign-statement
    (lhs symbol?)
    (rhs expression?)))

(define-datatype expression expression? 
  (var-exp
    (var symbol?))
  (diff-exp
    (exp1 expression?)
    (exp2 expression?)))

;正規表現　lexerに与える
(define scanner-spec-a
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

;文法　parserジェネレータに与える
(define grammar-a1
  '((statement
      ("{" statement ";" statement "}")
      compound-statement)
    (statement
      ("while" expression "do" statement)
      while-statement)
    (statement
      (identifier ":=" expression)
      assign-statement)
    (expression
      (identifier)
      var-exp)
    (expression
      ("(" expression "-" expression ")")
      diff-exp)))


(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-a grammar-a1)))

(define just-scan
  (sllgen:make-string-scanner scanner-spec-a grammar-a1))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-a grammar-a1))

(define read-eval-print
  (sllgen:make-rep-loop "--> " "{x := foo; while x do x := (x - bar)}"
    (sllgen:make-stream-parser scanner-spec-a grammar-a1)))

;(scan&parse "{x := foo; while x do x := (x - bar)}")
