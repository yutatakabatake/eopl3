#lang eopl

; Exercise 2.8

(define empty-env?
  (lambda (a-env)
    (null? a-env)))