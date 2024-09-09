#lang eopl

;var-exp : Var → Lc-exp
(define var-exp
  (lambda (var)
    var))

;lambda-exp : Var × Lc-exp → Lc-exp
(define lambda-exp
  (lambda (var body)
    (list 'lambda var body)))

;app-exp : Lc-exp × Lc-exp → Lc-exp
(define app-exp
  (lambda (exp1 exp2)
    (list exp1 exp2)))

; var-exp? : Lc-exp → Bool
(define var-exp?
  (lambda (exp)
    (symbol? exp)))

; lambda-exp? : Lc-exp → Bool
(define lambda-exp?
  (lambda (exp)
    (eqv? (car exp) 'lambda)))

; app-exp? : Lc-exp → Bool
(define app-exp?
  (lambda (exp)
    (null? (cddr exp))))

; var-exp->var : Lc-exp → Var
(define var-exp->var
  (lambda (exp)
    exp))

; lambda-exp->bound-var : Lc-exp → Var
(define lambda-exp->bound-var
  (lambda (exp)
    (cadr exp)))

; lambda-exp->body : Lc-exp → Lc-exp
(define lambda-exp->body
  (lambda (exp)
    (caddr exp)))

; app-exp->rator : Lc-exp → Lc-exp
(define app-exp->rator
  (lambda (exp)
    (car exp)))

; app-exp->rand : Lc-exp → Lc-exp
(define app-exp->rand
  (lambda (exp)
    (cadr exp)))