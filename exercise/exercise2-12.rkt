#lang eopl

;Stack =  -> SchemeVal

;empty-stack : () -> Stack
(define empty-stack
  (lambda ()
    (lambda (cmd)
      (report-no-binding-found cmd))))

;push : Val × Stack -> Stack
(define push
  (lambda (val stk)
    (lambda (cmd)
      (cond
        ((equal? cmd top)
         val)
        ((equal? cmd pop)
         stk)))))

;pop : Stack -> Stack
(define pop
  (lambda (stk)
    (stk pop)))

;top : Stack -> SchemeVal
(define top
  (lambda (stk)
    (stk top)))

(define report-no-binding-found
  (lambda (cmd)
    (eopl:error 'empty-stack "No binding for -s" cmd)))

(define report-invalid-env
  (lambda (stk)
    (eopl:error 'apply-env "Bad environment: -s" stk)))

(define report-stack-is-empty
  (lambda (ops)
    (eopl:error 'ops "Stack is empty")))

;オブザーバを基準に考えて，引数を一つ受け取って値を返す手続きとして環境のインタフェースを作る