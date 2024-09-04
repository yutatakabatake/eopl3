#lang eopl

;Stack =  -> SchemeVal

;empty-stack : () -> Stack
(define empty-stack
  (lambda ()
    (lambda (top-var)
      (report-no-binding-found top-var))))


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for -s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: -s" env)))


; (define report-stack-is-empty
;   (lambda (ops)
;     (eopl:error ops "Stack is empty")))

; (define empty-stack
;   (lambda ()
;     (lambda (ops)
;       (if (equal? ops 'empty?) #t
;           (report-stack-is-empty ops)))))

; (define push
;   (lambda (val stack)
;     (lambda (ops)
;       (cond [(equal? ops 'top) val]
;             [(equal? ops 'empty?) #f]
;             [(equal? ops 'pop) stack]))))

; (define top
;   (lambda (stack)
;     (stack 'top)))

; (define pop
;   (lambda (stack)
;     (stack 'pop)))

; (define empty-stack?
;   (lambda (stack)
;     (stack 'empty?)))

; (display
;  (and (equal? (empty-stack? (empty-stack)) #t)
;      (equal? (empty-stack? (push 1 (empty-stack))) #f)
;      (equal? (top (push 1 (empty-stack))) 1)
;      (equal? (empty-stack? (pop (push 1 (empty-stack)))) #t)
;      (equal? (top (push 1 (push 2 (push 3 (empty-stack))))) 1)
;      (equal? (top (pop (push 1 (push 2 (push 3 (empty-stack)))))) 2)))