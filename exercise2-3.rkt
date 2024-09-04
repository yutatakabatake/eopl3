#lang eopl

;Diff-tree = (one) | (diff Diff-tree Diff-tree)

;zero,is-zero?, successor, and predecessor

(define one
  (lambda ()
    '(one)))

(define diff
  (lambda (n1 n2)
    (list 'diff n1 n2)))

(define zero
  (lambda ()
    (diff (one) (one))))

(define is-zero?
  (lambda (diff-tree)
    (equal? (zero) diff-tree)))

; (define successor
;   (lambda (diff-tree)
;     (cond
;       ((is-zero? diff-tree)
;         (one))
;       (else
;         ())
;         )))

(define dtree1
  (diff (one) (zero)))