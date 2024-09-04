#lang eopl

;Diff-tree = (one) | (diff Diff-tree Diff-tree)

;zero,is-zero?, successor, and predecessor

(define one
  (lambda ()
    '(one)))

(define diff
  (lambda (n1 n2)
    (list 'diff n1 n2)))

(define tag-diff-tree car)
(define left-diff-tree cadr)
(define right-diff-tree caddr)

(define is-one?
  (lambda (n)
    (eqv? (tag-diff-tree (one)) (tag-diff-tree n))))

(define zero
  (lambda ()
    (diff (one) (one))))


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