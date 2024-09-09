#lang eopl

(define number->bintree
  (lambda (n)
    (list n '() '())))

(define current-element
  (lambda (bintree)
    (car bintree)))

(define move-to-left-son
  (lambda (bintree)
    (cadr bintree)))

(define move-to-right-son
  (lambda (bintree)
    (caddr bintree)))

(define insert-to-left
  (lambda (n bintree)
    (let ((elem (car bintree))
          (lson (cadr bintree))
          (rson (caddr bintree)))
      (list elem (list n lson '()) rson))))

(define insert-to-right
  (lambda (n bintree)
    (let ((elem (car bintree))
          (lson (cadr bintree))
          (rson (caddr bintree)))
      (list elem lson (list n '() rson)))))

(define t1 (insert-to-right 14 (insert-to-left 12 (number->bintree 13))))