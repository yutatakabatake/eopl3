#lang eopl

(define number->sequence
  (lambda (n)
    (list n '() '())))

(define current-element
  (lambda (lst)
    (car lst)))

(define move-to-left
  (lambda (lst)
    (let ((focus (car lst))
          (lst1 (cadr lst))
          (lst2 (caddr lst)))
      (list (car lst1) (cdr lst1) (cons focus lst2)))))

(define move-to-right
  (lambda (lst)
    (let ((focus (car lst))
          (lst1 (cadr lst))
          (lst2 (caddr lst)))
      (list (car lst2) (cons focus lst1) (cdr lst2)))))

(define insert-to-left
  (lambda (n lst)
    (let ((focus (car lst))
          (lst1 (cadr lst))
          (lst2 (caddr lst)))
      (list focus (cons n lst1) lst2))))

(define insert-to-right
  (lambda (n lst)
    (let ((focus (car lst))
          (lst1 (cadr lst))
          (lst2 (caddr lst)))
      (list focus lst1 (cons n lst2)))))

(define at-left-end?
  (lambda (lst)
    (let ((lst1 (cadr lst)))
      (null? lst1))))

(define at-right-end?
  (lambda (lst)
    (let ((lst2 (caddr lst)))
      (null? lst2))))