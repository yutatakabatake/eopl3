#lang eopl

(define duple
  (lambda (n x)
    (if (zero? n)
        '()
        (cons x (duple (- n 1) x)))))

(define invert
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (cons (car (cdr (car lst)))
                    (car (car lst)))
              (invert (cdr lst))))))

(define down
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (list (car lst))
              (down (cdr lst))))))

(define swapper
  (lambda (s1 s2 lst)
    (cond
      ((null? lst)
       lst)
      ((eqv? s1 (car lst))
       (cons s2 (swapper s1 s2 (cdr lst))))
      ((eqv? s2 (car lst))
       (cons s1 (swapper s1 s2 (cdr lst))))
      ((list? (car lst))
       (cons (swapper s1 s2 (car lst)) (swapper s1 s2 (cdr lst))))
      (else
       (cons (car lst) (swapper s1 s2 (cdr lst)))))))
      

(define list-set
  (lambda (lst n x)
    (if (null? lst)
        '()
        (if (zero? n)
            (cons x (cdr lst))
            (cons (car lst) (list-set (cdr lst) (- n 1) x))))))

(define count-occurrences
  (lambda (s slist)
    (count-help s slist 0)))


(define count-help
  (lambda (s slist n)
    (cond
      ((null? slist)
       n)
       ((eqv? s (car slist))
        (count-help s (cdr slist) (+ n 1)))
       ((list? (car slist))
        (+ (count-help s (car slist) n) (count-help s (cdr slist) n))) 
       (else
        (count-help s (cdr slist) n)))))

;concatenate the elements of the lst1 from the top and join the lst2 behind it
(define conc
  (lambda (lst1 lst2)
    (if (null? lst1)
        lst2
        (if (null? lst2)
            lst1
            (cons (car lst1) (conc (cdr lst1) lst2))))))

(define product
  (lambda (sos1 sos2)
    (if (null? sos1)
        '()
        (if (null? sos2)
            '()
            (conc (product-help (car sos1) sos2) (product (cdr sos1) sos2))))))

(define product-help
  (lambda (sym sos)
    (if (null? sos)
        sos
        (cons (cons sym (list (car sos))) (product-help sym (cdr sos))))))

(define up
  (lambda (lst)
    (if (null? lst)
        lst
        (if (list? (car lst))
            (conc (car lst) (up (cdr lst)))
            (cons (car lst) (up (cdr lst)))))))
    

(define filter-in
  (lambda (pred lst)
    (if (null? lst)
        '()
        (if (pred (car lst))
            (cons (car lst) (filter-in pred (cdr lst)))
            (filter-in pred (cdr lst))))))

(define list-index
  (lambda (pred lst)
    (if (eqv? '() (list-index-ex pred lst 0))
        #f
        (list-index-ex pred lst 0))))

(define list-index-ex
  (lambda (pred lst n)
    (if (null? lst)
        '()
        (if (pred (car lst))
            n
            (list-index-ex pred (cdr lst) (+ n 1))))))

(define every?
  (lambda (pred lst)
    (if (pred (car lst))
        (if (eqv? '() (cdr lst))
            #t
            (every? pred (cdr lst)))
        #f)))

(define exists?
  (lambda (pred lst)
    (if (pred (car lst))
        #t
        (if (null? (cdr lst))
            #f
            (exists? pred (cdr lst))))))

(define flatten
  (lambda (slist)
    (cond
      ((null? slist)
       slist)
      ((list? (car slist))
       (flatten (conc (car slist) (cdr slist))))
      (else
       (cons (car slist) (flatten (cdr slist)))))))

(define sort
  (lambda (loi)
    (cond
      ((null? loi)
       loi)
      (else
       (insert (car loi) (sort (cdr loi)))))))

(define insert
  (lambda (i loi)
    (if (null? loi)
       (list i)
       (cond
         ((<= i (car loi))
          (cons i loi))
         ((> i (car loi))
          (cons (car loi) (insert i (cdr loi))))))))

(define merge
  (lambda (loi1 loi2)
    (sort (conc loi1 loi2))))

(define (list-length lst)
  (if (null? lst)
      0
      (+ 1 (list-length (cdr lst)))))

(define (remove-first s los)
  (if (null? los)
      los
      (if (eqv? s (car los))
          (cdr los)
          (cons (car los) (remove-first s (cdr los))))))

(define sort/predicate
  (lambda (pred loi)
    (if (null? loi)
        loi
        (insert/predicate pred (car loi) (sort (cdr loi))))))

(define insert/predicate
  (lambda (pred i loi)
    (if (null? loi)
        (list i)
        (cond
          ((pred i (car loi))
           (cons i loi))
          ((eqv? i (car loi))
           (cons i loi))
          (else
           (cons (car loi) (insert/predicate pred i (cdr loi))))))))

(define leaf
  (lambda (n)
    n))

(define interior-node
  (lambda (sym bintree1 bintree2)
    (cons sym (cons bintree1 (list bintree2)))))

(define leaf?
  (lambda (bintree)
    (if (number? bintree)
        #t
        #f)))

(define lson
  (lambda (bintree)
    (if (number? bintree)
        bintree
        (cadr bintree))))

(define rson
  (lambda (bintree)
    (if (number? bintree)
        bintree
        (caddr bintree))))

(define contents-of
  (lambda (node)
    (if (leaf? node)
        node
        (car node))))

(define double-tree
  (lambda (bintree)
    (cond
      ((leaf? bintree)
       (* 2 bintree))
      ((leaf? (lson bintree))
       (cons (contents-of bintree) (cons (* 2 (lson bintree)) (list (double-tree (rson bintree))))))
      ((leaf? (rson bintree))
       (cons (contents-of bintree) (cons (lson bintree) (* 2 (rson bintree)))))
      (else
       (cons (contents-of bintree) (cons (double-tree (lson bintree)) (list (double-tree (rson bintree))))))
      )))

(define mark-leaves-with-red-depth
  (lambda (bintree)
    (mark-leaves-with-red-depth-help bintree 0)))

(define mark-leaves-with-red-depth-help
  (lambda (bintree n)
    (if (leaf? bintree)
        (leaf n)
        (if (eqv? 'red (contents-of bintree))
            (interior-node (contents-of bintree) (mark-leaves-with-red-depth-help (lson bintree) (+ n 1)) (mark-leaves-with-red-depth-help (rson bintree) (+ n 1)))
            (interior-node (contents-of bintree) (mark-leaves-with-red-depth-help (lson bintree) n) (mark-leaves-with-red-depth-help (rson bintree) n))))))

(define path
  (lambda (n bst)
    (path-help n bst '())))

(define path-help
  (lambda (n bst ans)
    (if (null? bst)
        bst
        (cond
          ((eqv? n (contents-of bst))
           ans)
          ((> n (contents-of bst))
           (path-help n (rson bst) (conc ans (list 'right))))
          ((< n (contents-of bst))
           (path-help n (lson bst) (conc ans (list 'left))))))))
            

(define number-leaves
  (lambda (bintree)
    (if (null? bintree)
        bintree
        (car (number-leaves-help (cons bintree 0))))))

; (bintree . num) -> (bintree . num)
(define number-leaves-help
  (lambda (lst-bintree-num)
    (let ((bintree (car lst-bintree-num))
          (num (cdr lst-bintree-num)))
      (let ((left (lson bintree))
            (right (rson bintree)))
        (cond
          ((leaf? (car lst-bintree-num))
           (cons (leaf num) (+ num 1)))
          (else
           (let ((left-lst (number-leaves-help (cons left num))))
             (let ((next-left (car left-lst))
                   (next-left-num (cdr left-lst)))
               (let ((right-lst (number-leaves-help (cons right next-left-num))))
                 (let ((next-right (car right-lst))
                       (next-right-num (cdr right-lst)))
                   (cons (interior-node (contents-of (car lst-bintree-num)) next-left next-right) next-right-num)))))))))))

(define number-elements
  (lambda (lst)
    (if (null? lst)
        '()
        (g (list 0 (car lst)) (number-elements (cdr lst))))))

    ;(number-elements-from lst 0)))

(define number-elements-from
  (lambda (lst n)
    (if (null? lst)
        '()
        (cons
         (list n (car lst))
         (number-elements-from (cdr lst) (+ n 1))))))

(define g
  (lambda (fst snd)
    (if (null? snd)
        (cons fst snd)
        (cons fst (g-help snd)))))


(define g-help
  (lambda (lst)
    (let ((num (car (car lst))) (sym (cdr (car lst))) (rst (cdr lst)))
      (if (null? rst)
          (cons (cons (+ num 1) sym) rst)
          (cons (cons (+ num 1) sym) (g-help rst))))))

;(define g
;  (lambda (x y)
;    (let ((0-list (cons x y)))
;      (let ((size (length 0-list)))
;        (h 0-list size)))))

;(define h
;  (lambda (lst size)
;    (if (eqv? size 1)
;        0-list
;        (let ((obj (car lst)))
;          (let ((obj-n (car obj)))
            
        

;; (number-elements lst)
(define lst '(a b c d e f g h i))
(define ex '((0 a) (1 b) (2 c) (3 d)))

(define a '(red 5 5))
(define b '(foo 100 100))
(define x '(bar 1 (red 4 5)))
(define xx '(bar (foo 1 2) (red 4 5)))
(define y
  (interior-node 'baz
                 (interior-node 'bar
                                (leaf 1)
                                (interior-node 'foo
                                               (interior-node 'fiz
                                                              (leaf 23)
                                                              (leaf 500))
                                               (leaf 2)))
                 (interior-node 'red
                                (leaf 9)
                                (leaf 12))))
(define z
  (interior-node 'foo
                 (interior-node 'bar
                                (leaf 26)
                                (leaf 12))
                 (interior-node 'baz
                                (leaf 11)
                                (interior-node 'quux
                                               (leaf 117)
                                               (leaf 14)))))
(define c '(14 (7 () (12 () ()))
               (26 (20 (17 () ())
                       ())
                   (31 () ()))))