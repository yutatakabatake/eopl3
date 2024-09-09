#lang eopl

(define-datatype bintree bintree?
  (leaf-node
   (num integer?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

(define bintree-to-list
  (lambda (btree)
    (cases bintree btree
      (leaf-node (num)
                 (list 'leaf-node num))
      (interior-node (key left right)
                     (list 'interior-node key (bintree-to-list left) (bintree-to-list right))))))

(define btree1
  (interior-node 'a
                 (leaf-node 3)
                 (leaf-node 4)))
(define btree2
  (interior-node 'a
                 (interior-node 'b
                                (leaf-node 1)
                                (leaf-node 2))
                 (leaf-node 3)))

