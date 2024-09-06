#lang eopl

(define-datatype bintree bintree?
  (leaf-node
   (num integer?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

; (define max-interior
;   (lambda (btree)
;     (cases bintree btree
;       (leaf-node (num)
;                  '())
;       (interior-node (key left right)
;                      (let ((left-sum )
;                            (right-sum )
;                            ))))))

; (define sum-leaves
;   (lambda (btree sum)
;     (cases bintree btree
;       (leaf-node (num)
;                  (+ num sum))
;       (interior-node (key left right)
;                      (cases bintree left
;                        (leaf-node (num)
;                                   ())
;                        (interior-node (key left right)
;                                       (sum-leaves left sum)))))))

(define tree-1
  (interior-node 'foo
                 (leaf-node 2)
                 (leaf-node 3)))

(define tree-2
  (interior-node 'bar
                 (leaf-node -1)
                 tree-1))

(define tree-3
  (interior-node 'baz
                 tree-2
                 (leaf-node 1)))