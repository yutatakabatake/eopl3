#lang eopl

;; CPS変換

; 1. (lambda (x y) (p (+ 8 x) (q y)))

; (lambda (x y cont)
;   (q y (lambda (v1)
;          (p (+ 8 x) v1 cont))))


; 2. (lambda (x y u v)
;      (+ 1 (f (g x y) (+ u v))))

; (lambda (x y u v cont)
;   (g x y (lambda (v1)
;            (f v1 (+ u v) (lambda (v2)
;                            (+ 1 v2 cont))))))


; 3. (+ 1 (f (g x y) (+ u (h v))))

; (g x y (lambda (v1)
;          (h v (lambda (v2)
;                 (f v1 (+ u v2) (lambda (v3)
;                                  (+ 1 v3)))))))


; 4. (zero? (if a (p x) (p y)))

; (a (lambda (v1)
;      (if v1
;          (p x (lambda (v2) (zero? v2)))
;          (p y (lambda (v3) (zero? v3))))))

; 5. (zero? (if (f a) (p x) (p y)))

; (f a (lambda (v1)
;        (if v1
;            (p x (lambda (v2) (zero? v2)))
;            (p y (lambda (v3) (zero? v3))))))


;; ???
; 6.(let ((x (let ((y 8))
;              (p y))))
;     x)

; (y 8 (lambda (var1)
;        (p y (lambda (val1)
;               (let ((var1 val1))
;                 var1 (lambda (val2)
;                        (let ((x val2))
;                          x)))))))


; 7. (let ((x (if a (p x) (p y)))) x)

; (a (lambda (val1)
;      (if a
;          (p x (lambda (val2) (let ((x val2)) x)))
;          (p y (lambda (val3) (let ((x val3)) x))))))
