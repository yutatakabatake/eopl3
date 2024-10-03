#lang eopl

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val reference?)
   (env environment?))
  (extend-env-rec
   (p-names (list-of identifier?))
   (b-vars (list-of identifier?))
   (p-bodies (list-of expression?))
   (env environment?)))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-names b-vars p-bodies saved-env)
                      (let ((n (location search-var p-names)))
                        (if n
                            (newref
                             (proc-val
                              (procedure
                               (list-ref b-vars n)
                               (list-ref p-bodies n)
                               env)))
                            (apply-env saved-env search-var)))))))

;; location : Sym * Listof(Sym) -> Maybe(Int)
;; (location sym syms) returns the location of sym in syms or #f is
;; sym is not in syms.  We can specify this as follows:
;; if (memv sym syms)
;;   then (list-ref syms (location sym syms)) = sym
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms))
       => (lambda (n)
            (+ n 1)))
      (else #f))))

;init-env : () → Env
;usage: (init-env) = [i=⌈1⌉,v=⌈5⌉,x=⌈10⌉]
(define init-env
  (lambda ()
    (extend-env
     'i (newref (num-val 1))
     (extend-env
      'v (newref (num-val 5))
      (extend-env
       'x (newref (num-val 10))
       (empty-env))))))


(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (mutpair-val
   (pair mutpair?)))

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))

(define-datatype mutpair mutpair?
  (a-pair
   (left-loc reference?)
   (right-loc reference?)))

;interface
;expval->num : ExpVal → Int
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

;expval->bool : ExpVal → Bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))

; apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of body
                           (extend-env var (newref val) saved-env))))))


; empty-store : () → Sto
(define empty-store
  (lambda () '()))

; usage: A Scheme variable containing the current state of the store. Initially set to a dummy value.
(define the-store 'uninitialized)

; get-store : () → Sto
(define get-store
  (lambda () the-store))

; initialize-store! : () → Unspecified
; usage: (initialize-store!) sets the-store to the empty store
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; reference? : SchemeVal → Bool
(define reference?
  (lambda (v)
    (integer? v)))

; newref : ExpVal → Ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

; deref : Ref → ExpVal
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

; setref! : Ref × ExpVal → Unspecified
; usage: sets the-store to a state like the original, but with position ref containing val.
; the-storeを更新している
(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                ; usage: returns a list like store1, except that position ref1 contains val.
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (report-invalid-reference ref the-store))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

; expval->mutpair : ExpVal → MutPair
(define expval->mutpair
  (lambda (val)
    (cases expval val
      (mutpair-val (pair) pair)
      (else
       (report-expval-extractor-error 'mutpair val)))))

; make-pair : ExpVal × ExpVal → MutPair
(define make-pair
  (lambda (val1 val2)
    (a-pair
     (newref val1)
     (newref val2))))

; left : MutPair → ExpVal
(define left
  (lambda (p)
    (cases mutpair p
      (a-pair (left-loc right-loc)
              (deref left-loc)))))

; right : MutPair → ExpVal
(define right
  (lambda (p)
    (cases mutpair p
      (a-pair (left-loc right-loc)
              (deref right-loc)))))

; setleft : MutPair × ExpVal → Unspecified
(define setleft
  (lambda (p val)
    (cases mutpair p
      (a-pair (left-loc right-loc)
              (setref! left-loc val)))))

; setright : MutPair × ExpVal → Unspecified
(define setright
  (lambda (p val)
    (cases mutpair p
      (a-pair (left-loc right-loc)
              (setref! right-loc val)))))


;Syntax data types
;BNFでの文法
(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (letrec-exp
   (proc-names (list-of identifier?))
   (bound-vars (list-of identifier?))
   (proc-bodies (list-of expression?))
   (letrec-body expression?))
  (begin-exp
    (exp1 expression?)
    (exps (list-of expression?)))
  (assign-exp
   (var identifier?)
   (exp1 expression?))
  (newpair-exp
   (exp1 expression?)
   (exp2 expression?))
  (left-exp
   (exp1 expression?))
  (right-exp
   (exp1 expression?))
  (setleft-exp
   (exp1 expression?)
   (exp2 expression?))
  (setright-exp
   (exp1 expression?)
   (exp2 expression?)))

; value-of-program : Program → ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-env))))))

;value-of : Exp × Env σ → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (- num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))

      ; バインドされるのは参照
      ; 新しいlocationを作る，storalbe valueはval1
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var (newref val1) env))))
      (proc-exp (var body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (arg (value-of rand env)))
                  (apply-procedure proc arg)))
      (letrec-exp (proc-names bound-vars proc-bodies letrec-body)
                  (value-of letrec-body (extend-env-rec proc-names bound-vars proc-bodies env)))
      (begin-exp (exp1 exps)
                 (value-of-begin-exp (cons exp1 exps) env))
      ; 環境内でvarを探してバインドされている参照を得る
      ; exp1を評価した値を参照先に割り当てる
      (assign-exp (var exp1)
                  (begin
                    (setref!
                     (apply-env env var)
                     (value-of exp1 env))
                    (num-val 27)))

      (newpair-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (mutpair-val (make-pair val1 val2))))
      (left-exp (exp1)
                (let ((val1 (value-of exp1 env)))
                  (let ((p1 (expval->mutpair val1)))
                    (left p1))))
      (right-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((p1 (expval->mutpair val1)))
                     (right p1))))
      (setleft-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (let ((p (expval->mutpair val1)))
                       (begin
                         (setleft p val2)
                         (num-val 82)))))
      (setright-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (let ((p (expval->mutpair val1)))
                        (begin
                          (setright p val2)
                          (num-val 83)))))
      )))

(define value-of-begin-exp
  (lambda (exps env)
    (if (null? (cdr exps))
        (value-of (car exps) env)
        (begin
          (value-of (car exps) env)
          (value-of-begin-exp (cdr exps) env)))))


(define scanner-spec-mutable-pairs
  '((whitespace (whitespace) skip) ; Skip the whitespace
    ; Any arbitrary string of characters following a "%" upto a newline are skipped.
    (comment ("%" (arbno (not #\newline))) skip)
    ; An identifier is a letter followed by an arbitrary number of contiguous digits,
    ; letters, or specified punctuation characters.
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    ; A number is any digit followed by an arbitrary number of digits
    ; or a "-" followed by a digit and an arbitrary number of digits.
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define grammar-mutable-pairs
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression (identifier) var-exp)

    ; zero?-exp : zero?(a)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    ; diff-exp : -(a,b) -> (- a b)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    ; if-exp : if a then b else c
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    ; let-exp : let y = a in b
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    ; proc-exp : proc(a) b
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    ; call-exp : (a b)
    (expression
     ("(" expression expression ")")
     call-exp)

    ; letrec-exp : letrec(a) = b in c
    (expression
     ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression)
     letrec-exp)

    ; begin-exp : begin a ; b ; c end
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)

    (expression
     ("set" identifier "=" expression)
     assign-exp)

    (expression
     ("pair" "(" expression "," expression ")")
     newpair-exp)

    (expression
     ("left" "(" expression ")")
     left-exp)

    (expression
     ("setleft" "(" expression "," expression ")")
     setleft-exp)

    (expression
     ("right" "(" expression ")")
     right-exp)

    (expression
     ("setright" "(" expression "," expression ")")
     setright-exp)
    ))



(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

;run : String → ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-mutable-pairs grammar-mutable-pairs))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-mutable-pairs grammar-mutable-pairs)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))

(define figure4.11
  "let glo = pair(11,22)
    in let f = proc (loc)
                let d1 = setright(loc, left(loc)) 
                in let d2 = setleft(glo, 99)
                    in -(left(loc),right(loc))
        in (f glo)")