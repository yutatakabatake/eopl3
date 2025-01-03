#lang eopl

; 3-4のLETRECを拡張した継続インタプリタから
; (set-rhs-cont env var cont)を使ってIMPLICIT-REFSを実装する

; environment ---------------------------------------
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val reference?)
   (env environment?))
  (extend-env-rec*
   (p-names (list-of identifier?))
   (b-vars (list-of identifier?))
   (p-bodies (list-of expression?))
   (env environment?)))

;apply-env : Env × Var → Ref
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec* (p-names b-vars p-bodies saved-env)
                       (let ((n (location search-var p-names)))
                         (if n
                             (newref
                              (proc-val
                               (procedure
                                (list-ref b-vars n)
                                (list-ref p-bodies n)
                                env)))
                             (apply-env saved-env search-var)))))))

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

; store --------------------------------------------------------------------

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
; the-storeのすでにバインドされている変数のexpvalを更新する
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

; expressed value -------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (list-val
   (lst (list-of expval?))))

(define-datatype proc proc?
  (procedure
   (var identifier?)
   (body expression?)
   (saved-env environment?)))

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

; expval->list : ExpVal → ListOf(ExpVal)
(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list val)))))

; continuation ------------------------------------------------------
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (rator-cont
   (rand expression?)
   (env environment?)
   (cont continuation?))
  (rand-cont
   (val1 expval?)
   (cont continuation?))
  (begin-exp-cont
    (exps (list-of expression?))
    (env environment?)
    (cont continuation?))
  (set-rhs-cont
   (env environment?)
   (var identifier?)
   (cont continuation?))
  (cons1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (cons2-cont
   (val1 expval?)
   (cont continuation?))
  (null?-cont
   (cont continuation?))
  (car-exp-cont
   (cont continuation?))
  (cdr-exp-cont
   (cont continuation?))
  (listfst-cont
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?))
  (listrst-cont
   (exps (list-of expression?))
   (lst expval?)
   (env environment?)
   (cont continuation?)))

; FinalAnswer = ExpVal
; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin
                  (eopl:printf "End of computation.~%")
                  val))
      (zero1-cont (saved-cont)
                  (apply-cont saved-cont
                              (bool-val
                               (zero? (expval->num val)))))
      (let-exp-cont (var body saved-env saved-cont)
                    (value-of/k body
                                (extend-env var (newref val) saved-env) saved-cont))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (if (expval->bool val)
                        (value-of/k exp2 saved-env saved-cont)
                        (value-of/k exp3 saved-env saved-cont)))
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (apply-cont cont (num-val (- num1 num2)))))
      (rator-cont (rand env cont)
                  (value-of/k rand env (rand-cont val cont)))
      (rand-cont (val1 cont)
                 (let ((proc1 (expval->proc val1)))
                   (apply-procedure/k proc1 val cont)))
      (begin-exp-cont (exps env cont)
                      (if (null? exps)
                          (apply-cont cont val)
                          (value-of/k (car exps) env
                                      (begin-exp-cont (cdr exps) env cont))))
      (set-rhs-cont (saved-env var saved-cont)
                    (let ((ref (apply-env saved-env var)))
                      (setref! ref val)
                      (apply-cont saved-cont (num-val 26))))
      (cons1-cont (exp2 env cont)
                  (value-of/k exp2 env (cons2-cont val cont)))
      (cons2-cont (val1 cont)
                  (apply-cont cont (list-val (cons val1 (list val)))))
      (null?-cont (cont)
                  (apply-cont cont (bool-val (null? (expval->list val)))))
      (car-exp-cont (cont)
                    (apply-cont cont (car (expval->list val))))
      (cdr-exp-cont (cont)
                    (apply-cont cont (list-val (cdr (expval->list val)))))
      (listfst-cont (exps env cont)
                    (if (null? exps)
                        (apply-cont cont (list-val (list val)))
                        (value-of/k (car exps) env
                                    (listrst-cont (cdr exps) (list-val (list val)) env cont))))
      (listrst-cont (exps lst env cont)
                    (if (null? exps)
                        (apply-cont cont (list-val (append (expval->list lst) (list val))))
                        (value-of/k (car exps) env
                                    (listrst-cont (cdr exps)
                                                  (list-val (append (expval->list lst) (list val)))
                                                  env cont))))
      )))

; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var (newref val) saved-env)
                             cont)))))

;Syntax data types
;BNFでの文法
(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (var-exp
   (var identifier?))
  (proc-exp
   (var identifier?)
   (body expression?))
  (letrec-exp
   (proc-names (list-of identifier?))
   (bound-vars (list-of identifier?))
   (proc-bodies (list-of expression?))
   (letrec-body expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (let-exp
   (var identifier?)
   (exp1 expression?)
   (body expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (call-exp
   (rator expression?)
   (rand expression?))
  (begin-exp
    (exp1 expression?)
    (exps (list-of expression?)))
  (assign-exp
   (var identifier?)
   (exp1 expression?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (car-exp
   (exp1 expression?))
  (cdr-exp
   (exp1 expression?))
  (null?-exp
   (exp1 expression?))
  (emptylist-exp)
  (list-exp
   (exps (list-of expression?))))

; value-of-program : Program → FinalAnswer
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k exp1 (init-env) (end-cont))))))

; value-of/k : Exp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (deref (apply-env env var))))
      (proc-exp (var body)
                (apply-cont cont
                            (proc-val
                             (procedure var body env))))
      (letrec-exp (p-names b-vars p-bodies letrec-body)
                  (value-of/k letrec-body
                              (extend-env-rec* p-names b-vars p-bodies env)
                              cont))
      (zero?-exp (exp1)
                 (value-of/k exp1 env
                             (zero1-cont cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont)))
      (let-exp (var exp1 body)
               (value-of/k exp1 env
                           (let-exp-cont var body env cont)))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env
                            (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                (value-of/k rator env
                            (rator-cont rand env cont)))
      (begin-exp (exp1 exps)
                 (value-of/k exp1 env
                             (begin-exp-cont exps env cont)))
      (assign-exp (var exp1)
                  (value-of/k exp1 env
                              (set-rhs-cont env var cont)))
      (cons-exp (exp1 exp2)
                (value-of/k exp1 env
                            (cons1-cont exp2 env cont)))
      (emptylist-exp ()
                     (apply-cont cont (list-val '())))
      (null?-exp (exp1)
                 (value-of/k exp1 env
                             (null?-cont cont)))
      (car-exp (exp1)
               (value-of/k exp1 env
                           (car-exp-cont cont)))
      (cdr-exp (exp1)
               (value-of/k exp1 env
                           (cdr-exp-cont cont)))
      (list-exp (exps)
                (if (null? exps)
                    (apply-cont cont (list-val '()))
                    (value-of/k (car exps) env
                                (listfst-cont (cdr exps) env cont))))
      )))


(define scanner-spec-cont-implicit
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

(define grammar-cont-implicit
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
     ("letrec"
      (arbno identifier "(" identifier ")" "=" expression)
      "in" expression)
     letrec-exp)

    ; begin-exp : begin a ; b ; c end
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)

    ; assign-exp : set x = a
    (expression
     ("set" identifier "=" expression)
     assign-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("emptylist")
     emptylist-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)
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
  (sllgen:make-string-parser scanner-spec-cont-implicit grammar-cont-implicit))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-cont-implicit grammar-cont-implicit)))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))

(define sigma
  "letrec sigma (x) = if zero?(x) 
                      then 0
                      else -((sigma -(x,1)), -(0,x))
    in (sigma 4)")

(define mytest
  "let x = 0
    in begin
        set x = 100;
        x
        end")

(define figure4.8
  "let f = proc (x) 
            proc (y)
                begin
                    set x = -(x,-1);
                    -(x,y)
                end
    in ((f 44) 33)")

(define swap-test
  "let swap = proc (x) proc (y) 
                let temp = x
                  in begin
                      set x = y;
                      set y = temp
                     end
      in let a = 33
         in let b = 44
            in begin
                ((swap a) b);
                -(a,b) 
               end")