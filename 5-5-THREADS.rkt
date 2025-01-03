#lang eopl

; threadsを継続を利用して実装
; storeを利用した値渡し

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

; store --------------------------------------------------------------------
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

; queue -----------------------------------------------------
(define empty-queue
  (lambda ()
    '()))

(define empty? null?)

(define enqueue
  (lambda (q val)
    (append q (list val))))

(define dequeue
  (lambda (q f)
    (f (car q) (cdr q))))

; scheduler ---------------------------------------------------
(define the-ready-queue 'uninitialized)
(define the-final-answer 'uninitialized)
(define the-max-time-slice 'uninitialized)
(define the-time-remaining 'uninitialized)

; Thread = () → ExpVal
; initialize-scheduler! : Int → Unspecified
(define initialize-scheduler!
  (lambda (ticks)
    (set! the-ready-queue (empty-queue))
    (set! the-final-answer 'uninitialized)
    (set! the-max-time-slice ticks)
    (set! the-time-remaining the-max-time-slice)))

; place-on-ready-queue! : Thread → Unspecified
(define place-on-ready-queue!
  (lambda (th)
    (set! the-ready-queue
          (enqueue the-ready-queue th))))

; run-next-thread : () → FinalAnswer
(define run-next-thread
  (lambda ()
    (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
                 (lambda (first-ready-thread other-ready-threads)
                   (set! the-ready-queue other-ready-threads)
                   (set! the-time-remaining the-max-time-slice)
                   (first-ready-thread))))))

; set-final-answer! : ExpVal → Unspecified
(define set-final-answer!
  (lambda (val)
    (set! the-final-answer val)))

; time-expired? : () → Bool
(define time-expired?
  (lambda ()
    (zero? the-time-remaining)))

; decrement-timer! : () → Unspecified
(define decrement-timer!
  (lambda ()
    (set! the-time-remaining (- the-time-remaining 1))))

; mutex ---------------------------------------------------------
(define-datatype mutex mutex?
  (a-mutex
   (ref-to-closed? reference?)
   (ref-to-wait-queue reference?)))

;    new-mutex : () → Mutex
(define new-mutex
  (lambda ()
    (a-mutex
     (newref #f)
     (newref '()))))

; wait-for-mutex : Mutex × Thread → FinalAnswer
; usage: waits for mutex to be open, then closes it.
(define wait-for-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (cond
                 ((deref ref-to-closed?)
                  (setref! ref-to-wait-queue
                           (enqueue (deref ref-to-wait-queue) th))
                  (run-next-thread))
                 (else
                  (setref! ref-to-closed? #t) (th)))))))

; signal-mutex : Mutex × Thread → FinalAnswer
(define signal-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (let ((closed? (deref ref-to-closed?))
                     (wait-queue (deref ref-to-wait-queue)))
                 (when closed?
                   (if (empty? wait-queue)
                       (setref! ref-to-closed? #f)
                       (dequeue wait-queue
                                (lambda (first-waiting-th other-waiting-ths)
                                  (place-on-ready-queue!
                                   first-waiting-th)
                                  (setref!
                                   ref-to-wait-queue
                                   other-waiting-ths)))))
                 (th))))))

; expressed value -------------------------------------
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?))
  (list-val
   (lst (list-of expval?)))
  (mutex-val
   (mutex mutex?)))

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
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc val)))))

; expval->proc : ExpVal → ListOf(Int)
(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (report-expval-extractor-error 'list val)))))

; expval->mutex : ExpVal → Mutex
(define expval->mutex
  (lambda (val)
    (cases expval val
      (mutex-val (mutex) mutex)
      (else (report-expval-extractor-error 'mutex val)))))

; program,expression ----------------------------------------------------------
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
   (exps (list-of expression?)))
  (print-exp
   (exp1 expression?))
  (spawn-exp
   (exp1 expression?))
  (mutex-exp)
  (wait-exp
   (exp1 expression?))
  (signal-exp
   (exp1 expression?)))

; value-of-program : Int × Program → FinalAnswer
(define value-of-program
  (lambda (timeslice pgm)
    (initialize-store!)
    (initialize-scheduler! timeslice)
    (cases program pgm
      (a-program (exp1)
                 (value-of/k
                  exp1
                  (init-env)
                  (end-main-thread-cont))
                 ))))

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
      (print-exp (exp1)
                 (value-of/k exp1 env
                             (print-cont cont)))
      (spawn-exp (exp1)
                 (value-of/k exp1 env
                             (spawn-cont cont)))
      (mutex-exp ()
                 (apply-cont cont (mutex-val (new-mutex))))
      (wait-exp (exp1)
                (value-of/k exp1 env (wait-cont cont)))
      (signal-exp (exp1)
                  (value-of/k exp1 env (signal-cont cont))))))

; apply-procedure/k : Proc × ExpVal × Cont → FinalAnswer
(define apply-procedure/k
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var (newref val) saved-env)
                             cont)))))

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
   (cont continuation?))
  (print-cont
   (cont continuation?))
  (spawn-cont
   (cont continuation?))
  (end-main-thread-cont)
  (end-subthread-cont)
  (wait-cont
   (cont continuation?))
  (signal-cont
   (cont continuation?)))

; FinalAnswer = ExpVal
; apply-cont : Cont × ExpVal → FinalAnswer
(define apply-cont
  (lambda (cont val)
    (if (time-expired?)
        (begin
          (place-on-ready-queue!
           (lambda () (apply-cont cont val)))
          (run-next-thread))
        (begin
          (decrement-timer!)
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
                        (apply-cont cont (list-val (cons val1 (expval->list val)))))
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
            (print-cont (cont)
                        (display val)
                        (newline)
                        (apply-cont cont (num-val 1)))  ; unspecified
            (spawn-cont (saved-cont)
                        (let ((proc1 (expval->proc val)))
                          (place-on-ready-queue!
                           (lambda ()
                             (apply-procedure/k proc1
                                                (num-val 28)
                                                (end-subthread-cont))))
                          (apply-cont saved-cont (num-val 73))))
            (end-main-thread-cont ()
                                  (set-final-answer! val)
                                  (run-next-thread))
            (end-subthread-cont ()
                                (run-next-thread))
            (wait-cont (saved-cont)
                       (wait-for-mutex
                        (expval->mutex val)
                        (lambda () (apply-cont saved-cont (num-val 52)))))
            (signal-cont (saved-cont)
                         (signal-mutex
                          (expval->mutex val)
                          (lambda () (apply-cont saved-cont (num-val 53)))))
            )))))

(define scanner-spec-threads
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

(define grammar-threads
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
     ("spawn" "(" expression ")")
     spawn-exp)

    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("list" "(" (separated-list number ",") ")")
     list-exp)

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

    ; print-exp : print(a)
    (expression
     ("print" "(" expression ")")
     print-exp)

    (expression
     ("mutex" "(" ")")
     mutex-exp)

    (expression
     ("wait" "(" expression ")")
     wait-exp)

    (expression
     ("signal" "(" expression ")")
     signal-exp)
    ))



(define identifier?
  (lambda (x)
    (and
     (symbol? x)
     (not (eqv? x 'lambda)))))

(define any?
  (lambda (x) #t))

;run : String → ExpVal
(define run
  (lambda (timeslice string)
    (value-of-program timeslice (scan&parse string))))

(define scan&parse
  (sllgen:make-string-parser scanner-spec-threads grammar-threads))

(define repl
  (sllgen:make-rep-loop "--> "
                        (lambda (pgm) (value-of-program pgm))
                        (sllgen:make-stream-parser scanner-spec-threads grammar-threads)))

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


; schedularが割り込む前にprintする
(define figure5.16
  "letrec
        noisy (l) = if null?(l) 
                    then 0
                    else begin 
                            print(car(l)); 
                            (noisy cdr(l)) 
                         end
    in
        begin
            spawn(proc (d) (noisy list(1,2,3,4,5))) ; 
            spawn(proc (d) (noisy list(6,7,8,9,10))) ; 
            print(100);
            33
        end")

(define figure5.17
  "let buffer = 0
    in let producer = proc (n)
            letrec
                Wwait(k) = if zero?(k)
                          then set buffer = n 
                          else begin
                               print(-(k,-200));
                               (Wwait -(k,1))
                                end
            in (Wwait 5)
        in let consumer = proc (d)
                letrec busywait (k) = if zero?(buffer) 
                                      then begin
                                              print(-(k,-100));
                                              (busywait -(k,-1))
                                            end
                                      else buffer
                in (busywait 0)
            in begin
                spawn(proc (d) (producer 44)); 
                % print(300);
                (consumer 86)
               end")

(define unsafe-counter
  "let x = 0
      in let incr_x = proc (id)
                       proc (dummy)
                        set x = -(x,-1)
            in begin
                  spawn((incr_x 100));
                  spawn((incr_x 200));
                  spawn((incr_x 300));
                  x
               end")

(define safe-counter-mutex
  "let x = 0
      in let mut = mutex()
           in let incr_x = proc (id)
                               proc (dummy)
                                begin
                                 wait(mut);
                                 set x = -(x,-1);
                                 signal(mut)
                                end
                in begin
                    spawn((incr_x 100));
                    spawn((incr_x 200));
                    spawn((incr_x 300));
                    x
                   end")

(define safe-ctr
  "let ctr = let x = 0 in let mut = mutex()
             in proc (n) proc (d)
                  begin
                   wait(mut);
                   print(n); 
                   print(x);
                   set x = -(x,-1);
                   print(n); 
                   print(x);
                   signal(mut)
                  end
   in begin
       spawn((ctr 100));
       spawn((ctr 200));
       spawn((ctr 300));
       999
      end")