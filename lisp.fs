
\ -----------------------------------------------------------------------------
\ SYMBOL TABLE

begin-structure symtab-entry
  field: sym-len
  field: sym-link
  field: sym-name
end-structure

100000 cells constant SYMTAB-SIZE

SYMTAB-SIZE allocate throw dup symtab-entry erase constant stp0
stp0 value symtab

: symtab-next ( u -- )
  cell - \ sym-name already allocates 1 cell
  symtab dup >r symtab-entry + + ( entry size )
  dup symtab-entry erase to symtab r> symtab sym-link !
;

: slookup-at ( addr u stp -- symaddr|0 )
  >r dup I sym-len @ =
  if I sym-name I sym-len @ str= if I else 0 then
  else 2drop 0 then
  rdrop
;

: slookup ( addr u -- symaddr|0 )
  symtab { addr u syp }
  begin
    syp 0= if 0 exit then
    addr u syp slookup-at dup 0<> if exit then
    drop syp sym-link @ to syp
  again
;

: intern { addr u -- symaddr }
  addr u slookup dup 0<> if exit then drop
  u symtab sym-len !
  addr symtab sym-name u cmove
  symtab >r u symtab-next r>
;

: symbol-name dup sym-name swap sym-len @ ;


\ -----------------------------------------------------------------------------
\ HEAP

10000000 cells constant HEAP-SIZE
HEAP-SIZE allocate throw constant heap0
variable heap heap0 heap !

: halloc ( -- addr )
  heap @ dup 2 cells + heap !
  dup heap0 HEAP-SIZE + >= abort" out of memory!"
;
: hfree drop ; \ TODO

: %cons ( a b -- addr )
  halloc { a b addr }
  a addr !
  b addr cell + !
  addr
;
: %car ( addr -- a ) @ ;
: %cdr ( addr -- b ) cell + @ ;
: %rplaca ( na addr -- ) ! ;
: %rplacd ( nd addr -- ) cell + ! ;


\ -----------------------------------------------------------------------------
\ TYPES

: T_SYM  1 ;
: T_CONS 2 ;
: T_NUM  3 ;
: T_FUN  4 ;
: T_FTH  5 ;

: symbolp   ( addr -- flag ) @ T_SYM = ;
: consp     ( addr -- flag ) @ T_CONS = ;
: numberp   ( addr -- flag ) @ T_NUM = ;
: functionp ( addr -- flag ) @ T_FUN = ;
: forthp    ( addr -- flag ) @ T_FTH = ;

: intern  ( addr u -- addr ) intern T_SYM swap %cons ;
s" nil" intern constant nil
s" t" intern constant t

: eq ( addr addr -- ) %cdr over %cdr = nip ;

: cons ( ca cb -- addr ) %cons T_CONS swap %cons ;

: car ( addr -- a )
  dup nil eq if exit then
  dup consp invert abort" car: type error"
  %cdr %car
;

: cdr ( addr -- b )
  dup nil eq if exit then
  dup consp invert abort" cdr: type error"
  %cdr %cdr
;

: rplaca ( a addr -- ) dup consp invert abort" rplaca: type error" %cdr %rplaca ;
: rplacd ( a addr -- ) dup consp invert abort" rplacd: type error" %cdr %rplacd ;

: box ( n -- addr )
  T_NUM swap %cons
;

: .num s>d 0 d.r ;

: function ( env args body -- fun ) %cons %cons T_FUN swap %cons ;
: function-env  ( fun -- env ) dup functionp invert abort" function-env: type error" %cdr %car ;
: function-args ( fun -- env ) dup functionp invert abort" function-env: type error" %cdr %cdr %car ;
: function-body ( fun -- env ) dup functionp invert abort" function-env: type error" %cdr %cdr %cdr ;

: forth-primitive T_FTH swap %cons ;

: show ( addr -- )
  dup numberp if %cdr .num exit then
  dup symbolp if %cdr symbol-name type exit then
  dup functionp if drop ." #<function>" exit then
  dup forthp if drop ." #<primitive>" exit then
  dup consp if
    [char] ( emit
    dup car recurse
    cdr
    begin
      dup consp while
      s"  " type
      dup car recurse
      cdr
    repeat
    dup nil eq invert if
      s"  . " type
      dup recurse
    then
    drop
    [char] ) emit
    exit
  then
  drop
;


\ -----------------------------------------------------------------------------
\ PARSER

variable token 256 allot
: parse-token ( "chars" -- addr u )
  token { buf }
  >in @ source over + { end } +
  dup end >= if drop refill if recurse else token 0 then exit then
  \ skip leading spaces
  begin
    dup end  1- < over c@ bl = and while
    char+
  repeat
  \ token
  begin
    dup c@ buf !
    buf char+ to buf
    char+

    dup end <
    over c@ bl <> and
    over c@ newline drop c@ <> and
    over c@ [char] ( <> and
    over c@ [char] ) <> and
    over c@ [char] . <> and
    over 1- c@ [char] ( <> and
    over 1- c@ [char] ) <> and
    over 1- c@ [char] . <> and
  while
  repeat
  source >r - r> min >in !
  token dup buf swap -
;

: alpha ( n -- flag )  dup [char] a [char] z within swap [char] A [char] Z within or ;
: numeric ( n -- flag )  [char] 0 [char] 9 within ;
: alphanum ( n -- flag )  dup alpha swap numeric or ;

defer parse-list

0 0 2value current-token
: next-token parse-token to current-token ;

: parse-lisp ( "lisp" -- addr )
  current-token over c@
  dup [char] ( = if
    drop 2drop
    next-token
    current-token drop c@ [char] ) = if nil else parse-list then
    exit
  then
  dup numeric invert over [char] ) <> and if drop intern exit then
  dup numeric if drop 0 0 2swap >number 0 <> if 1 abort" invalid number" then drop d>s box exit then
  abort" parse error: invalid token"
;

:noname ( "list" -- addr )
  parse-lisp
  next-token
  current-token
  over c@ [char] . = if
    2drop
    next-token
    parse-lisp
    next-token
    current-token over c@ [char] ) <> if 1 abort" parse error expected )" then
    2drop
    cons exit then
  over c@ [char] ) = if
    2drop
    nil cons exit then
  2drop
  parse-list
  cons
; is parse-list

: parse-lisp next-token parse-lisp ;


\ -----------------------------------------------------------------------------
\ EVAL

: assq ( key alist -- elm | nil )
  dup nil eq if swap drop exit then
  over >r dup car car r> eq if swap drop car exit then
  cdr recurse
;

s" quote" intern       constant SYM-QUOTE
s" if" intern          constant SYM-IF
s" progn" intern       constant SYM-PROGN
s" define" intern      constant SYM-DEFINE
s" setq" intern        constant SYM-SETQ
s" lambda" intern      constant SYM-LAMBDA
s" forth" intern       constant SYM-FORTH
s" current-env" intern constant SYM-CURRENT-ENV
s" macro" intern       constant SYM-MACRO

create global-env nil ,
create macro-env nil ,

defer apply
defer evlist

: eval { exp 'env -- exp }
  exp \ dup show cr
  dup nil eq if exit then
  dup t eq if exit then
  dup numberp if exit then
  dup symbolp if dup 'env @ assq dup nil eq invert if cdr swap drop exit else drop ." symbol: " show cr then
                 1 abort" Unbound variable!" then
  dup consp if
    dup car SYM-QUOTE eq if
      cdr car exit
    then
    dup car SYM-IF eq if
      cdr dup car ( lst cnd ) >r cdr dup car ( lst thn ) swap cdr car ( thn els )
      r> 'env recurse nil eq if 'env recurse swap drop else drop 'env recurse then
      exit
    then
    dup car SYM-PROGN eq if
      cdr ( lst )
      begin
        dup car 'env recurse ( lst res ) swap cdr
        dup nil eq invert while
        swap drop
      repeat
      drop
      exit
    then
    dup car SYM-DEFINE eq if
      cdr dup car >r \ name
      cdr car 'env recurse \ eval
      dup r> swap cons 'env @ cons 'env ! \ cons in front of env
      exit
    then
    dup car SYM-SETQ eq if
      cdr dup car >r cdr car 'env recurse
      dup r> 'env @ assq dup nil eq abort" setq unbound variable!" ( val cell )
      rplacd
      exit
    then
    dup car SYM-LAMBDA eq if
      cdr dup car ( lst args ) >r cdr car ( body ) 'env @ swap ( env body ) r> swap function
      exit
    then
    dup car SYM-FORTH eq if
      cdr car %cdr symbol-name find-name dup 0= abort" invalid forth primitive!" forth-primitive
      exit
    then
    dup car SYM-CURRENT-ENV eq if drop 'env @ exit then
    dup car SYM-MACRO eq if
      cdr dup car >r \ name
      cdr car 'env recurse \ eval
      dup r> swap cons macro-env @ cons macro-env !
      exit
    then
    dup car symbolp if \ macro
      dup car macro-env @ assq dup nil eq invert if
        cdr swap cdr nil cons apply 'env recurse
        exit
      then
      drop
    then
    \ apply
    dup car 'env recurse \ eval fn
    swap cdr 'env evlist \ evaled args
    apply
    exit
  then
  abort" Unknown expression type!"
;

:noname { lst 'env -- lst }
   lst nil eq if nil exit then
   lst car 'env eval
   lst cdr 'env recurse cons
; is evlist

: zip ( lst lst -- lst )
  over nil eq if 2drop nil exit then
  2dup
  over symbolp if cons nil cons -rot 2drop exit then
  dup nil eq if 2drop nil exit then swap
  dup nil eq if 2drop nil exit then swap
  car swap
  car swap
  cons >r cdr swap cdr swap recurse r> swap cons
;

: ++ ( 1lst 2lst -- lst )
  swap dup nil eq if drop exit then
  ( 2lst 1lst ) dup car -rot cdr swap ( car 1lst 2lst ) recurse cons
;

: push-list ( x:xs -- x ... xs)
  dup nil eq if drop exit then
  dup car swap cdr recurse
;

:noname ( fn args -- val )
  swap dup functionp if
    ( args fn ) dup >r function-args swap zip ( new-env )
    I function-env ++ ( env ) halloc dup -rot ! ( 'env ) r>  function-body swap eval
    exit then
  dup forthp if
    depth 2 - >r \ get old depth
    ( args fn ) >r push-list r> %cdr execute
    depth r> - 0= if nil then \ if command returns void, return nil
    exit then
  abort" invalid application!"
; is apply

: zerop 0= if t else nil then ;

0 value gensym-counter
: gensym s" gensym" gensym-counter dup 1+ to gensym-counter s>d <# #s #>
         { g gn n nn } g pad gn move n pad gn + nn move pad gn nn + intern ;

: symbol-ref ( sym n -- sym )
  over symbolp invert abort" symbol-ref: not a symbol"
  swap %cdr symbol-name ( n addr len )
  rot %cdr 2dup <= abort" symbol-ref: invalid idx"
  ( addr len n ) rot + swap drop 1 intern
;

: symbol-len ( sym -- u )
  dup symbolp invert abort" symbol-len: not a symbol"
  %cdr symbol-name swap drop box
;

: symbol-substring ( sym from to -- sym )
  rot dup symbolp invert abort" symbol-substring: not a symbol"
  ( from to sym ) %cdr symbol-name ( from to addr u ) { from to addr u }
  addr from + u from - to from - 1- + intern
;


: :lisp ( "lisp" ... ";" -- )
  begin parse-lisp dup s" ;" intern eq if drop exit then global-env eval drop again ;

:lisp

(define show (lambda (x) ((forth show) x) nil))
(define newline (forth cr))
(define append (forth ++))
(define + (lambda (x y) ((forth box) ((forth +) ((forth %cdr) x) ((forth %cdr) y)))))
(define * (lambda (x y) ((forth box) ((forth *) ((forth %cdr) x) ((forth %cdr) y)))))
(define - (lambda (x y) ((forth box) ((forth -) ((forth %cdr) x) ((forth %cdr) y)))))
(define zerop (forth zerop))
(define eq (lambda (a b) (if (zerop ((forth eq) a b)) nil t)))
(define cons (forth cons))
(define car (forth car))
(define cdr (forth cdr))
(define cadr (lambda (x) (car (cdr x))))
(define caar (lambda (x) (car (car x))))
(define cdar (lambda (x) (cdr (car x))))
(define cddr (lambda (x) (cdr (cdr x))))
(define caddr (lambda (x) (car (cdr (cdr x)))))
(define list (lambda args args))

(macro defun (lambda (frm)
 (list (quote progn)
       (list (quote define) (car frm) (quote nil))
       (list (quote setq) (car frm) (list (quote lambda) (cadr frm) (cons (quote progn) (cddr frm)) )))))

(defun mapcar (fn xs)
  (if (eq xs nil) nil
    (cons (fn (car xs)) (mapcar fn (cdr xs)))))

(macro let (lambda (frm)
 (cons
  (cons (quote lambda) (cons (mapcar car (car frm)) (list (cons (quote progn) (cdr frm)))))
  (mapcar cadr (car frm)))))

(define rplaca (lambda (l x) ((forth rplaca) x l)))
(define rplacd (lambda (l x) ((forth rplacd) x l)))
(define error (forth throw))
(define assq (forth assq))
(define consp (lambda (x) (if (zerop ((forth consp) x)) nil t)))
(define symbolp (lambda (x) (if (zerop ((forth symbolp) x)) nil t)))

(define setter
  (let ((setters (list (cons car rplaca)
                       (cons cdr rplacd))))
  (let ((setter (lambda (proc)
                  (let ((p (assq proc setters)))
                    (if p (cdr p) (error (quote no-setter)))))))
  (let ((set-setter (lambda (proc setter)
                      (setq setters (cons (cons proc setter) setters)))))
  (progn
    (set-setter setter set-setter)
    setter)))))

(macro setf (lambda (frm)
  (if (consp (car frm))
    (cons (list (quote setter) (caar frm)) (append (cdar frm) (cdr frm)))
    (cons (quote setq) frm))))

(define apply (forth apply))
(define eval (lambda (form . args)
              ((forth eval) form (if (eq nil args) ((forth global-env)) ((forth %cons) (car args) 0)))))

(defun not (x) (if x nil t))
(defun null (x) (eq x nil))
(macro and (lambda (args) (if (null args) t (list (quote if) (car args) (cons (quote and) (cdr args)) nil))))


(defun desugar-cond (branches)
  (let ((current-branch (car branches)))
    (if (eq t (car current-branch)) (cons (quote progn) (cdr current-branch))
     (list (quote if) (car current-branch)
           (cons (quote progn) (cdr current-branch))
           (desugar-cond (cdr branches))))))
(macro cond desugar-cond)

(define gensym (forth gensym))

(macro push (lambda (frm)
  (let ((elt (car frm))
        (place (cadr frm)))
    (list (quote setf) place (list (quote cons) elt place)))))

(macro pop (lambda (frm)
  (let ((place (car frm))
        (pop-tmp-var (gensym)))
    (list (quote let) (list (list pop-tmp-var (list (quote car) place)))
      (list (quote progn) (list (quote setf) place (list (quote cdr) place)) pop-tmp-var)))))

(defun print (what) (progn (show what) (newline)))
(macro defvar (lambda (frm) (cons (quote define) frm)))
(macro defconst (lambda (frm) (cons (quote define) frm)))

(defun destructuring-bind-expander (pattern symbol)
  (cond ((null pattern) nil)
        ((symbolp pattern) (list (list pattern symbol)))
        (t (append (destructuring-bind-expander (car pattern) (list (quote car) symbol))
                   (destructuring-bind-expander (cdr pattern) (list (quote cdr) symbol))))))

(macro destructuring-bind (lambda (frm)
  (let ((v (gensym)))
    (list (quote let) (list (list v (cadr frm)))
          (cons (quote let) (cons (destructuring-bind-expander (car frm) v) (cddr frm)))))))

(macro defmacro (lambda (frm)
                  (list (quote macro) (car frm)
                        (list (quote lambda) (list (quote lst))
                              (append
                               (list (quote destructuring-bind) (cadr frm) (quote lst))
                               (cddr frm))))))

(defun assert (cnd)
  (if cnd nil (error assert-error)))

(defmacro funcall args args)

(define symbol-ref (forth symbol-ref))
(define zip (forth zip))

(defun > (x y) (if (zerop ((forth >) ((forth %cdr) x) ((forth %cdr) y))) nil t))
(macro or (lambda (args) (if (null args) nil (list (quote if) (car args) t (cons (quote or) (cdr args))))))
(defun >= (a b) (or (> a b) (eq a b)))
(defun iota (start end)
  (if (>= start end) nil (cons start (iota (+ 1 start) end))))

(defmacro let* (binds . body)
  (if (null binds) (cons (quote progn) body)
    (list (quote let) (list (car binds))
          (cons (quote let*) (cons (cdr binds) body)))))

(defmacro letrec (binds . body)
  (list (quote let) (mapcar (lambda (b)  (list (car b) nil)) binds)
    (cons (quote progn)
      (append (mapcar (lambda (b) (list (quote setq) (car b) (cadr b))) binds)
              body))))

(defun intersperse (sep lst)
  (if (null lst) nil
    (letrec ((loop (lambda (sep lst)
                     (if (null lst) nil
                       (cons sep (cons (car lst) (loop sep (cdr lst))))))))
      (cons (car lst) (loop sep (cdr lst))))))

(defun length (lst) (if (null lst) 0 (+ 1 (length (cdr lst)))))

(defun memq (elt lst)
  (cond ((null lst) nil)
        ((eq elt (car lst)) t)
        (t (memq elt (cdr lst)))))

(defun filter (fn lst)
  (cond ((null lst) nil)
        ((fn (car lst)) (cons (car lst) (filter fn (cdr lst))))
        (t (filter fn (cdr lst)))))

(defun remove-duplicates (lst)
  (if (null lst) nil
    (cons (car lst) (remove-duplicates (filter (lambda (x) (not (eq x (car lst)))) (cdr lst))))))

(defun symbol-substring (sym from to)
  ((forth symbol-substring) sym ((forth %cdr) from) ((forth %cdr) to)))
(defun symbol-len (sym)
  ((forth symbol-len) sym))

(defun reverse (lst)
  (if (null lst) nil (append (reverse (cdr lst)) (cons (car lst) nil))))

;

\ TESTS
:lisp

(newline)
(defun fact (n) (if (eq n 0) 1 (* n (fact (- n 1)))))
(show (fact 6)) (newline)
(show (mapcar (lambda (x) (+ x 2)) (quote (1 2 3)))) (newline)
(let ((x 3) (y 5)) (progn (show (+ x y)) (newline)))
(let ((x (list 1 2))) (progn (setf (car x) 3) (show x) (newline)))

;

\ PROLOG
:lisp

(defconst unbound (quote unbound))
(defun var (name binding) (cons (quote var) (cons name binding)))
(defun var-p (var) (and (consp var) (eq (quote var) (car var))))
(defun var-name (var) (cadr var))
(defun var-binding (var) (cddr var))
(defun var-bound-p (var) (not (eq (var-binding var) unbound)))

(setf (setter var-binding) (lambda (var binding) (setf (cdr (cdr var)) binding)))

(defun var-deref (exp)
  (if (and (var-p exp) (var-bound-p exp))
    (var-deref (var-binding exp))
    exp))

(defvar *trail* nil)

(let ((old-var-binding-setter (setter var-binding)))
  (setf (setter var-binding) (lambda (var binding)
                               (if (not (eq var binding))
                                   (progn
                                     (if (not (eq binding unbound))
                                         (push var *trail*) nil)
                                     (old-var-binding-setter var binding)) nil))))

(defun equal (a b)
  (cond ((and (consp a) (consp b)) (and (equal (car a) (car b)) (equal (cdr a) (cdr b))))
        (t (eq a b))))

(defun unify! (x y)
  (let ((deref-x (var-deref x)) (deref-y (var-deref y)))
    (cond ((equal deref-x deref-y) t)
          ((var-p deref-x) (setf (var-binding deref-x) deref-y) t)
          ((var-p deref-y) (setf (var-binding deref-y) deref-x) t)
          ((and (consp deref-x) (consp deref-y))
           (and (unify! (car deref-x) (car deref-y))
                (unify! (cdr deref-x) (cdr deref-y))))
          (t nil))))

(defun undo-bindings! (old-trail)
  (if (eq *trail* old-trail) nil
    (progn
      (setf (var-binding (pop *trail*)) unbound)
      (undo-bindings! old-trail))))

(defvar *var-counter* 0)

(defun ? ()
  (let ((v (var *var-counter* unbound)))
    (setf *var-counter* (+ 1 *var-counter*))
    v))

(defun mk-= (x y) (list (quote =) x y))
(defun symbol-var-p (sym) (and (symbolp sym) (eq (symbol-ref sym 0) (quote ?))))

(defun compile-arg (arg parms)
  (cond ((or (symbol-var-p arg) (and (symbolp arg) (memq arg parms))) arg)
        ((consp arg) (list (quote cons) (compile-arg (car arg) parms) (compile-arg (cdr arg) parms)))
        ((null arg) nil)
        (t (list (quote quote) arg))))


(defun compile-clause-body (body cont)
  (if (null body) (list (quote funcall) cont)
    (let* ((goal (car body))
           (predicate (car goal))
           (args (cdr goal))
           (arity (length args)))
      (cond ((and (eq predicate (quote =)) (eq 2 arity))
             (list (quote if) (list (quote unify!)
                                    (compile-arg (car args) args)
                                    (compile-arg (cadr args) args))
                              (compile-clause-body (cdr body) cont)
                              nil))
            (t (append
                 (cons predicate (mapcar (lambda (a) (compile-arg a args)) args))
                 (list (list (quote lambda) nil (compile-clause-body (cdr body) cont)))))))))

(defun variables-in (exp)
  (cond ((symbol-var-p exp) (list exp))
        ((consp exp) (append (variables-in (car exp)) (variables-in (cdr exp))))
        (t nil)))

(defun bind-unbound-vars (params exp)
  (let ((exp-vars (remove-duplicates (filter (lambda (x) (not (memq x params))) (variables-in exp)))))
    (if (null exp-vars) exp
      (list (quote let) (mapcar (lambda (v) (list v (quote (?)))) exp-vars) exp))))

(defun compile-clause (clause params cont)
  (let ((args (cdar clause)))
    (bind-unbound-vars params
      (compile-clause-body
        (append (mapcar (lambda (a) (destructuring-bind (x . y) a (list (quote =) x y))) (zip params args))
                (cdr clause))
        cont))))

(defun add-undo-bindings (compiled-exps)
  (if (eq 1 (length compiled-exps)) compiled-exps
    (list (append (list (quote let) (list (list (quote old-trail) (quote *trail*))))
                  (intersperse (quote (undo-bindings! old-trail)) compiled-exps)))))


(defun compile-predicate (symbol clauses)
  (let* ((arity (length (cdr (caar clauses))))
         (params (mapcar (lambda (x) (gensym)) (iota 0 arity))))
    (mapcar (lambda (x) (assert (eq arity (length (cdar x))))) clauses)
    (append (list (quote defun) symbol (append params (list (quote cont))))
            (add-undo-bindings
              (mapcar (lambda (clause) (compile-clause clause params (quote cont)))
                      clauses)))))

(defvar *db-predicates* nil)
(defvar *uncompiled* nil)

(defun add-clause (clause)
  (let ((clause-predicate (caar clause)))
    (assert (and (symbolp clause-predicate) (not (var-p clause-predicate))))
    (let ((entry (assq clause-predicate *db-predicates*)))
      (if (null entry)
        (progn
          (setq entry (cons clause-predicate nil))
          (push entry *db-predicates*))
        nil)
    (setf (cdr entry) (append (cdr entry) (list clause)))
    (if (not (memq clause-predicate *uncompiled*))
      (push clause-predicate *uncompiled*) nil)
    clause-predicate)))

(defmacro <- clause (list (quote add-clause) (list (quote quote) clause)))

(defun clear-predicate (symbol)
  (setq *db-predicates* (filter (lambda (x) (not (eq (car x) symbol))) *db-predicates*)))

(defun deref-exp (exp)
 (cond ((and (var-p exp) (not (var-bound-p exp))) exp)
       ((var-p exp) (deref-exp (var-deref exp)))
       ((consp exp) (cons (deref-exp (car exp)) (deref-exp (cdr exp))))
       (t exp)))

(defun prolog-success (var-names vars cont)
  (if (null vars) (print (quote yes))
      (progn
        (mapcar (lambda (x)
                  (progn
                    (show (car x)) (show (quote =)) (show (deref-exp (cdr x)))
                    (newline)))
          (zip var-names vars))
        (newline))))

(defun delete-var-? (s) (symbol-substring s 1 (symbol-len s)))
(defun ignore () nil)

(defun run-prolog (goals)
 (let* ((vars (remove-duplicates (variables-in goals)))
        (var-names (mapcar delete-var-? vars)))
   (clear-predicate (quote toplevel-query))
   (add-clause (append (cons (list (quote toplevel-query)) goals)
                       (list (list (quote prolog-success) var-names vars))))
   (let ((uncompiled (reverse *uncompiled*)))
     (setq *uncompiled* nil)
     (append
       (cons (quote progn)
         (mapcar (lambda (sym)
                   (compile-predicate sym (cdr (assq sym *db-predicates*))))
                 uncompiled))
         (list (list (quote setq) (quote *trail*) nil)
               (list (quote toplevel-query) (quote ignore)))))))

(defmacro ?- goals (run-prolog goals))

;

:lisp

(<- (member ?item (?item . ?rest)))
(<- (member ?item (?x . ?rest)) (member ?item ?rest))

(<- (app () ?x ?x))
(<- (app ?x () ?x))
(<- (app (?x . ?rest) ?y (?x . ?app)) (app ?rest ?y ?app))

(<- (rev () ()))
(<- (rev (?x . ?rest) ?rev) (rev ?rest ?rest1) (app ?rest1 (?x) ?rev))

(?- (member ?x (2 3 ?y 3)) (= ?y 4))
(?- (rev (1 2 3 4) ?l))

;
