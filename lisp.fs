
\ -----------------------------------------------------------------------------
\ SYMBOL TABLE

begin-structure symtab-entry
  field: sym-len
  field: sym-link
  field: sym-name
end-structure

10000 cells constant SYMTAB-SIZE

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

100000 cells constant HEAP-SIZE
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
    dup car s" quote" intern eq if 
      cdr car exit
    then
    dup car s" if" intern eq if
      cdr dup car ( lst cnd ) >r cdr dup car ( lst thn ) swap cdr car ( thn els )
      r> 'env recurse nil eq if 'env recurse swap drop else drop 'env recurse then
      exit
    then
    dup car s" progn" intern eq if
      cdr ( lst )
      begin
        dup car 'env recurse ( lst res ) swap cdr 
        dup nil eq invert while
        swap drop
      repeat
      drop
      exit
    then
    dup car s" define" intern eq if
      cdr dup car >r \ name
      cdr car 'env recurse \ eval
      dup r> swap cons 'env @ cons 'env ! \ cons in front of env
      exit
    then
    dup car s" setq" intern eq if
      cdr dup car >r cdr car 'env recurse
      dup r> 'env @ assq dup nil eq abort" setq unbound variable!" ( val cell )
      rplacd
      exit
    then
    dup car s" lambda" intern eq if
      cdr dup car ( lst args ) >r cdr car ( body ) 'env @ swap ( env body ) r> swap function
      exit
    then
    dup car s" forth" intern eq if
      cdr car %cdr symbol-name find-name dup 0= abort" invalid forth primitive!" forth-primitive
      exit
    then
    dup car s" show-env" intern eq if
      ." env: " 'env @ show cr .s cr drop nil
      exit
    then
    dup car s" macro" intern eq if
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
  dup nil eq if 2drop nil exit then swap
  dup nil eq if 2drop nil exit then swap
  2dup
  over symbolp if cons nil cons -rot 2drop exit then
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
(define list (lambda args args))

(macro defun (lambda (frm)
 (list (quote progn)
       (list (quote define) (car frm) (quote nil))
       (list (quote setq) (car frm) (cons (quote lambda) (cdr frm))))))

(defun mapcar (fn xs)
  (if (eq xs nil) nil
    (cons (fn (car xs)) (mapcar fn (cdr xs)))))

(macro let (lambda (frm)
 (cons
  (cons (quote lambda) (cons (mapcar car (car frm)) (cdr frm)))
  (mapcar cadr (car frm)))))

(define rplaca (lambda (l x) ((forth rplaca) x l)))
(define rplacd (lambda (l x) ((forth rplacd) x l)))
(define error (forth throw))
(define assq (forth assq))
(define consp (lambda (x) (if (zerop ((forth consp) x)) nil t)))

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

;

\ TESTS
:lisp

(newline)

(defun fact (n) (if (eq n 0) 1 (* n (fact (- n 1)))))
(show (fact 6))
(newline)

(show (mapcar (lambda (x) (+ x 2)) (quote (1 2 3))))
(newline)

(let ((x 3) (y 5))
  (progn
    (show (+ x y))
    (newline)))

;

