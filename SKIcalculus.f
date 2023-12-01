\ SKI Calculus in AlexForth
\ Tested in AlexForth for 6502
\ (C) 2023 Alexandre Dumont <adumont@gmail.com>
\ SPDX-License-Identifier: GPL-3.0-only

\ ENTER, places a empty header in the dictionary
\ $4C is 6502's JMP
: ENTER, ( -- ) 4C C, COMPILE COLON ;

\ Create a Function (or combinator)
\ Combinators are Higher Order Functions, meaning
\ they take a function as an Argument and return a function
\ which we will eventually apply later using ")"
: :FUNC ( "name" -- ) CREATE ENTER, ] ;


\ Application operator
: )   ( xt -- xt ) EXEC  ; \ Apply <=> "Application"

\ Syntactic sugar definitions
: ))  ( xt -- xt ) ) )   ;
: ))) ( xt -- xt ) ) ) ) ;


\ Here we redefine I,
\ no problem we can always use R> in DO LOOPs...

\ Identity Combinator
\ Ix=x    λx.x
:FUNC I ;

\ Constant Combinator, aka Kestrel
\ Kxy=x   λxy.x
:FUNC K
  HERE \ leaves the XT of the :NONAME word on the stack
  \ now we compile the :NONAME word
  ENTER,
  COMPILE DROP     \ Drop X
  COMPILE LIT      \ Push Y onto the stack
  SWAP \ put Y back on TOS
  ,  \ store Y into the definition
  COMPILE EXIT
;

\ Kite Combinator
\ KIxy=y    λxy.y
I K )   CONSTANT   KI

\ Cardinal combinator
\ λfab.fba  Cfab=fba
:FUNC C ( f -- CF )
  HERE
  ENTER,
  COMPILE HERE
  COMPILE ENTER,
  COMPILE COMPILE COMPILE LIT
  COMPILE SWAP
  COMPILE ,   \ stores a
  COMPILE COMPILE COMPILE SWAP
  COMPILE COMPILE COMPILE LIT
  COMPILE LIT
  SWAP
  ,
  COMPILE ,
  COMPILE COMPILE COMPILE ))
  COMPILE COMPILE COMPILE EXIT
  COMPILE EXIT
;

\ S combinator
\ λxyz.xz(yz)  Sxyz = xz(yz)
:FUNC S
  HERE
  ENTER,
  COMPILE HERE
  COMPILE ENTER,
  COMPILE SWAP
  COMPILE COMPILE COMPILE DUP
  COMPILE COMPILE COMPILE LIT \ y
  COMPILE , \ y
  COMPILE COMPILE COMPILE )
  COMPILE COMPILE COMPILE SWAP
  COMPILE COMPILE COMPILE LIT
  COMPILE LIT \ x
  SWAP
  , \ store x
  COMPILE ,
  COMPILE COMPILE COMPILE ))
  COMPILE COMPILE COMPILE EXIT
  COMPILE EXIT
;

\ Hack: we define those two functions so we can check results of boolean operations
:FUNC .T .( TRUE )  ;
:FUNC .F .( FALSE ) ;

: BOOL CLS .F .T ;

\ BOOLEANS
K  CONSTANT T    \ TRUE  λxy.x
KI CONSTANT F    \ FALSE λxy.y

\ Test with:
\ .F .T K  )))  --> TRUE
\ .F .T KI )))  --> FALSE

\ We define the INCR function so we
\ can check results of church numerals operations
:FUNC INCR 1+ ;
: CN 0 INCR ;

\ Garbage collection
DEFER _FORGET
:NONAME ; IS _FORGET \ NOP
: GC _FORGET MARKER ; GC
' FORGET IS _FORGET

-------------------

Process of defining S

z y x S ) → SX 	   :: S(x)
z y SX ) 	→ SXY 	 :: SX(y) = S(x)(y)
z SXY ) 	→ SXY(z) :: z y ) z x ) ) = xz(yz)
xz(yz)


: SXY ( z -- xz(yz) )
  DUP
  LIT y
  )
  SWAP
  LIT x
  ))
; \ EXIT

: SX ( y -- SXY )
  HERE
  ENTER,
  SWAP
  COMPILE DUP
  COMPILE LIT
  , \ y
  COMPILE )
  COMPILE SWAP
  COMPILE LIT
  LIT x
  ,
  COMPILE ))
  COMPILE EXIT
; \ EXIT


:FUNC S ( X -- SX )
  HERE
  ENTER,
  COMPILE HERE
  COMPILE ENTER,
  COMPILE SWAP
  COMPILE COMPILE COMPILE DUP
  COMPILE COMPILE COMPILE LIT \ y
  COMPILE , \ y
  COMPILE COMPILE COMPILE )
  COMPILE COMPILE COMPILE SWAP
  COMPILE COMPILE COMPILE LIT
  COMPILE LIT \ x
  SWAP
  , \ store x
  COMPILE ,
  COMPILE COMPILE COMPILE ))
  COMPILE COMPILE COMPILE EXIT
  COMPILE EXIT
;


Sxyz = xz(yz)


ok 1   2    3    K    I   K    S   .S
0001 0002 0003 0342 0332 0342 041E            HERE=047F
ok ) .S
0001 0002 0003 0342 0332 047F                 HERE=04AE
ok

047F 04AE DUMP

047F is the XT of S(K):

047F:
  4C
  7782       COLON
  CF8E       HERE
  0603       ENTER,
  278F       SWAP
  7683 158F  COMPILE   DUP
  7683 9F83  COMPILE   LIT
  E68D       ,
  7683 D702  COMPILE   )
  7683 278F  COMPILE   SWAP
  7683 9F83  COMPILE   LIT
  9F83 4203  LIT       0342  (K)
  E68D       ,
  7683 E302  COMPILE   ))
  7683 9482  COMPILE   EXIT
  9482       EXIT

ok 1   2    3    K   ID   SK   .S
0001 0002 0003 0342 0332 047F     HERE=04AE
ok ) .S
0001 0002 0003 0342 04AE          HERE=04C3

04AE 04C3 DUMP

04AE is the XT of SK(ID)

04AE    SK(ID)
  4C
  7782      COLON
  158F      DUP
  9F83 3203 LIT 0332  (I)
  D702      )
  278F      SWAP
  9F83 4203 LIT 0342  (K)
  E302      ))
  9482      EXIT

  1   2    3    K   SKI   .S
0001 0002 0003 0342 04AE          HERE=04C3
ok ) .S
0001 0002 0003 0342               HERE=04CE

SKIK -> K = 0342

)

ok ) .S

  1   2   K(3)
0001 0002 04CE
ok

ok ) .S
0001 0003

K(3)(2) = 3     K is the Constant Function / TRUE Function



1 2 3 ID K ID S ))) ))

1 2 3 S(ID)(K)(ID) ))

1 2


\ \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\ BOOLEANS
\ \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

: T K ;
: F KI ;

CLS .F .T T ))) CR --> TRUE
CLS .F .T F ))) CR --> FALSE

We can also use FALSE=SK. To prove it though, we do it like this:



ok CLS .F .T   F T   K S ))) ))) CR
FALSE ok

--> This verifies that SK hence select KI from "KI and K", which applied to .T & .F ends selecting .F, which shows FALSE upon executing.



----- Church  numerals!!

https://codegolf.stackexchange.com/questions/198840/ski-calculus-golf-half-of-a-church-numeral#:~:text=A%20Church%20numeral%20is%20an,applied%20to%20x%20n%20times.


:FUNC INCR 1+ ;
ok 0 INCR ) .
0001
ok 1 INCR ) .
0002

--- ZERO ---

KI is 0 --> let's check

KI is false --> 2nd argument --> won't execute INCR anytime (0) --> returns 0

ok 0 INCR KI )) .
0000 ok

--- ONE --- ??

I is ONE:

ok 0 INCR I )) .
0001 ok

--- SUCCESOR ---

SUCC = S(S(KS)K)    --> K S K ) S )) S )

LET's SEE If we can't verify that
SUCC(ONE) (it's a function) we apply it to INCR to 0 --> ¿?

0 INCR I


ok 0 INCR I    K S K ) S )) S )
ok .S
0000 04BF 0331 0520
ok ))) .
0002 ok


Let's apply only twice: ))

ok 0 INCR   I    K S K ) S )) S )
ok ))
ok .S
0000 0680
ok

We clearly see there's now a function (0680) that will apply to 0000:

Let's apply it:

ok .S
0000 0680
ok ) .
0002 ok


: ZERO KI ;
: ONE  I  ;
: SUCC K S K ) S )) S ) ;

ok 0 INCR ZERO )) .
0000 ok

ok 0 INCR ZERO SUCC ) )) .
0001 ok

ok 0 INCR ONE SUCC ) )) .
0002 ok

ok 0 INCR ONE SUCC ) SUCC ) SUCC ) )) .
0004 ok


--- SUM ---

SUM = S(KS)(S(K(S(KS)K)))

: SUM   K S K ) S )) K ) S ) S K ) S ))  ;

K S K ) S )) K ) S ) S K ) S ))

ONE SUCC ) VALUE TWO
TWO SUCC ) SUCC ) VALUE FOUR

ok 0 INCR TWO FOUR SUM ))) .S
0000 19E6 ok ) .
0006 ok



--- CREATE A DISASS FOR an XT... ¿? (reuse SEE CODE?)




\ /\ /\ /\ /\ /\ /\
 \ Lambda Calculus \
  \ /\ /\ /\ /\ /\ /\

\ Church Encoding Booleans

\ AND:   \pq.pqp

Q P AND ) --> Q AND(P) ) --> AND(P)(Q) = P Q P ))

Application behaviour of AND(P) is:

:FUNC AND
  HERE
  ENTER,
  COMPILE LIT
  SWAP
  ,
  COMPILE SWAP
  COMPILE OVER
  COMPILE ))
  COMPILE EXIT
;


ok CLS .F .T   T F AND ))) ))
FALSE ok

ok CLS .F .T   F T AND ))) ))
FALSE ok

ok CLS .F .T   F F AND ))) ))
FALSE ok

ok CLS .F .T   T T AND ))) ))
TRUE ok

\ OR:   \pq.ppq

Q P OR --> Q OR(P) --> Q P P ))


:FUNC OR
  HERE
  ENTER,
  COMPILE LIT
  SWAP
  ,
  COMPILE DUP
  COMPILE ))
  COMPILE EXIT
;

ok CLS  .F .T   T F OR ))) )) .S
TRUE ok

ok CLS  .F .T   F T OR ))) )) .S
TRUE ok

ok CLS  .F .T   F F OR ))) )) .S
FALSE ok

ok CLS  .F .T   T T OR ))) )) .S
TRUE ok


\ NOT = C (Cardinal)

: NOT C ;

ok CLS  .F .T   T NOT )) )) .S
FALSE ok

ok CLS  .F .T   F NOT )) )) .S
TRUE ok



\ EQUALITY??

EQ = XOR = \pq.pq(NOT q)

Q P EQ --> Q EQ(P) --> Q NOT ) Q P ))

:FUNC EQ
  HERE
  ENTER,
  COMPILE DUP
  COMPILE NOT
  COMPILE )
  COMPILE SWAP
  COMPILE LIT
  SWAP
  ,
  COMPILE ))
  COMPILE EXIT
;

ok CLS  .F .T   T T EQ ))) )) .S
TRUE ok

ok CLS  .F .T   T F EQ ))) )) .S
FALSE ok

ok CLS  .F .T   F T EQ ))) )) .S
FALSE ok

ok CLS  .F .T   F F EQ ))) )) .S
FALSE ok


\ Pure SKI in-fix OR

: or T ;

ok CLS  .F .T   T or F ))) )) .S
TRUE ok

ok CLS  .F .T   F or F ))) )) .S
FALSE ok

ok CLS  .F .T   F or T ))) )) .S
TRUE ok

ok CLS  .F .T   T or T ))) )) .S
TRUE ok

\ Pure SKI (post-fix) AND

\ because it's post-fix in normal SKI notation, it becomes pre-fix in Forth's postfix

: and F ;

ok CLS  .F .T   and T T ))) )) .S
TRUE ok

ok CLS  .F .T   and T F ))) )) .S
FALSE ok

ok CLS  .F .T   and T F ))) )) .S
FALSE ok

ok CLS  .F .T   and F F ))) )) .S
FALSE ok

\ Pure SKI (post-fix) NOT

\ because it's post-fix in normal SKI notation, it becomes pre-fix in Forth's postfix

: not T F ;

ok .F .T   not  T  ))) )) .S
FALSE ok
ok
ok .F .T   not  F  ))) )) .S
TRUE ok
ok



\ ----------------------------

Smart ")" word

  2 ) --> ) )

  6 ) --> ) 6 times...

  XT ) --> 1 time

  ) --> exit, do nothing DEPTH 0= IF EXIT THEN ...


  *) --> repeat ) until depth is 0


: )
  DEPTH 0=
  IF EXIT THEN

  DUP $100 / 0 > IF 1 EXEC EXIT THEN

  0 DO
    DEPTH 0=
    IF LEAVE
    ELSE EXEC
    THEN
  LOOP
;

: )* FF ) ;


**** MULTIPLICATION

MUL: λabf.a(bf)

MUL(a,b,f) = a(bf)

f b a MUL -)-> f b MUL(a) -)-> f MUL(a)(b) -)-> f b ) a )



