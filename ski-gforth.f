: CLS CLEARSTACK ;
: DUMP HERE OVER - DUMP ;
: COMPILE   R> DUP @ COMPILE, CELL+ >R ;
: COMPILE2  R> DUP @ COMPILE, CELL+
               DUP @ COMPILE, CELL+ >R ;

: ENTER, docol: cfa, ;

: :FUNC ( "name" -- ) CREATE ENTER, defstart ] :-hook ;

\ Application operator
: )   ( xt -- xt ) EXECUTE  ; \ Apply <=> "Application"

\ Syntactic sugar definitions
: ))  ( xt -- xt ) ) )   ;
: ))) ( xt -- xt ) ) ) ) ;

:FUNC I ;

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

I K )   CONSTANT   KI

\ S combinator
\ λxyz.xz(yz)  Sxyz = xz(yz)
:FUNC S ( y -- SX )
  HERE
  ENTER,
  COMPILE2 HERE
  COMPILE2 ENTER,
  COMPILE  SWAP
  COMPILE2 COMPILE  COMPILE DUP
  COMPILE2 COMPILE  COMPILE LIT \ y
  COMPILE2 , \ y
  COMPILE2 COMPILE2 COMPILE2 )
  COMPILE2 COMPILE  COMPILE SWAP
  COMPILE2 COMPILE  COMPILE LIT
  COMPILE  LIT \ x
  SWAP
  , \ store x
  COMPILE2 ,
  COMPILE2 COMPILE2 COMPILE2 ))
  COMPILE2 COMPILE  COMPILE EXIT
  COMPILE  EXIT
;

:FUNC .T ." TRUE "  ;
:FUNC .F ." FALSE " ;

: BOOL .F .T ;

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

