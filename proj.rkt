#lang racket
(require redex)

(define-language pcf
  (e ::= ;; expressions 
     x
     z
     (e e)
     (s(e))
     (ifz(e e x e))
     (fun(x x e))
     (app(e e))
     )
  (v ::=
     (fun(x x e))
     z
     (s(v))
     )
  (z 0)
  (mu ((l v) ...))
  (ro ((l v) ...))
  (nu ((l v) ...))
  (x ::= variable-not-otherwise-mentioned)
  (sig ::= store)
  (store ::= (mu ro nu))
  (l number)
  (r ::=
     (l ...))
  (n ::= number)
  )


(define judgment-form pcf
  #:contract(evdy sig e r n) 
  #:mode (evdy I I I O)


  ------------------------------- tz
  sig z r 
  
  )
