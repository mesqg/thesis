-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Wrapper (a::*) = W a
data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F
data Duplo  = D (Wrapper Fail) (Wrapper Fail)

implicit i : Bool  ~> Fail = \x. F
implicit j : Chuck ~> Fail = \x. F 
implicit k : (a::*)(b ::*) . (j : a ~> b )=> (Wrapper a) ~> (Wrapper b) = \x. case x of
  W s -> W (j s)
-- | Program expression

D (W B1) (W C1)
:*: Duplo
