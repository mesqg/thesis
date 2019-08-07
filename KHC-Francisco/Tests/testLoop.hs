-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Wrapper (a::*) = W a
data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F
data Duplo  = D Chuck

implicit i : Bool  ~> Fail = \x. F
implicit j : Fail ~> Bool = \x. B2
implicit d : Fail ~> Chuck= \x.C1  
--implicit k : (a::*)(b::*) . (j : a ~> b )=> (Wrapper a) ~> (Wrapper b) = \x. case x of
--  W s -> W (j s)
-- | Program expression

D B1
