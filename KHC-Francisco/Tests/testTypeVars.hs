-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Wrapper (a::*) = W a
data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F
data Duplo = D (Wrapper Chuck)

implicit i : (a::*). (j : Fail ~> Bool) => (Wrapper a) ~> (Wrapper Chuck)  = \x. W C2
implicit f : Fail ~> Bool = \x. B1
  
-- | Program expression

D (W B1)
