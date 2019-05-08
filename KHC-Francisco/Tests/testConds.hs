-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Wrapper (a::*) = W a
data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F
data Duplo = D Chuck

implicit i : (a::*).(j : Fail ~> Bool) => Bool ~> Chuck = \x. ((\s. C2) j)
implicit f : Fail ~> Bool = \x. B1
  
-- | Program expression

(D B1)
-- \x.x
