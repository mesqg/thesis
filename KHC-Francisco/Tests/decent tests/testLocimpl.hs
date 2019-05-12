-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data TyA = A
data TyB = B1 | B2
data TyC = C1 | C2

implicit i : TyB ~> TyC = \x. C2

class Cls a :: * where
  f :: TyC -> TyC -> TyC

instance Cls TyC where
  f = \x. \y. C1   

-- | Program expression
f (locimp i:TyA ~> TyB = \x.B1 in (f A A)) (locimp i:TyA ~> TyB = \x.B2 in (f A A))



