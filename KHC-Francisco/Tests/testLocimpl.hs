-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data TyA = A1 | A2 | A3 | A4 | A5
data TyB = B1 | B2
data TyC = C1 | C2
data TyD = D

implicit i : TyB ~> TyC = \x. C2
implicit conf : TyC ~> TyD = \x.D
  
class Cls a :: * where
  f :: a  -> a-> a

instance Cls TyC where
  f = \x.\y. x

class Cls2 a :: * where
  g :: a -> a -> TyC

instance Cls2 TyA where
  g = \x. \y .C1       

instance Cls TyA where
  f = \x.\y.y
    
-- | Program expression
--g (locimp i:TyA ~> TyB = \x.B2 in (f A2 A3)) (f A4 A5) (locimp i:TyA ~> TyB = \x.B1 in (f A1 A1))
(locimp i:TyA ~> TyB = \x.B2 in (g (f A2 A3) (f A1 A4)))
--g (f A A)
:*: TyC

