-- * Simple example with superclasses
-- ----------------------------------------------------------------------------

data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F

implicit i : Bool ~> Chuck = \x. C2

class Eq a :: * where
  equals :: Chuck -> Chuck -> Chuck

instance Eq Chuck where
  equals = \x. \y. C1   

-- | Program expression

equals (locimp (i:Fail ~> Bool = \x.B1) in (equals F F)) (locimp (i:Fail ~> Bool = \x.B2) in (equals F F))
