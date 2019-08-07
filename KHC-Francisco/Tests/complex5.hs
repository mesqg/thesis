-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data TyA = A
data TyB = B
data TyC = C TyB
data TyD = D
data TyW (a::*) = W a a


--(locimp l : TyD ~> TyA = \x.A in (locimp k : (v1::*)(v2::*). (j : v1 ~> v2) => (TyW v1) ~> (TyW v2) = \x. case x of W a b -> (W (j a) (j b)) in (locimp i1 :TyC ~> TyD = \x.D in (locimp i2 : TyB~>TyD = \x1. D in (W B (locimp i3 : TyA ~> TyB = \x.B in (C A)))))))
(locimp i3 : TyA ~> TyB = \x.B in (\z1.\z2. W z1 z2) A B)
:*: TyW TyB

