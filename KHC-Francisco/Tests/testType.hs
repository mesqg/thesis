-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data TyA = A
data TyB = B1 | B2
data TyC = C1 | C2
data TyD = D
data TyE = E
data TyS = S

implicit i : TyB ~> TyC = \x. C2 -- global implicit declaration
implicit j : TyA ~> TyC = \x. C1
implicit k : TyC ~> TyD = \x. D
implicit l : TyB ~> TyE = \x. E
implicit s : TyS ~> TyD = \x. D
--implicit r : TyS ~> TyC = \x. C2
  
class Cls a :: * where
  f :: a -> a -> a -> a

instance Cls TyD where
  f = \x. \y. \z. x

instance Cls TyC where
  f = \x. \y. \z. y 
    

-- | Program expression
f A B1 S-- local implicit declarations
  
:*: TyD
