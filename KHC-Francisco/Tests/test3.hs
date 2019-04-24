
-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Arm = A
data Bool = B
data Chuck  = C
data Dreamz = D
data Fail = F
--data List a = Cons a
--comment yoley out to see it working
--implicit yoley : Bool Arm = \x. D --Use to see that the 
implicit yupa : (a :: *) . (i : Arm ~> Bool) => Dreamz ~> Chuck =\x. C
--implicit yupaa : (a :: *) . Dreamz Chuck =\x. C
implicit yamano : Arm ~> Bool = \x. B
implicit yeye : Bool ~> Chuck = \x. C
--implicit f : Dreamz Arm = \x. A
--implicit yupa2 : (a :: *) . (Arm Bool) => Dreamz Chuck =\x. C


class Eq a :: * where
  equals :: a -> a -> Bool

class Eq a => Ord a :: * where
  compare :: a -> a -> Bool

-- Should Find Eq Chuck but doesnt atm. If we uncomment next lines all works because we got luck.
--instance Eq Bool where
--  equals = \x. \y. B

instance Eq Chuck where
  equals = \x. \y. B    

-- | Program expression

--(equals B A) --all good
--(equals C A)
(equals A D) -- nop
--(equals C B)
--(equals Yeah AA) --no backtracking
--(equals A (equals D B))
