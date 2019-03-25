
-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Arm = A
data Bool = B
data Chuck  = C
data Dreamz = D
--data Oink = OinkOink | Yeah
--implicit yoley : Bool Dreamz = \x. D
--implicit yupa : Dreamz Chuck =\x. C
--implicit yamano : Arm Bool = \x. B
implicit yeye : Bool Chuck = \x. C

class Eq a :: * where
  equals :: a -> a -> Bool

class Eq a => Ord a :: * where
  compare :: a -> a -> Bool

instance Eq Bool where
  equals = \x. \y. B

-- | Program expression

--(equals B A) --all good
--(equals C A)
--(equals A B) -- nop
(equals C B)
--(equals Yeah AA) --no backtracking
