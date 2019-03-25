
-- * Simple example with superclasses
-- ----------------------------------------------------------------------------

data Bool = True | False
data Chuck  = AA
data Oink = OinkOink | Yeah

implicit yamano : Chuck Bool = \x. False
implicit yeye : Bool Oink = \x. OinkOink

class Eq a :: * where
  equals :: a -> a -> Bool

class Eq a => Ord a :: * where
  compare :: a -> a -> Bool

instance Eq Bool where
  equals = \x. \y. case x of
      True -> case y of
          True -> True
          False -> False
      False -> case y of
          True -> False
          False -> True
instance Eq Oink where
  equals = \z.\z.False

-- | Program expression

--(\x. (equals False x)) (Yeah) -- works fine
--(\x. (equals AA x)) (Yeah) -- works fine
(\x. (equals x False)) (Yeah) -- doesn't. Think because we dont have backtrack yet

--(equals False AA) --all good
   -- (equals Yeah AA) --no backtracking
