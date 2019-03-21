
-- * Simple example with superclasses
-- ----------------------------------------------------------------------------

data Bool = True | False
data Chuck  = AA

implicit yamano : Bool Bool = \x. AA

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
instance Eq Chuck where
  equals = \z.\z.False

-- | Program expression
--(\z. compare (\x. \y. equals x y) z)
   \x. equals True x
