

data A = Algeria
data B = Benin
data C = Comoros
data D = Djibouti


implicit i2 : A ~> C = \x. Comoros
implicit i3 : C ~> B = \x. Benin  
implicit i1 : (a :: *) . (j:A ~> C) (i : C ~> B) => A ~> B = \x. i (j x)
  --implicit i3 : D C = \x. Comoros

class Eq a :: * where
  equals :: a -> a -> B

instance Eq C where
  equals = \x. \y. Benin    

-- | Program expression

--(\x. equals Algeria x)
(equals Algeria Benin)






