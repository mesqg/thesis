-- * Simple example with superclasses
-- ----------------------------------------------------------------------------
data Wrapper (a::*) = W a
data Bool   = B1 | B2
data Chuck  = C1 | C2
data Fail = F
data Duplo  = D (Wrapper Chuck)

implicit i : Bool  ~> Fail = \x. F
implicit j : Fail ~> Bool = \x. B2
implicit d : Bool ~> Chuck= \x.C1
--implicit a : Bool ~> Chuck=\x. C2
implicit s : Fail ~> Chuck =\x.C2  
implicit k : (a::*) . (j : a ~> Fail )=> (Wrapper a) ~> (Wrapper Fail) = \x. case x of -- Substituing Fail by b leads to a loop. from onestep
  W s -> W (j s)
implicit t : .  => (Wrapper Bool) ~> (Wrapper Chuck) = \x.W C2

-- | Program expression

D (W B1)
