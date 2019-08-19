data Int = One
data Float = Pi
data DKK = K_dkk Float
(locimp \x.Pi  : Int ~> Float  in (K_dkk One))
:*: DKK
