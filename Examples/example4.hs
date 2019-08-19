data Int = One
data Float = Pi | F28dot0 | F1dot2 | F3dot4 | F5dot25

data EUR = K_eur Float
data CHF = K_chf Float
data DKK = K_dkk Float
data USD = K_usd Float
data Wallet (a :: *) = K_wallet a a

(locimp \x.K_eur F28dot0 : DKK ~> EUR in
(locimp \x.K_eur F1dot2  : CHF ~> EUR in
(locimp \x.K_usd F3dot4  : EUR ~> USD in
(locimp (\x. case x of K_wallet x1 x2 -> K_wallet (j x1) (j x2) ) : (a::*)(b::*) . (j : a ~> b )=> (Wallet a) ~> (Wallet b) in
  (K_wallet (K_chf F5dot25) (locimp \x.Pi : Int ~> Float in (K_dkk One)))
))))
:*: Wallet USD
