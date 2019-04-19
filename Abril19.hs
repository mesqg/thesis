-- * NEW CODE FOR SOLVING IMPLICIT CONSTRAINTS
-- | Completely entail the set of Implicit constraints. This allows to try several orders in which to solve the set.
solveY :: YCs -> ImplicitTheory -> TcM (FcTmSubst,HsTySubst)
solveY ycs it = entailYcs (f ycs it) it
  `catchError` (\s-> throwError (s++" :solveY"))
   
  
-- TODO duplicated code! -}
-- | Completely entail a set of conversion constraints. Fail if not possible
entailYcs :: YCs -> ImplicitTheory -> TcM (FcTmSubst,HsTySubst)
entailYcs SN it = return mempty
entailYcs (xs :> x) it = do
  (subst,ty_subst) <- entailYct [] it (singletonSnocList x)
  (rest,ty_subst2) <- entailYcs (substInYCs ty_subst xs) it
  return (rest <> subst, ty_subst2 <> ty_subst)

entailYct :: [RnTyVar] ->  ImplicitTheory -> YCs -> TcM (FcTmSubst,HsTySubst)
entailYct untch theory yct = do
     x <- runSolverFirstM (go yct)
     return x
  where
    go (cs :> c) = do
      (ycs,subst1,ty_subst1) <- rightEntailsBacktracQ untch theory c
      case ycs of
        SN -> return (subst1,ty_subst1)
        otherwise -> do
         (subst2,ty_subst2) <- go  ycs
         return (subst2 <> subst1,ty_subst2 <> ty_subst1)

rightEntailsBacktracQ :: [RnTyVar] -> ImplicitTheory -> YCt
                      -> SolveM (YCs,FcTmSubst,HsTySubst)
rightEntailsBacktracQ untch it yct = liftSolveM (snocListChooseM (it:>CV_Nil) left_entail) >>= SolveM . selectListT
  where
    left_entail conv_axiom = leftEntailsIConv untch conv_axiom yct

leftEntailsIConv :: [RnTyVar] -> ConvAxiom -> YCt
            -> TcM (Maybe (YCs, FcTmSubst,HsTySubst))
leftEntailsIConv untch CV_Nil (YCt j (MCT ty1 ty2))
  | Right ty_subst <- unify [] [ty1 :~: ty2] = do
              x <- freshFcTmVar
              t0 <-  elabMonoTy (substInMonoTy ty_subst ty1)
              let id = FcTmAbs x t0 (FcTmVar x)
              return $ Just (SN, j |-> id,ty_subst)
  | otherwise = return Nothing              
leftEntailsIConv untch (UC (MCT a b) exp) (YCt j (MCT ty1 ty2))
  | Right ty_subst <- unify [] [ty1 :~: a]  = do
    x <- freshFcTmVar
    b' <- elabMonoTy b
    ty2' <- elabMonoTy ty2
    let yct = substInYCt ty_subst (YCt x (MCT b ty2))
    return $ Just (singletonSnocList yct , j |-> FcTmApp (FcTmVar x) exp,ty_subst)
  | Left _         <- unify [] [ty1 :~: a]  = return Nothing

  
-- | the f function in the specification. "prepares" the YCs to be solved directly later.
f :: YCs -> ImplicitTheory -> YCs
f ycs it = step2 (step1 ycs) it

-- | looking for the types reachable from `init`
reachable :: RnMonoTy -> ImplicitTheory -> [RnMonoTy]
reachable init it = aux [init] [] it
   where 
         aux :: [RnMonoTy]->[RnMonoTy]->ImplicitTheory->[RnMonoTy]
         aux acc q@(at:rest) (xs:>x) = case onestep (acc `union` q)  at x of 
             Just v -> aux acc (q++[v]) xs
             Nothing -> aux acc q xs
         aux acc (at:rest) SN = aux (at:acc) rest it
         aux acc [] _ = acc

         onestep :: [RnMonoTy]->RnMonoTy->ConvAxiom->Maybe RnMonoTy
         onestep old at (UC (MCT a b) exp)
          | Right ty_subst <- unify [] [at :~: a] =
              if (substInMonoTy ty_subst b) `elem` old then Nothing else
                Just (substInMonoTy ty_subst b)
          | Left _         <- unify [] [at :~: a] = Nothing
          
-- | propagates type to vars with only one incomming edge
step1 :: YCs -> YCs
step1 all@(rest:>conv@(YCt _ (MCT a (TyVar b))))
 | one_incomming (TyVar b) all 0 = (step1 (substInYCs ( b |-> a) rest)):>(substInYCt ( b |-> a) conv)
 | otherwise      = (step1 rest):>conv
 where one_incomming b SN 1 = True
       one_incomming b SN _ = False
       one_incomming b (xs:>x@(YCt _ (MCT _ c))) i = if c == b then one_incomming b xs (i+1) else one_incomming b xs i
step1 SN = SN

-- | look for a common type where they can meet
step2 :: YCs -> ImplicitTheory -> YCs
step2 ycs it = aux2 ycs it
 where
  aux2 SN _ = SN
  aux2 (rest:>conv@(YCt _ (MCT a b))) it = case b of
    TyVar x -> let new = (foldr intersect (reachable (head (incomming b ycs)) it) (map (\x->reachable x it) (tail (incomming b ycs))))!!0 in
     let subst = x |-> new in
       --step2 (substInYCs subst ycs) it
       (step2 (substInYCs subst rest) it):>(substInYCt subst conv)
    otherwise -> (aux2 rest it):>conv

  incomming :: RnMonoTy -> YCs -> [RnMonoTy]
  incomming at const = aux_in at [] const

  aux_in :: RnMonoTy -> [RnMonoTy] -> YCs -> [RnMonoTy]
  aux_in at acc (rest:>conv@(YCt _ (MCT a c))) = if at==c then aux_in at (a:acc) rest else aux_in at acc rest
  aux_in at acc SN = acc  
