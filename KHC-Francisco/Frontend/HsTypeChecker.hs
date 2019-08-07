{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} -- George says: God I hate this flag
--TODO: change the way implicits get into the expression: don't absorb terms
--TODO: merge the second step into something pretty: merge mustsTo, pathsFromTo,checkUniqueness and reachability
--TODO: why doesnt f return the ycs's?
--TODO: make sure the type variables from typing environment (f :: a -> a) are untouchables when unifying
module Frontend.HsTypeChecker (hsElaborate) where

import Frontend.HsTypes
import Frontend.HsRenamer
import Frontend.Conditions

import Backend.FcTypes

import Utils.Substitution
import Utils.FreeVars
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Annotated
import Utils.Ctx
import Utils.SnocList
import Utils.PrettyPrint
import Utils.Utils
import Utils.Errors
import Utils.Trace
import Utils.ListT

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Arrow (second)
import Data.List (nub,intersect,union)

-- * Create the typechecking environment from the renaming one
-- ------------------------------------------------------------------------------

-- | Build the initial typechecker environment from the renaming environment
buildInitTcEnv :: RnProgram -> RnEnv -> TcM ()
buildInitTcEnv pgm (RnEnv _rn_cls_infos dc_infos tc_infos {-conv_infos-}) = do -- GEORGE: Assume that the initial environment is completely empty (mempty mempty mempty)
  -- Prepopulate the environment with the (user-defined) data constructor information
  mapAssocListM_ (uncurry addDataConInfoTcM) $
    mapFstWithDataAssocList (\_ info -> hs_dc_data_con info) dc_infos
  -- Prepopulate the environment with the (user-defined) type constructor information
  mapAssocListM_ (uncurry addTyConInfoTcM)   $
    mapFstWithDataAssocList (\_ info -> hs_tc_ty_con   info) tc_infos
  -- Create and store in the environment all infos for type classes
  -- (and the constructors they give rise to) -- GEORGE: UPDATE THIS WHEN YOU ADD SUPERCLASSES
  buildStoreClsInfos pgm
  where
    buildStoreClsInfos :: RnProgram -> TcM ()
    buildStoreClsInfos (PgmExp {})   = return ()
    buildStoreClsInfos (PgmInst _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmImpl _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmData _ p) = buildStoreClsInfos p
    buildStoreClsInfos (PgmCls  c p) = case c of
      ClsD rn_cs rn_cls (rn_a :| _kind) rn_method method_ty -> do
        -- Generate And Store The TyCon Info
        rn_tc <- getUniqueM >>= return . HsTC . mkName (mkSym ("T" ++ (show $ symOf rn_cls)))
        let tc_info = HsTCInfo rn_tc [rn_a] (FcTC (nameOf rn_tc))
        addTyConInfoTcM rn_tc tc_info

        -- Generate And Store The DataCon Info
        rn_dc  <- getUniqueM >>= return . HsDC . mkName (mkSym ("K" ++ (show $ symOf rn_cls)))
        let dc_info = HsDCClsInfo rn_dc [rn_a] rn_tc rn_cs [method_ty] (FcDC (nameOf rn_dc))
        addDataConInfoTcM rn_dc dc_info

        -- Generate And Store The Class Info
        let cls_info = ClassInfo rn_cs rn_cls [rn_a] rn_method method_ty rn_tc rn_dc
        addClsInfoTcM rn_cls cls_info

        -- Continue with the rest
        buildStoreClsInfos p

-- | Add a renamed class name to the state
addClsInfoTcM :: RnClass -> ClassInfo -> TcM ()
addClsInfoTcM cls info = modify $ \s ->
  s { tc_env_cls_info = extendAssocList cls info (tc_env_cls_info s) }

-- | Add a renamed datacon name to the state
addDataConInfoTcM :: RnDataCon -> HsDataConInfo -> TcM ()
addDataConInfoTcM dc info = modify $ \s ->
  s { tc_env_dc_info = extendAssocList dc info (tc_env_dc_info s) }

-- | Add a renamed tycon name to the state
addTyConInfoTcM :: RnTyCon -> HsTyConInfo -> TcM ()
addTyConInfoTcM tc info = modify $ \s ->
  s { tc_env_tc_info = extendAssocList tc info (tc_env_tc_info s) }

-- * Type Checking Monad
-- ------------------------------------------------------------------------------

type TcM = UniqueSupplyT (ReaderT ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) (StateT TcEnv (ExceptT String (Writer Trace))))

type TcCtx = Ctx RnTmVar RnPolyTy RnTyVar Kind

data TcEnv = TcEnv { tc_env_cls_info :: AssocList RnClass   ClassInfo
                   , tc_env_dc_info  :: AssocList RnDataCon HsDataConInfo
                   , tc_env_tc_info  :: AssocList RnTyCon   HsTyConInfo
                   }

instance PrettyPrint TcEnv where
  ppr (TcEnv cls_infos dc_infos tc_infos)
    = braces $ vcat $ punctuate comma
    [ text "tc_env_cls_info" <+> colon <+> ppr cls_infos
    , text "tc_env_dc_info"  <+> colon <+> ppr dc_infos
    , text "tc_env_tc_info"  <+> colon <+> ppr tc_infos
    ]
  needsParens _ = False

-- | Transform info for a type constructor to the System F variant
elabHsTyConInfo :: HsTyConInfo -> FcTyConInfo
elabHsTyConInfo (HsTCInfo _tc as fc_tc) = FcTCInfo fc_tc (map rnTyVarToFcTyVar as)

elabHsDataConInfo :: HsDataConInfo -> TcM FcDataConInfo
elabHsDataConInfo (HsDCInfo _dc as tc tys fc_dc) = do
  fc_tc  <- lookupTyCon tc
  fc_tys <- map snd <$> extendTcCtxTysM as (mapM wfElabPolyTy tys)
  return $ FcDCInfo fc_dc (map rnTyVarToFcTyVar as) fc_tc fc_tys
elabHsDataConInfo (HsDCClsInfo _dc as tc super tys fc_dc) = do
  fc_tc  <- lookupTyCon tc
  fc_sc  <- extendTcCtxTysM as (mapM elabClsCt super)
  fc_tys <- map snd <$> extendTcCtxTysM as (mapM wfElabPolyTy tys)
  return $ FcDCInfo fc_dc (map rnTyVarToFcTyVar as) fc_tc (fc_sc ++ fc_tys)

buildInitFcAssocs :: TcM (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)
buildInitFcAssocs = do
  -- Convert the tyCon associations
  tc_infos <- gets tc_env_tc_info
  fc_tc_infos <- flip mapAssocListM tc_infos $ \(tc, tc_info) -> do
    fc_tc <- lookupTyCon tc
    return (fc_tc, elabHsTyConInfo tc_info)

  -- Convert the dataCon associations
  dc_infos <- gets tc_env_dc_info
  fc_dc_infos <- flip mapAssocListM dc_infos $ \(dc, dc_info) -> do
    fc_dc      <- lookupDataCon dc
    fc_dc_info <- elabHsDataConInfo dc_info
    return (fc_dc, fc_dc_info)

  return (fc_tc_infos, fc_dc_infos)

-- * Ensure that some things are not bound in the local context
-- ------------------------------------------------------------------------------

-- | Ensure something is not already bound in the local context
notInTcCtxM :: (PrettyPrint a, MonadReader ((ctx,ty),i) m, MonadError String m) => (ctx -> a -> Maybe t) -> a -> m ()
notInTcCtxM f x = ask >>= \((ctx,_),_) -> case f ctx x of
  Just {} -> throwErrorM (text "notInTcCtxM" <+> colon <+> ppr x <+> text "is already bound")
  Nothing -> return ()

-- | Ensure the type variable is not already bound
tyVarNotInTcCtxM :: RnTyVar -> TcM ()
tyVarNotInTcCtxM = notInTcCtxM lookupTyVarCtx

-- | Ensure the term variable is not already bound
tmVarNotInTcCtxM :: RnTmVar -> TcM ()
tmVarNotInTcCtxM = notInTcCtxM lookupTmVarCtx

-- * Lookup data and type constructors for a class
-- ------------------------------------------------------------------------------

-- GEORGE: 1. Rename TcEnv to TcGblEnv
--         2. It's exactly the same as lookupFcGblEnv. Abstract over both.

-- | Lookup something in the global environment
lookupTcEnvM ::  (Eq a, PrettyPrint a, MonadError String m, MonadState s m) => (s -> AssocList a b) -> a -> m b
lookupTcEnvM f x = gets f >>= \l -> case lookupInAssocList x l of
  Just y  -> return y
  Nothing -> throwErrorM (text "lookupTcEnvM" <+> colon <+> ppr x <+> text "is unbound")

-- | Lookup a type constructor
lookupTyCon :: RnTyCon -> TcM FcTyCon
lookupTyCon tc = hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc

-- | Lookup the kind of a type constructor
tyConKind :: RnTyCon -> TcM Kind
tyConKind tc = do
  info <- lookupTcEnvM tc_env_tc_info tc
  return (mkArrowKind (map kindOf (hs_tc_type_args info)) KStar)

-- | Lookup a data constructor
lookupDataCon :: RnDataCon -> TcM FcDataCon
lookupDataCon dc = hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc

-- | Lookup the kinds of the arguments
clsArgKinds :: RnClass -> TcM [Kind]
clsArgKinds cls = lookupTcEnvM tc_env_cls_info cls >>= return . map kindOf . cls_type_args

-- | Lookup the System Fc type constructor for a class
lookupClsTyCon :: RnClass -> TcM FcTyCon
lookupClsTyCon cls = do
  hs_tycon <- cls_tycon <$> lookupTcEnvM tc_env_cls_info cls
  hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info hs_tycon

-- | Lookup the System Fc data constructor for a class
lookupClsDataCon :: RnClass -> TcM FcDataCon
lookupClsDataCon cls = do
  hs_datacon <- cls_datacon <$> lookupTcEnvM tc_env_cls_info cls
  hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info hs_datacon

-- | Get the signature of a data constructor in pieces
dataConSig :: RnDataCon -> TcM ([RnTyVar], [RnPolyTy], RnTyCon) -- GEORGE: Needs to take into account the class case too
dataConSig dc = lookupTcEnvM tc_env_dc_info dc >>= \info ->
  return ( hs_dc_univ    info
         , hs_dc_arg_tys info
         , hs_dc_parent  info )

-- | Get the superclasses of a class
lookupClsSuper :: RnClass -> TcM RnClsCs
lookupClsSuper cls = cls_super <$> lookupTcEnvM tc_env_cls_info cls

-- | Get the parameter of the class
lookupClsParam :: RnClass -> TcM RnTyVar
lookupClsParam cls = do
  info <- lookupTcEnvM tc_env_cls_info cls
  case cls_type_args info of
    [a] -> return a
    _   -> throwErrorM (text "lookupClsParam")

-- * Type and Constraint Elaboration (With Well-formedness (well-scopedness) Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
wfElabMonoTy :: RnMonoTy -> TcM (Kind, FcType)
wfElabMonoTy (TyCon tc) = do
  kind  <- tyConKind tc
  fc_tc <- lookupTyCon tc
  return (kind, FcTyCon fc_tc)
wfElabMonoTy (TyApp ty1 ty2) = do
  (k1, fc_ty1) <- wfElabMonoTy ty1
  (k2, fc_ty2) <- wfElabMonoTy ty2
  case k1 of
    KArr k1a k1b
      | k1a == k2 -> return (k1b, FcTyApp fc_ty1 fc_ty2)
    _other_kind   -> throwErrorM (text "wfElabMonoTy" <+> colon <+> text "TyApp")
wfElabMonoTy (TyVar v) = do
  kind <- lookupTyVarN v
  return (kind, rnTyVarToFcType v)

-- | Elaborate a qualified type
wfElabQualTy :: RnQualTy -> TcM (Kind, FcType)
wfElabQualTy (QMono ty)    = wfElabMonoTy ty
wfElabQualTy (QQual ct ty) = do
  fc_ty1         <- wfElabClsCt ct
  (kind, fc_ty2) <- wfElabQualTy ty
  unless (kind == KStar) $
    throwErrorM (text "wfElabQualTy" <+> colon <+> text "QQual")
  return (KStar, mkFcArrowTy fc_ty1 fc_ty2)

-- | Elaborate a class constraint
wfElabClsCt :: RnClsCt -> TcM FcType
wfElabClsCt (ClsCt cls ty) = do
  (ty_kind, fc_ty) <- wfElabMonoTy ty
  clsArgKinds cls >>= \case
    [k] | k == ty_kind -> do
      fc_tc <- lookupClsTyCon cls
      return (FcTyApp (FcTyCon fc_tc) fc_ty)
    _other_kind -> throwErrorM (text "wfElabCtr" <+> colon <+> text "CtrClsCt")

-- | Elaborate a constraint
wfElabCtr :: RnCtr -> TcM FcType
wfElabCtr (Ctr []  []     ct) = wfElabClsCt ct
wfElabCtr (Ctr []  (c:cs) ct) = mkFcArrowTy <$> wfElabClsCt c <*> wfElabCtr (Ctr [] cs ct)
wfElabCtr (Ctr ((a :| k):as) cs  ct) = do
  tyVarNotInTcCtxM a
  FcTyAbs (rnTyVarToFcTyVar a) <$> (extendCtxTyN a k (wfElabCtr (Ctr as cs ct)))

-- | Elaborate a list of class constraints
wfElabClsCs :: RnClsCs -> TcM [FcType]
wfElabClsCs = mapM wfElabClsCt

-- | Elaborate a polytype
wfElabPolyTy :: RnPolyTy -> TcM (Kind, FcType)
wfElabPolyTy (PQual ty) = wfElabQualTy ty
wfElabPolyTy (PPoly (a :| _) ty) = do
  tyVarNotInTcCtxM a {- GEORGE: ensure is unbound -}
  (kind, fc_ty) <- extendCtxTyN a (kindOf a) (wfElabPolyTy ty)
  unless (kind == KStar) $
    throwErrorM (text "wfElabPolyTy" <+> colon <+> text "PPoly")
  return (KStar, FcTyAbs (rnTyVarToFcTyVar a) fc_ty)

-- * Type and Constraint Elaboration (Without Well-scopedness Check)
-- ------------------------------------------------------------------------------

-- | Elaborate a monotype
elabMonoTy :: RnMonoTy -> TcM FcType
elabMonoTy (TyCon tc)      = FcTyCon <$> lookupTyCon tc
elabMonoTy (TyApp ty1 ty2) = FcTyApp <$> elabMonoTy ty1 <*> elabMonoTy ty2
elabMonoTy (TyVar v)       = return (rnTyVarToFcType v)

-- | Elaborate a class constraint (DO NOT CHECK WELL-SCOPEDNESS)
elabClsCt :: RnClsCt -> TcM FcType
elabClsCt (ClsCt cls ty)
  = FcTyApp <$> (FcTyCon <$> lookupClsTyCon cls) <*> elabMonoTy ty

-- | Elaborate a constraint (DO NOT CHECK WELL-SCOPEDNESS)
-- GEORGE: Check kinds though!!
elabCtr :: RnCtr -> TcM FcType
elabCtr (Ctr []  []     ct) = elabClsCt ct
elabCtr (Ctr []  (c:cs) ct) = mkFcArrowTy <$> (elabClsCt c) <*> elabCtr (Ctr [] cs ct)
elabCtr (Ctr (a:as) cs  ct) = FcTyAbs (rnTyVarToFcTyVar (labelOf a)) <$> elabCtr (Ctr as cs ct)

-- * Constraint Solving Monad
-- ------------------------------------------------------------------------------

newtype SolveM a = SolveM (ListT TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState TcEnv, MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)), MonadError String )

instance MonadUnique SolveM where
  getUniqueSupplyM = liftSolveM getUniqueSupplyM

-- | Lift TcM into SolveM
liftSolveM :: TcM a -> SolveM a
liftSolveM m = SolveM (lift m)

-- | Get the first solution
runSolverFirstM :: SolveM a -> TcM a
runSolverFirstM (SolveM m) = firstListT m

-- * Constraint store
-- ------------------------------------------------------------------------------

-- | ConstraintStore containing both the equality constraints and named class constraints
-- UPDATED
data ConstraintStore = CS EqCs YCs AnnClsCs

instance Semigroup ConstraintStore where
  (<>) (CS eqs1 ycs1 ccs1) (CS eqs2 ycs2 ccs2)
    = CS (eqs1 <> eqs2) (ycs1 <> ycs2) (ccs1 <> ccs2)

instance Monoid ConstraintStore where
  mempty = CS mempty mempty mempty

-- | Type inference generation monad
newtype GenM a = GenM (StateT ConstraintStore TcM a)
  deriving ( Functor, Applicative, Monad
           , MonadState ConstraintStore, MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)), MonadError String )

-- GEORGE: All this is bad. We should not store the unique supply within the
-- global environment, rather wrap our monads with the UniqueSupplyT transformer
instance MonadUnique GenM where
  getUniqueSupplyM = liftGenM getUniqueSupplyM

-- | Get out of the constraint generation monad
runGenM :: GenM a -> TcM (a, EqCs, YCs, AnnClsCs)
runGenM (GenM m) = do
    (v , (CS eqs ics ccs)) <- runStateT m mempty
    return (v, eqs, ics, ccs)

-- | Lift TcM into GenM
liftGenM :: TcM a -> GenM a
liftGenM m = GenM (StateT (\cs -> m >>= \x -> return (x, cs)))

-- | Add some equality constraints in the constraint store
storeEqCs :: EqCs -> GenM ()
storeEqCs cs = modify (\(CS eqs ycs ccs) -> CS (cs ++ eqs) ycs ccs)

-- | Add some equality constraints in the constraint store
storeYCs ::YCs -> GenM ()
storeYCs cs = modify (\(CS eqs ycs ccs) -> CS eqs (cs <> ycs) ccs)

-- | Add some (variable-annotated) class constraints in the constraint store
storeAnnCts :: AnnClsCs -> GenM ()
storeAnnCts cs = modify (\(CS eqs ycs ccs) -> CS eqs ycs (mappend ccs cs))

-- | Add many type variables to the typing context
extendTcCtxTysM :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => [RnTyVar] -> m a -> m a
extendTcCtxTysM []     m = m
extendTcCtxTysM (a:as) m = extendCtxTyN a (kindOf a) (extendTcCtxTysM as m) -- just a left fold..

-- | Set the typing environment
setTcCtxTmM :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => TcCtx -> m a -> m a
setTcCtxTmM ctx = local (\((_,ty),i) -> ((ctx,ty),i))

-- * Term Elaboration
-- ------------------------------------------------------------------------------

-- | Freshen up a list of type variables. Return
--   a) the list of fresh variables (NB: same length as input)
--   b) the substitution from the old to the fresh ones
freshenRnTyVars :: [RnTyVar] -> TcM ([RnTyVar], HsTySubst)
freshenRnTyVars tvs = do
  new_tvs <- mapM freshRnTyVar (map kindOf tvs)
  let subst = buildRnSubst (zipExact tvs new_tvs)
  return (new_tvs, subst)

-- | Instantiate a polytype with fresh unification variables
instPolyTy :: RnPolyTy -> TcM ([RnTyVar], RnClsCs, RnMonoTy)
instPolyTy poly_ty = do
  (bs, subst) <- freshenRnTyVars (map labelOf as)
  let new_cs = substInClsCs subst cs
  let new_ty = substInMonoTy subst ty
  return (bs, new_cs, new_ty)
  where
    (as, cs, ty) = destructPolyTy poly_ty

-- | Generate a number of fresh dictionary variables
genFreshDictVars :: MonadUnique m => Int -> m [DictVar]
genFreshDictVars n = replicateM n freshDictVar

-- | Annotate a list of constraints with a fresh dictionary variables
-- annotateCts :: RnCts -> TcM ([DictVar], AnnCts)
-- annotateCts cs = do
--   ds <- genFreshDictVars (length cs)
--   return (ds, (listToSnocList ds) |: (listToSnocList cs))

-- | Annotate a list of class constraints with a fresh dictionary variables
annotateClsCs :: RnClsCs -> TcM ([DictVar], SimpleProgramTheory)
annotateClsCs cs = do
  ds <- genFreshDictVars (length cs)
  return (ds, (listToSnocList ds) |: (listToSnocList cs))

-- | Elaborate a term
elabTerm :: RnTerm -> GenM (RnMonoTy, FcTerm)
elabTerm (TmApp tm1 tm2)   = elabTmApp tm1 tm2
elabTerm (TmAbs x tm)      = elabTmAbs x tm
elabTerm (TmVar x)         = elabTmVar x
elabTerm (TmCon dc)        = liftGenM (elabTmCon dc)
elabTerm (TmLet x tm1 tm2) = elabTmLet x tm1 tm2
elabTerm (TmLocImp i tm)   = elabTmLocImp i tm
elabTerm (TmCase scr alts) = elabTmCase scr alts

-- | Elaborate a term application UPDATE: add a var for the implicits, add conv constrain
-- UPDATED!
elabTmApp :: RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmApp tm1 tm2 = do
  j <- freshFcTmVar
  --let j = FcTmVar newTmVar
  (ty1, fc_tm1) <- elabTerm tm1
  (ty2, fc_tm2) <- elabTerm tm2
  a <- TyVar <$> freshRnTyVar KStar
  b <- TyVar <$> freshRnTyVar KStar
  pair <- ask
  storeEqCs [mkRnArrowTy [b] a :~: ty1]
  --storeEqCs [mkRnArrowTy [b] a :~: ty1]
  storeYCs $ constrYCs j ty2 b fc_tm2 (fst (snd pair))
  (CS e y an) <- get -- TODO? ugly 
  put (CS e y (substInAnnClsCs (ty2 |-> b) an))
  return (a, FcTmApp fc_tm1 (FcTmVar j)) -- add fresh FcTmVar in between


-- | Elaborate a lambda abstraction
elabTmAbs :: RnTmVar -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmAbs x tm = do
  liftGenM (tmVarNotInTcCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty, fc_tm) <- extendTC x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm
  let result = FcTmAbs (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm
  return (mkRnArrowTy [TyVar tv] ty, result)

-- | Elaborate a term variable
elabTmVar :: RnTmVar -> GenM (RnMonoTy, FcTerm)
elabTmVar x = do
  poly_ty     <- liftGenM (lookupTmVarN x)
  (bs,cs,ty)  <- liftGenM (instPolyTy poly_ty)
  _           <- extendTcCtxTysM bs $ liftGenM (wfElabClsCs cs) -- Check well formedness of the constraints
  (ds,ann_cs) <- liftGenM (annotateClsCs cs)
  storeAnnCts $ ann_cs -- store the constraints
  let fc_ds = map FcTmVar ds         -- System F representation
  let fc_bs = map rnTyVarToFcType bs -- System F representation
  let fc_tm = fcTmApp (fcTmTyApp (rnTmVarToFcTerm x) fc_bs) fc_ds
  return (ty, fc_tm)

-- | Elaborate a let binding (monomorphic, recursive)
elabTmLet :: RnTmVar -> RnTerm -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmLet x tm1 tm2 = do
  liftGenM (tmVarNotInTcCtxM x) {- ensure not bound -}
  tv <- freshRnTyVar KStar
  (ty1, fc_tm1) <- extendTC x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm1
  (ty2, fc_tm2) <- extendTC x (monoTyToPolyTy (TyVar tv)) $ elabTerm tm2 -- could have also passed ty1 but it is the same
  storeEqCs [TyVar tv :~: ty1]
  let fc_tm = FcTmLet (rnTmVarToFcTmVar x) (rnTyVarToFcType tv) fc_tm1 fc_tm2
  return (ty2, fc_tm)

  -- | Elaborate a let binding (monomorphic, recursive)
elabTmLocImp :: RnIConv -> RnTerm -> GenM (RnMonoTy, FcTerm)
elabTmLocImp (ICC name pct@(PCT vars pairs monoty@(MCT a b)) exp) tm =
 case a of
    (TyVar x) -> throwError ("invalid implicit "++ (render$ppr name)++ "Type variables can't be the rhs of the final convmonoty")
    otherwise -> do
      let (rnPHs,types) = aux pairs
    -- probably TODO in elabTermWithSig
      pair <- ask
      let ft = snd (snd pair)
      elab_exp <- emptyIT (extendTCs rnPHs types (liftGenM (elabTermWithSig [] ft exp (monoTyToPolyTy (mkRnArrowTy [a] b)))) )
      cax <- liftGenM (do
        fc_a <- elabMonoTy a
        fc_b <- elabMonoTy b
        --let ugly = (FcTmTyApp elab_exp fc_a)
        case pairs of
               [] -> return (MCA monoty elab_exp)
               otherwise -> return (PCA pct elab_exp))
      (ty, fc_tm) <- extendIT cax (elabTerm tm)
      return (ty, fc_tm)
      
  where
    aux :: [(RnTmVar,RnMonoConvTy)] -> ([RnTmVar],[RnPolyTy])
    aux pairs = (map fst pairs, map (\(MCT a b) -> monoTyToPolyTy (mkRnArrowTy [a] b)) (map snd pairs))
    
-- | Elaborate a data constructor
elabTmCon :: RnDataCon -> TcM (RnMonoTy, FcTerm)
elabTmCon dc = do
  (bs, arg_tys, tc) <- freshenDataConSig dc
  fc_dc <- lookupDataCon dc

  let mono_ty = mkRnArrowTy arg_tys (mkTyConApp tc (map TyVar bs))                 -- Haskell monotype
  let fc_tm = fcTmTyApp (FcTmDataCon fc_dc) (rnTyVarsToFcTypes bs) -- System F term

  return (mono_ty, fc_tm)

freshenDataConSig :: RnDataCon -> TcM ([RnTyVar], [RnMonoTy], RnTyCon)
freshenDataConSig dc = do
  (as, poly_arg_tys, tc) <- dataConSig dc
  (bs, subst) <- freshenRnTyVars as                              -- Freshen up the universal type variables
  arg_tys     <- polyTysToMonoTysM $ map (substInPolyTy subst) poly_arg_tys -- Substitute in the argument types
  return (bs, arg_tys, tc)

-- | Cast a list of polytypes to monotypes. Fail if not possible
polyTysToMonoTysM :: MonadError String m => [PolyTy a] -> m [MonoTy a]
polyTysToMonoTysM []       = return []
polyTysToMonoTysM (ty:tys) = case polyTyToMonoTy ty of
  Just mono_ty -> fmap (mono_ty:) (polyTysToMonoTysM tys)
  Nothing      -> throwErrorM (text "polyTysToMonoTysM" <+> colon <+> text "non-monotype")

-- | Elaborate a case expression UPDATED
elabTmCase :: RnTerm -> [RnAlt] -> GenM (RnMonoTy, FcTerm)
elabTmCase scr alts = do
  (scr_ty, fc_scr) <- elabTerm scr               -- Elaborate the scrutinee
  b  <- TyVar <$> freshRnTyVar KStar 
  rhs_ty  <- TyVar <$> freshRnTyVar KStar        -- Generate a fresh type variable for the result
  fc_alts <- mapM (elabHsAlt b rhs_ty) alts -- Check the alternatives
  pair <- ask
  j <- freshFcTmVar
  storeYCs $ constrYCs j scr_ty b fc_scr (fst (snd pair)) 
  return (rhs_ty, FcTmCase (FcTmVar j) fc_alts)

-- | Elaborate a case alternative
elabHsAlt :: RnMonoTy {- Type of the scrutinee -}
          -> RnMonoTy {- Result type           -}
          -> RnAlt    {- Case alternative      -}
          -> GenM FcAlt
elabHsAlt b res_ty (HsAlt (HsPat dc xs) rhs) = do 
  (as, orig_arg_tys, tc) <- liftGenM (dataConSig dc) -- Get the constructor's signature
  fc_dc <- liftGenM (lookupDataCon dc)               -- Get the constructor's System F representation
  (bs, ty_subst) <- liftGenM (freshenRnTyVars as)               -- Generate fresh universal type variables for the universal tvs
  let arg_tys = map (substInPolyTy ty_subst) orig_arg_tys       -- Apply the renaming substitution to the argument types
  (rhs_ty, fc_rhs) <- extendTCs xs arg_tys (elabTerm rhs)   -- Type check the right hand side
  storeEqCs [ b :~: foldl TyApp (TyCon tc) (map TyVar bs)  -- The scrutinee type must match the pattern type
            , res_ty :~: rhs_ty ]                               -- All right hand sides should be the same
  return (FcAlt (FcConPat fc_dc (map rnTmVarToFcTmVar xs)) fc_rhs)

-- | Covert a renamed type variable to a System F type
rnTyVarToFcType :: RnTyVar -> FcType
rnTyVarToFcType = FcTyVar . rnTyVarToFcTyVar

-- | Covert a list of renamed type variables to a list of System F types
rnTyVarsToFcTypes :: [RnTyVar] -> [FcType]
rnTyVarsToFcTypes = map rnTyVarToFcType

-- | Covert a renamed term variable to a System F term
rnTmVarToFcTerm :: RnTmVar -> FcTerm
rnTmVarToFcTerm = FcTmVar . rnTmVarToFcTmVar

-- * Type Unification
-- ------------------------------------------------------------------------------

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError String m => [RnTyVar] -> EqCs -> m HsTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- go (one_step untchs) eqs
  = do subst2 <- unify untchs (substInEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = throwErrorM $ vcat [ text "Unification failed."
                                   , text "Residual constraints" <+> colon <+> ppr eqs
                                   , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: [RnTyVar] -> EqCt -> Maybe (HsTySubst, EqCs)
    one_step _us (TyVar v1 :~: TyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step us (TyVar v :~: ty)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
      | otherwise                        = Nothing
    one_step us (ty :~: TyVar v)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
      | otherwise                        = Nothing
    one_step _us (TyCon tc1 :~: TyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
      | otherwise  = Nothing
    one_step _us (TyApp ty1 ty2 :~: TyApp ty3 ty4)
      = Just (mempty, [ty1 :~: ty3, ty2 :~: ty4])
    one_step _us (TyCon {} :~: TyApp {}) = Nothing
    one_step _us (TyApp {} :~: TyCon {}) = Nothing

    go :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
    go _p []     = Nothing
    go  p (x:xs) | Just y <- p x = Just (y, xs)
                 | otherwise     = second (x:) <$> go p xs

-- | Occurs Check (true means OK)
occursCheck :: RnTyVar -> RnMonoTy -> Bool
occursCheck _ (TyCon {})      = True
occursCheck a (TyApp ty1 ty2) = occursCheck a ty1 && occursCheck a ty2
occursCheck a (TyVar b)       = a /= b

-- * NEW CODE FOR SOLVING IMPLICIT CONSTRAINTS
-- | Completely entail the set of Implicit constraints. This allows to try several orders in which to solve the set.

--Cheap solveY because bypasses f. For solving conversions with conditions. Ugly and a TODO.
csolveY :: YCs -> TcM (FcTmSubst,HsTySubst)
csolveY ycs = do
  --checkUniqueness ycs
  (fctmsubst,tysubst2) <- auxSolveY []  ycs
  return (fctmsubst,tysubst2)
  `catchError` (\s-> throwError (s++" :csolveY"))

solveY :: YCs -> TcM (FcTmSubst,HsTySubst)
solveY ycs = do
  tysubst1 <- f ycs
  (fctmsubst,tysubst2) <- auxSolveY []  (substInYCs mempty  tysubst1 ycs)
  return (fctmsubst,tysubst1<>tysubst2)
  `catchError` (\s-> throwError (s++" :solveY"))

auxSolveY untch ycs = entailYcs [] ycs
     where
   -- | Completely entail a set of conversion constraints. Failed if not possible
   entailYcs :: [RnTyVar] -> YCs -> TcM (FcTmSubst,HsTySubst)
   entailYcs _ SN = return mempty
   entailYcs untch (xs :> x) = do
     (tmsubst,ty_subst) <- entailYct untch (singletonSnocList x)
     (rest,ty_subst2) <- entailYcs untch (substInYCs tmsubst ty_subst xs)
     return (rest <> tmsubst, ty_subst2 <> ty_subst)
    
   entailYct :: [RnTyVar] -> YCs -> TcM (FcTmSubst,HsTySubst)
   entailYct untch yct = do
        x <- runSolverFirstM (go [] yct)
        return  x
     where
       go beens (cs :> c) = do
         (ycs,subst1,ty_subst1,nbeens) <- rightEntailsBacktracQ beens c
         case ycs of
           SN -> return (subst1,ty_subst1)
           otherwise -> do
            (subst2,ty_subst2) <- go nbeens ycs
            return (subst2 <> subst1,ty_subst2 <> ty_subst1)

   rightEntailsBacktracQ :: [RnMonoTy] -> YCt
                         -> SolveM (YCs,FcTmSubst,HsTySubst,[RnMonoTy])
   rightEntailsBacktracQ beens yct@(YCt _ _ _ it) = 
     liftSolveM (snocListChooseM (it:>CV_Nil) left_entail) >>= SolveM . selectListT
     where
       left_entail conv_axiom = leftEntailsIConv beens conv_axiom yct --TODO!

   leftEntailsIConv :: [RnMonoTy] -> ConvAxiom -> YCt
               -> TcM (Maybe (YCs, FcTmSubst,HsTySubst,[RnMonoTy]))
   leftEntailsIConv beens CV_Nil (YCt j (MCT ty1 ty2) exp _)
     | Right ty_subst <- unify [] [ty1 :~: ty2] = do
                 return $ Just (SN, j |-> exp,ty_subst,beens)
     | otherwise = return Nothing              
   leftEntailsIConv beens (MCA (MCT a b) exp) (YCt j (MCT ty1 ty2) tm it)
     | elem b beens = return Nothing
     | Right ty_subst <- unify [] [ty1 :~: a]  = do
       b' <- elabMonoTy b
       ty2' <- elabMonoTy ty2
       let yct = case tm of
             FcDummyTerm -> substInYCt mempty ty_subst (YCt j (MCT b ty2) exp it)
             otherwise  -> substInYCt mempty ty_subst (YCt j (MCT b ty2) (FcTmApp exp tm) it)
       return $ Just (singletonSnocList yct , mempty,ty_subst,b:beens)
     | otherwise  = return Nothing
   -- If the conversion has type vars in the resulting type, we unify it with the end type ty2. Fail if not possible.    
   leftEntailsIConv beens ca@(PCA (PCT vars pairs (MCT a b)) exp) yct@(YCt j (MCT ty1 ty2) tm it)
     | Right _ <- unify [] [ty1 :~: a]  = do
       (ca'@(PCA (PCT vars' pairs' (MCT a' b')) exp'),f_sub) <- case (ftyvsOf b) of
         []        -> freshenCA ca
         otherwise -> 
           case (do {unify [] [ty2 :~: b]}) of
             Right uniB -> do
               fc_uniB <- elabHsTySubst uniB
               let ca_u = (PCA (PCT vars (substInConds uniB pairs) (MCT a ty2)) (substFcTyInTm fc_uniB exp))
               (exp,sub)<-freshenCA ca_u
               return (exp,sub <> uniB)
             otherwise -> throwError "Too much freedom"
       ty_subst <- unify [] [ty1 :~: a']
       fc_ty_subst <- elabHsTySubst ty_subst
       ycs <- prepare (PCA (PCT vars' (substInConds ty_subst pairs') (MCT ty1 b')) (substFcTyInTm fc_ty_subst exp)) (xcludeSelf ca it)
       (tm_subst,ty_subst2) <- auxSolveY [] ycs
       let nb = (substInMonoTy (ty_subst2 <> ty_subst <> f_sub) b)
       let yct = case tm of
             FcDummyTerm -> substInYCt mempty ty_subst (YCt j (MCT nb ty2) (substFcTmInTm tm_subst exp') it)
             otherwise   -> substInYCt mempty ty_subst (YCt j (MCT nb ty2) (FcTmApp (substFcTmInTm tm_subst exp') tm) it)
       return $ case elem nb beens of
         True  -> Nothing
         False -> Just (singletonSnocList  yct , mempty , ty_subst2 <> ty_subst <> f_sub,nb:beens)
       `catchError` (\s-> return Nothing)
     | otherwise  = return Nothing
     where
         xcludeSelf :: ConvAxiom -> ImplicitTheory -> ImplicitTheory
         xcludeSelf ca (x:>xs)
           | ca == xs  = x
           | otherwise = (xcludeSelf ca x):>xs
         --xcludeSelf _ SN = SN
         freshenCA :: ConvAxiom -> TcM (ConvAxiom, HsTySubst)
         freshenCA ca@(PCA (PCT labVars pairs mct) exp) = do
         (f_vars,f_sub) <- freshenRnTyVars (labelOf labVars)
         let mct' = substInMCT f_sub mct
         let pairs' = substInConds f_sub pairs
         let labVars' = zipWith (:|) f_vars (dropLabel labVars)
         f_fc_sub <- (elabHsTySubst f_sub)
         return (PCA (PCT labVars' pairs' mct') (substFcTyInTm f_fc_sub exp),f_sub)
         

-- | prepares the conditions of conditional ITC to check entailalibity
prepare :: ConvAxiom -> ImplicitTheory -> TcM (YCs)
prepare = aux_p SN
     where
       aux_p ycs (PCA (PCT v (x@(var,mct):xs) m) exp) it =
         let j = rnTmVarToFcTmVar var in     
         let yct  = YCt j mct FcDummyTerm it in --TODO? not pretty but not the worst?
         aux_p (ycs:>yct) (PCA (PCT v xs m) exp) it
       aux_p ycs (PCA (PCT _ [] m) exp) _ = return ycs

-- | the f function in the specification. "prepares" the YCs to be solved directly later.
f :: YCs -> TcM(HsTySubst)
f ycs = let subst1 = (step1 ycs ycs) in
  do
    subst2 <- step2 (substInYCs mempty subst1 ycs)
    let nycs = (substInYCs mempty (subst2<>subst1) ycs)
    checkUniqueness nycs
    return (subst1 <> subst2)
     where
  -- | propagates type to vars with only one incomming edge

  step1 :: YCs -> YCs-> HsTySubst
  step1 (rest:>conv@(YCt _ (MCT a (TyVar b)) _ _)) all
   | same_incomming (TyVar b) all a = (b |-> a) <> (step1 (substInYCs mempty (b |-> a) rest) (substInYCs mempty (b |-> a) all))
   | otherwise      = (step1 rest all)
   where same_incomming b SN _ = True
         same_incomming b (xs:>x@(YCt _ (MCT a' c) _ _)) a = if c == b then (if a'==a then same_incomming b xs a else False) else same_incomming b xs a
  step1 (rest:>conv) all = (step1 rest all)
  step1 SN _ = mempty

  -- | look for a common type where they can meet
  step2 :: YCs -> TcM(HsTySubst)
  step2 ycs =aux2 ycs ycs
   where
    aux2 :: YCs -> YCs -> TcM(HsTySubst)
    aux2 SN _ = return mempty
    aux2 (rest:>conv@(YCt _ (MCT a b) _ it)) all = case b of
        (TyVar x) -> let source = incomming b ycs in case foldr (++) [] (map ftyvsOf source) of
          [] ->do
             rh <- (reachable (head source) it)
             rr <- (mapM (\x-> reachable x it) (tail source))
             let meet = (foldr intersect rh rr) in
               do
                 dom <- dominator  source meet  it
                 subst2 <- aux2 (substInYCs mempty (x |-> dom) all) (substInYCs mempty (x |-> dom) all)
                 return (subst2<>(x |-> dom))
          otherwise -> aux2 rest all
        otherwise -> aux2 rest all {- -> do
          subst <- aux2 rest all
          return subst -}

        
  -- | looking for the types reachable from `init`
  reachable :: RnMonoTy -> ImplicitTheory -> TcM [RnMonoTy]
  reachable init it = aux [] [init] it
    where 
         aux :: [RnMonoTy]->[RnMonoTy]->ImplicitTheory-> TcM [RnMonoTy]
         aux acc q@(at:rest) (xs:>x) = do
           os <- (onestep at x it)
           case os  of 
             Just v -> aux acc (q++(filter (\x -> not $ x `elem` (acc `union` q)) v)) xs
             Nothing -> aux acc q xs
         aux acc (at:rest) SN = aux (at:acc) rest it
         aux acc [] _ = return acc


  incomming :: RnMonoTy -> YCs -> [RnMonoTy]
  incomming at const = aux_in at [] const

  aux_in :: RnMonoTy -> [RnMonoTy] -> YCs -> [RnMonoTy]
  aux_in at acc (rest:>conv@(YCt _ (MCT a c) _  _)) = if at==c then aux_in at (a:acc) rest else aux_in at acc rest
  aux_in at acc SN = acc
  -- | Find the dominator of a set of types.
  {-
     If type X is not dominated either it is the dominator or none exist;
     If type X is dominated types in S, either the dominator is in S or none exists
  -}
  dominator :: [RnMonoTy] -> [RnMonoTy] -> ImplicitTheory -> TcM (RnMonoTy)
  dominator _              []            _  = throwError ("no overlap")
  dominator _              [x]           _  = return x
  dominator sources@(x:xs) sinks@(y:ys)  it =  do
    fst <- (mustsTo sources y it)
    oth <- (mapM (\z-> mustsTo sources z it) ys)
    let b = (foldr intersect fst oth ) in
      case b of
        [x] -> return x
        otherwise -> throwError ("no dominator from> "++(render$ppr sources))
  
  mustsTo :: [RnMonoTy] -> RnMonoTy -> ImplicitTheory -> TcM [RnMonoTy]
  mustsTo sources@(x:xs) to it = do
    h <- (pathsFromTo [] [[x]] to it it)
    othersources <- (mapM (\init-> (pathsFromTo [] [[init]] to it it)) xs)
    let h' = case h of
          []   ->  []
          --[[]] ->  []
          [el] ->  el
          (fst:rest) -> foldr intersect fst rest
    let o' = case othersources of
          []   ->  []
          --[[]] ->  []
          [el] ->  el
          (fst:rest) -> foldr intersect fst rest
    return$foldr intersect h' o' 


--TODO! Possibility of b being type var...
onestep :: RnMonoTy->ConvAxiom->ImplicitTheory -> TcM (Maybe [RnMonoTy])
onestep at (MCA (MCT a b) exp) _
 | Right ty_subst <- unify [] [at :~: a] =
     --if (substInMonoTy ty_subst b) `elem` old then return Nothing else
       return$Just [(substInMonoTy ty_subst b)]
 | Left _         <- unify [] [at :~: a] = return Nothing
onestep at ca@(PCA pct@(PCT vars pairs mono@(MCT a b)) exp) it 
  | Right ty_subst <-  unify [] [at :~: a] = case (ftyvsOf (substInMonoTy ty_subst b)) of
      []        -> do
        isSat <- (sat ca it ty_subst)
        if isSat then return$ Just [(substInMonoTy ty_subst b)] else return Nothing
      [var] -> do --super restricted. conds must be a single cond (ftyvarOf a)~>(ftyvarOf b)=>a ~> b
        ycs <- prepare ca it
        return$ Just $ map (\x -> (substInMonoTy (var |-> x) b)) (aux_match (substInYCs mempty ty_subst ycs) it [])
        --match yct against all monoconv types. get substs for each yct. substs present in all yct are okay: too strong.. enough that b |-> same
          where
            aux_match :: YCs -> ImplicitTheory -> [RnMonoTy] -> [RnMonoTy]
            aux_match ycs@(SN:>conv@(YCt _ (MCT za zc) _  _)) (x:>(MCA (MCT a b) exp)) acc = if (za == a) then aux_match ycs x (b:acc) else aux_match ycs x acc
            aux_match ycs (x:>(PCA _ _)) acc = aux_match ycs x acc
            aux_match ycs SN acc            = acc

  | otherwise = return Nothing   

--TODO! Think its done somewhere else
sat :: ConvAxiom -> ImplicitTheory -> HsTySubst -> TcM Bool
sat ca it sub = do
        ycs <- prepare ca it
        let nycs = substInYCs mempty sub ycs
        checkUniqueness nycs
        return True
        `catchError` (\s -> return False)

pathsFromTo :: [[RnMonoTy]]->[[RnMonoTy]]-> RnMonoTy ->ImplicitTheory-> ImplicitTheory -> TcM [[RnMonoTy]]
pathsFromTo done_paths paths@(this@(at:rest):otherpaths) to (xs:>x) it
 | at == to = pathsFromTo (this:done_paths) otherpaths to it it
 | otherwise = do
     res <- (onestep at x it)
     case  res of 
       Just nexts -> let os = filter (\x -> not $ x `elem` this) nexts in
                  let news = {-filter (\x -> not $ x `elem` otherpaths)-} (map (\x -> x:this ) os) in
                  pathsFromTo done_paths (this:(news++otherpaths)) to xs it
       Nothing -> pathsFromTo done_paths paths to xs it
pathsFromTo done_paths paths@(this@(at:rest):otherpaths) to SN it 
   | at == to = pathsFromTo (this:done_paths) otherpaths to it it
   | otherwise = pathsFromTo done_paths otherpaths to it it
pathsFromTo done_paths [] q _ _= do
  return done_paths 

checkUniqueness :: YCs -> TcM ()
checkUniqueness ycs@(rest:>conv@(YCt _ (MCT (TyVar a) b) _  it)) = throwError "Ambiguous program: unable to decide the type of the conversions needed."
checkUniqueness ycs@(rest:>conv@(YCt _ (MCT c (TyVar a)) exp  it)) = throwError ("VAR>  "++(render$ppr c)++" to "++(render$ppr a)++" IT> "++(show it)++" EXP> "++(render$ppr exp))
checkUniqueness ycs@(rest:>conv@(YCt _ (MCT a c) exp  it))= do
        paths <- pathsFromTo [] [[a]] c it it
        case paths of
          []   ->  if a==c then checkUniqueness rest else throwError ("no path from "++(render$ppr a)++" to "++(render$ppr c)++" IT> "++(show it)++" EXP> "++(render$ppr exp))
          --[[]] ->  throwError "2"
          [el] ->  checkUniqueness rest 
          (fst:rest) -> throwError ("ambiguous conversions from "++(render$ppr a)++" to "++(render$ppr c))
checkUniqueness SN = return ()

-- * Overlap Checking
-- ------------------------------------------------------------------------------

overlapCheck :: MonadError String m => FullTheory -> RnClsCt -> m ()
overlapCheck theory cls_ct@(ClsCt cls1 ty1) = case lookupSLMaybe overlaps (theory_inst theory) of -- We only care about the instance theory
  Just msg -> throwErrorM msg
  Nothing  -> return ()
  where
    overlaps (_ :| ctr)
      | ClsCt cls2 ty2 <- ctrHead ctr
      , cls1 == cls2
      , Right {} <- unify [] [ty1 :~: ty2]
      = Just (text "overlapCheck:" $$ ppr cls_ct $$ ppr ctr)
      | otherwise = Nothing

-- * Constraint Entailment
-- ------------------------------------------------------------------------------

-- | Completely entail a set of constraints. Fail if not possible
entailTcM :: [RnTyVar] -> ProgramTheory -> SimpleProgramTheory -> TcM FcTmSubst
entailTcM untch theory ctrs = do
  runSolverFirstM (go ctrs)
  `catchError` (\s-> throwError (s++" :Unable to Solve Class Constraints"))
  where
    go SN        = return mempty
    go (cs :> c) = do
      (ccs, subst1) <- rightEntailsBacktrack untch theory c
      subst2 <- go (cs <> ccs)
      return (subst2 <> subst1)

-- | Exhaustively simplify a set of constraints (this version does not backtrack)
entailDetTcM :: [RnTyVar] -> ProgramTheory -> SimpleProgramTheory -> TcM (SimpleProgramTheory, FcTmSubst)
entailDetTcM untch theory ctrs = go ctrs
  where
    entail_one :: AnnClsCt -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
    entail_one = rightEntailsDet untch theory

    go :: SimpleProgramTheory -> TcM (SimpleProgramTheory, FcTmSubst)
    go cs = findSLMaybeM entail_one cs >>= \case
      Just (rest, (simp_cs, subst1)) -> do
        (final_cs, subst2) <- go (rest <> simp_cs)
        return (final_cs, subst2 <> subst1)
      Nothing -> return (cs, mempty)

-- | Performs a single right entailment step.
--   a) fail if the constraint is not entailed by the given program theory
--   b) return the new wanted (class) constraints, as well as the System F term subsitution
rightEntailsDet :: [RnTyVar] -> ProgramTheory -> AnnClsCt
                -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
rightEntailsDet untch theory ann_cls_ct = lookupSLMaybeM left_entails theory
  where
    left_entails ct = leftEntails untch ct ann_cls_ct

-- | Performs a single right entailment step.
--   a) fail if the constraint is not entailed by the given program theory
--   b) return the new wanted (class) constraints, as well as the System F term subsitution
rightEntailsBacktrack :: [RnTyVar] -> ProgramTheory -> AnnClsCt
                      -> SolveM (SimpleProgramTheory, FcTmSubst)
rightEntailsBacktrack untch theory ann_cls_ct = liftSolveM (snocListChooseM theory left_entail) >>= SolveM . selectListT
  where
    left_entail ann_ctr = leftEntails untch ann_ctr ann_cls_ct

-- | Checks whether the class constraint is entailed by the given constraint
--   a) fails if the class constraint is not entailed
--   b) return the new wanted constraints, as well as the System F term substitution
leftEntails :: [RnTyVar] -> AnnCtr -> AnnClsCt
            -> TcM (Maybe (SimpleProgramTheory, FcTmSubst))
leftEntails untch (d_g :| ctr_g) (d_w :| cls_ct_w) = do
  (Ctr as cls_cs cls_ct_g) <- freshenLclBndrs ctr_g
  matchClsCs untch (d_g :| cls_ct_g) (d_w :| cls_ct_w) >>= \case
    Nothing            -> return Nothing
    Just (ty_subst, _) -> do
      (residual_ccs , d_res)   <- constructResidualCcs ty_subst cls_cs
      ev_subst_tm              <- constructEvFcTerm ty_subst (FcTmVar d_g) as d_res
      let ev_subst             = d_w |-> ev_subst_tm
      return $ Just (residual_ccs , ev_subst)
  where
    constructResidualCcs :: HsTySubst -> [RnClsCt] -> TcM (SimpleProgramTheory, [DictVar])
    constructResidualCcs _ty_subst []     = return (mempty , [])
    constructResidualCcs  ty_subst (c:cs) = do
      d             <- freshDictVar
      let subst_c   = substInClsCt ty_subst c
      (ann_cs , ds) <- constructResidualCcs ty_subst cs
      return (ann_cs :> (d :| subst_c) , d : ds)

    constructEvFcTerm :: HsTySubst -> FcTerm -> [RnTyVarWithKind] -> [DictVar] -> TcM FcTerm
    constructEvFcTerm _ty_subst fc_tm []     []     = return fc_tm
    constructEvFcTerm  ty_subst fc_tm []     (d:ds) =
      constructEvFcTerm ty_subst (FcTmApp fc_tm (FcTmVar d)) [] ds
    constructEvFcTerm  ty_subst fc_tm (a:as) ds     =
      elabMonoTy (substInMonoTy ty_subst (TyVar (labelOf a))) >>= \subst_fc_ty ->
      constructEvFcTerm ty_subst (FcTmTyApp fc_tm subst_fc_ty) as ds

-- | Unify two annotated class constraints (check that they have the same class
-- name and that the arguments can be unified). Return the resulting type and
-- term substitution.
matchClsCs :: Monad m => [RnTyVar] -> AnnClsCt {- Given -} -> AnnClsCt {- Wanted -}
           -> m (Maybe (HsTySubst, FcTmSubst))
matchClsCs untch (d1 :| ClsCt cls1 ty1) (d2 :| ClsCt cls2 ty2)
  | cls1 == cls2
  , Right ty_subst <- unify untch [ty1 :~: ty2]
  = return $ Just (ty_subst, d2 |-> FcTmVar d1)
  | otherwise = return Nothing

-- | Elaborate a class declaration. Return
--   a) The data declaration for the class
--   b) The method implementation
--   c) The extended typing environment
elabClsDecl :: RnClsDecl -> TcM (FcDataDecl, FcValBind, [FcValBind], ProgramTheory, TcCtx)
elabClsDecl (ClsD rn_cs cls (a :| _) method method_ty) = do
  -- Generate a fresh type and data constructor for the class
  -- GEORGE: They should already be generated during renaming.
  tc <- lookupClsTyCon   cls
  dc <- lookupClsDataCon cls

  -- Elaborate the superclass constraints (with full well-formedness checking also)
  fc_sc_tys <- extendCtxTyN a (kindOf a) (mapM wfElabClsCt rn_cs)

  -- Elaborate the method type (with full well-formedness checking also)
  (_kind, fc_method_ty) <- extendCtxTyN a (kindOf a) (wfElabPolyTy method_ty)

  -- Generate the datatype declaration
  let fc_data_decl = FcDataDecl tc [rnTyVarToFcTyVar a] [(dc, fc_sc_tys ++ [fc_method_ty])]

  -- Generate the method implementation
  (fc_val_bind, hs_method_ty) <- elabMethodSig method a cls method_ty

  -- Construct the extended typing environment
  ((ty_ctx,_),_) <- extendTC method hs_method_ty ask

  (sc_schemes, sc_decls) <- fmap unzip $ forM (zip [0..] rn_cs) $ \(i,sc_ct) -> do
    d  <- freshDictVar -- For the declaration
    da <- freshDictVar -- For the input dictionary

    let cls_head  = ClsCt cls (TyVar a) -- TC a
    fc_cls_head <- elabClsCt cls_head   -- T_TC a

    let scheme = constructCtr ([a :| kindOf a], [cls_head], sc_ct) -- forall a. TC a => SC
    fc_scheme <- elabCtr scheme                                    -- forall a. T_TC a -> upsilon_SC

    xs <- replicateM (length rn_cs + 1) freshFcTmVar               -- n+1 fresh variables

    let fc_tm = FcTmTyAbs (rnTyVarToFcTyVar a) $
                  FcTmAbs da fc_cls_head $
                    FcTmCase (FcTmVar da)
                             [FcAlt (FcConPat dc xs) (FcTmVar (xs !! i))]
    let proj = FcValBind d fc_scheme fc_tm

    return (d :| scheme, proj) -- error "NOT IMPLEMENTED YET"

  return (fc_data_decl, fc_val_bind, sc_decls, listToSnocList sc_schemes, ty_ctx)

-- | Elaborate a method signature to
--   a) a top-level binding
--   b) the actual source type (with the proper class qualification)
elabMethodSig :: RnTmVar -> RnTyVar -> RnClass-> RnPolyTy -> TcM (FcValBind, RnPolyTy)
elabMethodSig method a cls sigma = do
  -- Create the actual type, freshen it up and take it apart
  (bs, cs, ty) <- instPolyTy (mkRealMethodTy a cls sigma)

  -- Source and target method types
  let method_ty = constructPolyTy (zipWithExact (:|) bs (map kindOf bs), cs, ty)
  (_kind, fc_method_ty) <- wfElabPolyTy method_ty

  -- Annotate the constraints with fresh dictionary variables
  (ds, ann_cs) <- annotateClsCs cs

  dc <- lookupClsDataCon cls  -- pattern constructor
  n  <- length <$> lookupClsSuper cls
  xs <- replicateM (n+1) freshFcTmVar -- n superclass variables + 1 for the method

  -- elaborate the annotated dictionary variables to System F term binders
  dbinds <- annClsCsToTmBinds $ ann_cs

  let rn_bs = map rnTyVarToFcType bs

  let fc_method_rhs = fcTmTyAbs (map rnTyVarToFcTyVar bs) $
                        fcTmAbs dbinds $
                          FcTmCase (FcTmVar (head ds))
                                   [FcAlt (FcConPat dc xs)
                                          (fcDictApp (fcTmTyApp (FcTmVar (last xs)) (tail rn_bs)) (tail ds))]

  let fc_val_bind = FcValBind (rnTmVarToFcTmVar method) fc_method_ty fc_method_rhs

  return (fc_val_bind, method_ty)

-- | Construct the real method type out of the class specification
-- (a, TC, forall bs. C => ty) ~~~~~> forall a bs. (TC a, C) => ty
mkRealMethodTy :: RnTyVar -> RnClass -> RnPolyTy -> RnPolyTy
mkRealMethodTy a cls polyty = case destructPolyTy polyty of
  (bs, cs, ty) -> constructPolyTy ((a :| kindOf a) : bs, (ClsCt cls (TyVar a)) : cs, ty)

-- | Elaborate a list of annotated dictionary variables to a list of System F term binders.
annClsCsToTmBinds :: SimpleProgramTheory -> TcM [(FcTmVar, FcType)]
annClsCsToTmBinds annClsCs = mapM (\(d :| ct) -> elabCtr (constructCtr ([],[],ct)) >>= \ty -> return (d, ty)) $ snocListToList annClsCs

-- * Data Declaration Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a datatype declaration
elabDataDecl :: RnDataDecl -> TcM FcDataDecl
elabDataDecl (DataD tc as dcs) = do
  fc_tc <- hs_tc_fc_ty_con <$> lookupTcEnvM tc_env_tc_info tc  -- Elaborate the type constructor
  let fc_as = map (rnTyVarToFcTyVar . labelOf) as              -- Elaborate the universal type variables

  fc_dcs <- forM dcs $ \(dc, tys) -> do
    fc_dc <- hs_dc_fc_data_con <$> lookupTcEnvM tc_env_dc_info dc         -- Elaborate the data constructor
    (kinds, fc_tys) <- unzip <$> extendCtxKindAnnotatedTysM as (mapM wfElabMonoTy tys) -- Elaborate the argument types
    unless (all (==KStar) kinds) $
      throwErrorM (text "elabDataDecl" <+> colon <+> text "not all datacon args have kind star")
    return (fc_dc, fc_tys)
  return (FcDataDecl fc_tc fc_as fc_dcs)

-- | Extend the typing environment with some kind annotated type variables
extendCtxKindAnnotatedTysM :: (MonadReader (((Ctx x x' a Kind),d),c) m, Kinded a, MonadError String m) => [Ann a t] -> m b -> m b
extendCtxKindAnnotatedTysM ann_as = extendCtxTysN as (map kindOf as)
  where
    as = map labelOf ann_as

-- * Class Instance Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate a class instance. Take the program theory also as input and return
--   a) The dictionary transformer implementation
--   b) The extended program theory
elabInsDecl :: RnInsDecl -> TcM (FcValBind, FullTheory)
elabInsDecl (InsD ins_ctx cls typat method method_tm) = do
  -- Ensure the instance does not overlap
  pair <- ask
  let theory = snd (snd pair)
  overlapCheck theory head_ct

  -- Create the instance constraint scheme
  ins_d <- freshDictVar
  let ins_scheme = ins_d |: constructCtr (bs, ins_ctx, head_ct)

  --  Generate fresh dictionary variables for the instance context
  ann_ins_ctx <- snd <$> annotateClsCs ins_ctx

  --  The local program theory
  let local_theory = theory `ftExtendLocal` progTheoryFromSimple ann_ins_ctx

  -- The extended program theory
  let ext_theory = theory `ftExtendInst` singletonSnocList ins_scheme

  -- Create the dictionary transformer type
  dtrans_ty <- do
    fc_head_ty <- extendTcCtxTysM (map labelOf bs) (wfElabCtr (constructCtr ([],[],head_ct)))
    fc_ins_ctx <- extendTcCtxTysM (map labelOf bs) (wfElabClsCs ins_ctx)
    return $ fcTyAbs fc_bs $ fcTyArr fc_ins_ctx fc_head_ty

  -- Elaborate the method implementation
  let local_method_theory = local_theory `ftExtendLocal` singletonSnocList ins_scheme
  fc_method_tm <- do
    expected_method_ty <- instMethodTy (hsTyPatToMonoTy typat) <$> lookupTmVarN method
    elabTermWithSig (map labelOf bs) local_method_theory method_tm expected_method_ty

  -- Entail the superclass constraints
  fc_super_tms <- do
    a <- lookupClsParam cls
    (ds, super_cs) <- lookupClsSuper cls                          >>=
                      return . substVar a (hsTyPatToMonoTy typat) >>=
                      annotateClsCs

    ev_subst <- entailTcM (map labelOf bs) (ftToProgramTheory local_theory) super_cs
    --(residual_cs, ev_subst) <- rightEntailsRec (map labelOf bs) (ftToProgramTheory local_theory) super_cs
    --unless (nullSnocList residual_cs) $
    --  throwErrorM (text "Failed to resolve superclass constraints" <+> colon <+> ppr residual_cs
    --               $$ text "From" <+> colon <+> ppr local_theory)

    return (map (substFcTmInTm ev_subst . FcTmVar) ds)

  -- The full implementation of the dictionary transformer
  fc_dict_transformer <- do
    binds <- annClsCsToTmBinds ann_ins_ctx
    dc    <- lookupClsDataCon cls
    pat_ty <- elabMonoTy (hsTyPatToMonoTy typat)
    return $ fcTmTyAbs fc_bs $
               fcTmAbs binds $
                 fcDataConApp dc pat_ty (fc_super_tms ++ [fc_method_tm])

  -- Resulting dictionary transformer
  let fc_val_bind = FcValBind ins_d dtrans_ty fc_dict_transformer

  return (fc_val_bind, ext_theory)
  where
    bs      = ftyvsOf typat
    fc_bs   = map (rnTyVarToFcTyVar . labelOf) bs
    head_ct = ClsCt cls (hsTyPatToMonoTy typat)

-- | Instantiate a method type for a particular instance
instMethodTy :: RnMonoTy -> RnPolyTy -> RnPolyTy
instMethodTy typat poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    ((a :| _kind):as,_c:cs,ty) = destructPolyTy poly_ty
    subst      = (a |-> typat)
    new_as     = as
    new_cs     = substInClsCs subst cs
    new_ty     = substInMonoTy subst ty
-- TODO! duplicated only to fit elabIConv
-- GJ: I don't understand. Why is this duplicated?
instMethodTy2 :: RnMonoTy -> RnPolyTy -> RnPolyTy
instMethodTy2 typat poly_ty = constructPolyTy (new_as, new_cs, new_ty)
  where
    ((a :| _kind):as,cs,ty) = destructPolyTy poly_ty
    subst      = (a |-> typat)
    new_as     = as
    new_cs     = substInClsCs subst cs
    new_ty     = substInMonoTy subst ty
-- | Elaborate a term with an explicit type signature (method implementation).
-- This involves both inference and type subsumption.
-- UPDATED!
elabTermWithSig :: [RnTyVar] -> FullTheory -> RnTerm -> RnPolyTy -> TcM FcTerm
elabTermWithSig untch theory tm poly_ty = do

  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ics, wanted_ccs) <- runGenM $ elabTerm tm

  -- Generate fresh dictionary variables for the given constraints
  given_ccs <- snd <$> annotateClsCs cs
  dbinds    <- annClsCsToTmBinds given_ccs

  -- Resolve all the wanted constraints
  let untouchables = nub (untch ++ map labelOf as)

  ty_subst  <- unify untouchables $ wanted_eqs ++ [mono_ty :~: ty]

    -- NEW: YCs
  let refined_wanted_ics = substInYCs mempty ty_subst wanted_ics                       -- refine the wanted implicit conversion constraints
  (subst_place_holding_vars,ty_subst2) <- csolveY refined_wanted_ics
    -- End NEW

  ev_subst <- do
    let local_theory = ftToProgramTheory theory <> progTheoryFromSimple given_ccs
    let wanted       = substInSimpleProgramTheory (ty_subst2 <> ty_subst) wanted_ccs
    -- rightEntailsRec untouchables local_theory wanted
    entailTcM untouchables local_theory wanted
  -- -- Ensure that the constraints are completely resolved
  -- unless (nullSnocList residual_cs) $
  --   throwErrorM (text "Failed to resolve constraints" <+> colon <+> ppr residual_cs
  --                $$ text "From" <+> colon <+> ppr theory)

  fc_subst <- elabHsTySubst (ty_subst <> ty_subst2)
  let refined_fc_tm = substFcTyInTm  fc_subst fc_tm
  let fc_tm_after_Y = substFcTmInTm subst_place_holding_vars refined_fc_tm

  -- Generate the resulting System F term
  return $
    fcTmTyAbs fc_as $
      fcTmAbs dbinds $
        substFcTmInTm ev_subst $
          substFcTmInTm subst_place_holding_vars fc_tm_after_Y
  where
    (as,cs,ty) = destructPolyTy poly_ty
    fc_as      = map rnTyVarToFcTyVar (labelOf as)

-- | Convert a source type substitution to a System F type substitution
elabHsTySubst :: HsTySubst -> TcM FcTySubst
elabHsTySubst = mapSubM (return . rnTyVarToFcTyVar) elabMonoTy

-- * Implicit Conversion Elaboration
-- ------------------------------------------------------------------------------

-- | Elaborate an Implicit Conversion. Take the program theory also as input and return
--   a) 
--   b)

--plenty TO DO's... ugly baked in things. 
-- GJ: Uhm... We'll go through this function together in the next meeting...
elabIConvDecl :: RnIConvDecl -> TcM (ConvAxiom)
elabIConvDecl (IConvD i@(ICC name pct@(PCT vars pairs monoty@(MCT a b)) exp)) =
  case a of
    (TyVar x) -> throwError ("invalid implicit "++ (render$ppr name)++ "Type variables can't be the rhs of the final convmonoty")
    otherwise -> do
     pair <- ask
     let ft = snd (snd pair)
     --make sure tyVars are fine
     let (rnPHs,types) = aux pairs
     elab_exp <- emptyIT (extendTCs rnPHs types (case vars of
                                          []         -> elabTermWithSig (labelOf vars) ft exp (monoTyToPolyTy (mkRnArrowTy [a] b))
                                          otherwise  -> elabTermWithSig (labelOf vars) ft exp (monoTyToPolyTy (mkRnArrowTy [a] b))
                                       )) --TODO: why dropsuper here?
     let ext_it = case pairs of
           []        -> (MCA monoty elab_exp)
           otherwise -> (PCA pct  elab_exp)
     return (ext_it)
     where
       aux :: [(RnTmVar,RnMonoConvTy)] -> ([RnTmVar],[RnPolyTy])
       aux pairs = (map fst pairs, map (\(MCT a b) -> monoTyToPolyTy (mkRnArrowTy [a] b)) (map snd pairs))

extendIT :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => ConvAxiom -> m b -> m b
extendIT ca = local (\(x,(iCtx,ft)) -> (x,((iCtx:>ca),ft)))
extendTC :: MonadReader ((TcCtx,d),c) m => RnTmVar-> RnPolyTy -> m b -> m b
extendTC a b = local (\((tcCtx,ty),i) -> ((extendCtxTm tcCtx a b,ty),i))

extendSuper :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => ProgramTheory -> m b -> m b
extendSuper pt  = local (\(x,(iCtx,ft)) -> (x,(iCtx,ft `ftExtendSuper` pt)))

emptyIT :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => m b -> m b
emptyIT = local (\(x,(iCtx,ft)) -> (x,(SN,ft)))

setFT :: MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m => FullTheory -> m b -> m b
setFT ft  = local (\(x,(iCtx,_)) -> (x,(iCtx,ft)))          

-- | Add many type variables to the context
extendTCs :: (MonadReader ((TcCtx,RnMonoTy),(ImplicitTheory,FullTheory)) m, MonadError String m) => [RnTmVar] -> [RnPolyTy] -> m b -> m b
extendTCs []     []     m = m
extendTCs (a:as) (b:bs) m = extendTC a b (extendTCs as bs m)
extendTCs _      _      _ = throwErrorM (text "extendTCs" <+> colon <+> text "length mismatch")
-- * Type Inference With Constraint Simplification
-- ------------------------------------------------------------------------------
-- UPDATED
elabTermSimpl :: ProgramTheory -> RnTerm -> TcM (RnMonoTy, FcTerm) -- UPDATED
elabTermSimpl theory tm = do
  -- Infer the type of the expression and the wanted constraints
  ((mono_ty, fc_tm), wanted_eqs, wanted_ics, wanted_ccs) <- runGenM $ elabTerm tm
  -- Simplify as much as you can
  pair <- ask
  let given_ty = snd$fst pair
  let nwanted_eqs = (given_ty:~:mono_ty):wanted_eqs
  ty_subst <- unify mempty $  nwanted_eqs  -- Solve the needed equalities first

  let refined_wanted_ics = substInYCs mempty ty_subst wanted_ics                      -- refine the wanted implicit conversion constraints
  let refined_mono_ty    = substInMonoTy ty_subst mono_ty                             -- refine the monotype

  -- NEW: YCs
  (subst_place_holding_vars, ty_subst2) <- solveY refined_wanted_ics
  let refined_wanted_ccs = substInSimpleProgramTheory  (ty_subst2 <> ty_subst)  wanted_ccs       -- refine the wanted class constraints
  -- End NEW
  
  let fc_tm_after_Y = substFcTmInTm subst_place_holding_vars  fc_tm
  refined_fc_tm <- elabHsTySubst  (ty_subst<>ty_subst2)  >>= return . flip substFcTyInTm fc_tm_after_Y -- refine the term
  let untouchables = nub (ftyvsOf refined_mono_ty)

  ev_subst <- entailTcM untouchables theory refined_wanted_ccs --refined_wanted_ccs -- Francisco: No unresolved type classes.
  
  let new_mono_ty = refined_mono_ty
  -- Elaborate the term
  let full_fc_tm = --fcTmTyAbs fc_as $ fcTmAbs dbinds $
                       substFcTmInTm ev_subst $
                         refined_fc_tm

  return (new_mono_ty, full_fc_tm)

-- * Program Elaboration
-- ------------------------------------------------------------------------------


-- | Elaborate a tprogram
elabTProgram :: RnTProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnMonoTy)        {- Term type (MonoTy?)      -}
elabTProgram (TP p t) = elabProgram p

-- | Elaborate a program
elabProgram :: RnProgram
            -> TcM ( FcProgram       {- Elaborated program       -}
                   , RnMonoTy)        {- Term type (MonoTy?)      -}

-- Elaborate the program expression
elabProgram (PgmExp tm) = do
  --TODO theres probably a better way
  pair <- ask
  let theory = snd (snd pair)
  (ty, fc_tm) <- elabTermSimpl (ftDropSuper theory) tm
  return (FcPgmTerm fc_tm, ty) -- GEORGE: You should actually return the ones we have accumulated.

-- Elaborate a class declaration
elabProgram (PgmCls cls_decl pgm) = do
  (fc_data_decl, fc_val_bind, fc_sc_proj, ext_theory, ext_ty_env)  <- elabClsDecl cls_decl
  (fc_pgm, ty) <- setTcCtxTmM ext_ty_env (extendSuper ext_theory (elabProgram pgm))
  let fc_program = FcPgmDataDecl fc_data_decl (FcPgmValDecl fc_val_bind (foldl (flip FcPgmValDecl) fc_pgm fc_sc_proj))
  return (fc_program, ty)

-- | Elaborate a class instance
elabProgram (PgmInst ins_decl pgm) = do
  (fc_val_bind, ext_theory) <- elabInsDecl ins_decl
  (fc_pgm, ty) <- setFT ext_theory (elabProgram pgm)
  let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_program, ty)

-- | Elaborate a datatype declaration
elabProgram (PgmData data_decl pgm) = do
  fc_data_decl <- elabDataDecl data_decl
  (fc_pgm, ty) <- elabProgram pgm
  let fc_program = FcPgmDataDecl fc_data_decl fc_pgm
  return (fc_program, ty)

-- | Elaborate an implicit conversion declaration
elabProgram (PgmImpl iconv_decl pgm) = do
  ca <- elabIConvDecl iconv_decl
  (fc_pgm, ty) <- extendIT ca (elabProgram pgm)  --let fc_program = FcPgmValDecl fc_val_bind fc_pgm
  return (fc_pgm, ty)  

-- * Invoke the complete type checker
-- ------------------------------------------------------------------------------

hsElaborate :: RnEnv -> UniqueSupply -> RnTProgram
            -> (Either String ((((FcProgram, RnMonoTy), (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)), UniqueSupply), TcEnv),
                Trace)
hsElaborate rn_gbl_env us tpgm@(TP pgm ty) = runWriter
                              $ runExceptT
                              $ flip runStateT  tc_init_gbl_env -- Empty when you start
                              $ flip runReaderT ((tc_init_ctx,ty),(init_implicits_theory,tc_init_theory))
                              $ flip runUniqueSupplyT us
                              $ do { buildInitTcEnv pgm rn_gbl_env -- Create the actual global environment
                                   ; result <- elabTProgram tpgm
                                   ; assocs <- buildInitFcAssocs
                                   ; return (result, assocs) }
  where
    init_implicits_theory = mempty
    tc_init_theory  = FT mempty mempty mempty
    tc_init_ctx     = mempty
    tc_init_gbl_env = TcEnv mempty mempty mempty
----------------------------------------------------------
