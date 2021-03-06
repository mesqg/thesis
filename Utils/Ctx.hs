{-# LANGUAGE FlexibleContexts #-}

module Utils.Ctx
( Ctx -- Keep opaque
, lookupTyVarCtx, lookupTmVarCtx, extendCtxTy, extendCtxTm
, lookupTyVarM, lookupTyVarN, lookupTmVarM, lookupTmVarN
, extendCtxTyM, extendCtxTysM,extendCtxTyN,extendCtxTysN
, extendCtxTmM, extendCtxTmsM
, extendCtxM, setCtxM
) where

import Utils.PrettyPrint
import Utils.Errors

import Control.Monad.Reader
import Control.Monad.Except

-- | All kinds of contexts. E.g. used for
--   a) source renaming environment
--   b) source typing environment
--   c) target typing environment

data Ctx tm_var tm_assoc ty_var ty_assoc
  = CtxNil                                                          -- ^ Empty context
  | CtxConsTm (Ctx tm_var tm_assoc ty_var ty_assoc) tm_var tm_assoc -- ^ Term binding
  | CtxConsTy (Ctx tm_var tm_assoc ty_var ty_assoc) ty_var ty_assoc -- ^ Type binding

instance ( PrettyPrint tm_var, PrettyPrint tm_assoc
         , PrettyPrint ty_var, PrettyPrint ty_assoc
         ) => PrettyPrint (Ctx tm_var tm_assoc ty_var ty_assoc) where
  ppr = brackets . fsep . punctuate comma . reverse . ctxToList
    where
      ctxToList CtxNil                          = []
      ctxToList (CtxConsTm ctx tm_var tm_assoc) = (ppr tm_var <+> colon <+> ppr tm_assoc) : ctxToList ctx
      ctxToList (CtxConsTy ctx ty_var ty_assoc) = (ppr ty_var <+> colon <+> ppr ty_assoc) : ctxToList ctx
  needsParens _ = False

instance Semigroup (Ctx tm_var tm_assoc ty_var ty_assoc) where
  (<>) ctx CtxNil            = ctx
  (<>) ctx (CtxConsTm c v t) = CtxConsTm (ctx <> c) v t
  (<>) ctx (CtxConsTy c v t) = CtxConsTy (ctx <> c) v t

instance Monoid (Ctx tm_var tm_assoc ty_var ty_assoc) where
  mempty = CtxNil

  mconcat = foldl mappend CtxNil -- foldl since mappend does induction on the second argument

-- | Lookup a type variable binding
lookupTyVarCtx :: Eq a => Ctx x x' a a' -> a -> Maybe a'
lookupTyVarCtx CtxNil                 _a = Nothing
lookupTyVarCtx (CtxConsTm ctx _x _x')  a = lookupTyVarCtx ctx a
lookupTyVarCtx (CtxConsTy ctx  b  b')  a = if a == b then Just b' else lookupTyVarCtx ctx a

-- | Lookup a term variable binding
lookupTmVarCtx :: Eq x => Ctx x x' a a' -> x -> Maybe x'
lookupTmVarCtx CtxNil                 _x = Nothing
lookupTmVarCtx (CtxConsTm ctx  y  y')  x = if x == y then Just y' else lookupTmVarCtx ctx x
lookupTmVarCtx (CtxConsTy ctx _b _b')  x = lookupTmVarCtx ctx x

-- | Extend the context with a type binding
extendCtxTy :: Ctx x x' a a' -> a -> a' -> Ctx x x' a a'
extendCtxTy ctx tv ty = CtxConsTy ctx tv ty

-- | Extend the context with a term binding
extendCtxTm :: Ctx x x' a a' -> x -> x' -> Ctx x x' a a'
extendCtxTm ctx tv tm = CtxConsTm ctx tv tm

-- | Lookup a type variable in the context
lookupTyVarM :: (Eq a, PrettyPrint a, MonadReader (Ctx x x' a b) m, MonadError String m) => a -> m b
lookupTyVarM psb = ask >>= \ctx -> case lookupTyVarCtx ctx psb of
  Just rnb -> return rnb
  Nothing  -> throwErrorM (text "Unbound type variable" <+> colon <+> ppr psb)

-- | NEW! Lookup a type variable in the context w/ our reader
lookupTyVarN :: (Eq a, PrettyPrint a, MonadReader (((Ctx x x' a b),d),c) m, MonadError String m) => a -> m b
lookupTyVarN psb = ask >>= \((ctx,ty),i) -> case lookupTyVarCtx ctx psb of
  Just rnb -> return rnb
  Nothing  -> throwErrorM (text "Unbound type variable" <+> colon <+> ppr psb)

-- | Lookup a term variable in the context
lookupTmVarM :: (Eq a1, PrettyPrint a1, MonadReader (Ctx a1 b a a') m, MonadError String m) => a1 -> m b
lookupTmVarM psy = ask >>= \ctx -> case lookupTmVarCtx ctx psy of
  Just rny -> return rny
  Nothing  -> throwErrorM (text "Unbound term variable" <+> colon <+> ppr psy)

-- | New! Lookup a term variable in the context w/ our reader
lookupTmVarN :: (Eq a1, PrettyPrint a1, MonadReader (((Ctx a1 b a a'),d),c) m, MonadError String m) => a1 -> m b
lookupTmVarN psy = ask >>= \((ctx,_),_) -> case lookupTmVarCtx ctx psy of
  Just rny -> return rny
  Nothing  -> throwErrorM (text "Unbound term variable" <+> colon <+> ppr psy)

-- | Add a type variable to the context
extendCtxTyM :: MonadReader (Ctx x x' a a') m => a -> a' -> m b -> m b
extendCtxTyM psa rna = local (\ctx -> extendCtxTy ctx psa rna)

-- | NEW! Add a type variable to the context w/ our reader
extendCtxTyN :: MonadReader (((Ctx x x' a a'),d),c) m => a -> a' -> m b -> m b
extendCtxTyN psa rna = local (\((ctx,ty),i) -> ((extendCtxTy ctx psa rna,ty),i))

-- | Add many type variables to the context
extendCtxTysM :: (MonadReader (Ctx x x' a a') m, MonadError String m) => [a] -> [a'] -> m b -> m b
extendCtxTysM []     []     m = m
extendCtxTysM (a:as) (b:bs) m = extendCtxTyM a b (extendCtxTysM as bs m)
extendCtxTysM _      _      _ = throwErrorM (text "extendCtxTysM" <+> colon <+> text "length mismatch")

-- | New! Add many type variables to the context w/ our reader
extendCtxTysN :: (MonadReader (((Ctx x x' a a'),d),c) m, MonadError String m) => [a] -> [a'] -> m b -> m b
extendCtxTysN []     []     m = m
extendCtxTysN (a:as) (b:bs) m = extendCtxTyN a b (extendCtxTysN as bs m)
extendCtxTysN _      _      _ = throwErrorM (text "extendCtxTysN"<+> colon <+> text "length mismatch")

-- | Add a term variable to the context
extendCtxTmM :: MonadReader (Ctx x x' a a') m => x -> x' -> m b -> m b
extendCtxTmM psx rnx = local (\ctx -> extendCtxTm ctx psx rnx)

-- | Add many term variables to the context
extendCtxTmsM :: (MonadReader (Ctx x x' a a') m, MonadError String m) => [x] -> [x'] -> m b -> m b
extendCtxTmsM []     []     m = m
extendCtxTmsM (x:xs) (y:ys) m = extendCtxTmM x y (extendCtxTmsM xs ys m)
extendCtxTmsM _      _      _ = throwErrorM (text "extendCtxTmsM" <+> colon <+> text "length mismatch")

-- | Extend the context with a context extension
extendCtxM :: (Monoid r, MonadReader r m) => r -> m a -> m a
extendCtxM ctx2 = local (\ctx1 -> ctx1 <> ctx2)

-- | Replace the context
setCtxM :: MonadReader r m => r -> m a -> m a
setCtxM ctx = local (\_ -> ctx)
