{-# LANGUAGE TypeFamilies, RankNTypes, NoMonomorphismRestriction, TupleSections #-}

import qualified Data.IntMap as IntMap
import qualified Data.IntMap as M
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import Debug.Trace
import Control.Monad
import Data.Maybe

-------------------------------------------------------------------------------
-- TrieMap

type XT a = Maybe a -> Maybe a -- How to alter a non-existent elt (Nothing)
                               -- or an existing elt (Just)

liftSnd :: a -> XT b -> XT (a, b)
liftSnd a f (Just (_, b)) = fmap (a,) (f (Just b))
liftSnd a f Nothing = fmap (a,) (f Nothing)

class TrieMap m where
    type Key m :: *
    emptyTM :: m a
    lookupTM :: forall b. Key m -> m b -> Maybe b
    alterTM :: forall b. Key m -> XT b -> m b -> m b
    foldTM   :: (a -> b -> b) -> m a -> b -> b

-- The unusual argument order here makes
-- it easy to compose calls to foldTM;
-- see for example fdE below
insertTM :: TrieMap m => Key m -> a -> m a -> m a
insertTM k v m = alterTM k (\_ -> Just v) m

deleteTM :: TrieMap m => Key m -> m a -> m a
deleteTM k m = alterTM k (\_ -> Nothing) m

(>.>) :: (a -> b) -> (b -> c) -> a -> c
-- Reverse function composition (do f first, then g)
infixr 1 >.>
(f >.> g) x = g (f x)
infixr 1 |>, |>>
(|>) :: a -> (a->b) -> b -- Reverse application
x |> f = f x

-- One specific type
{-
(|>>) :: TrieMap m2
      => (XT (m2 a) -> m1 (m2 a) -> m1 (m2 a))
      -> (m2 a -> m2 a)
      -> m1 (m2 a) -> m1 (m2 a)
      -}
(|>>) :: TrieMap m2
      => (XT (m2 a) -> t)
      -> (m2 a -> m2 a)
      -> t
(|>>) f g = f (Just . g . deMaybe)

deMaybe :: TrieMap m => Maybe (m a) -> m a
deMaybe Nothing = emptyTM
deMaybe (Just m) = m

-------------------------------------------------------------------------------
-- Maybe

data MaybeMap m a = EmptyMM | MM { mm_nothing  :: Maybe a, mm_just :: m a }

instance TrieMap m => TrieMap (MaybeMap m) where
   type Key (MaybeMap m) = Maybe (Key m)
   emptyTM  = EmptyMM
   lookupTM = lkMaybe lookupTM
   alterTM  = xtMaybe alterTM
   foldTM   = fdMaybe

wrapEmptyMaybeMap = MM { mm_nothing = Nothing, mm_just = emptyTM }

lkMaybe :: TrieMap m => (forall b. k -> m b -> Maybe b)
        -> Maybe k -> MaybeMap m a -> Maybe a
lkMaybe lk x m
    | EmptyMM <- m = Nothing
    | otherwise    = go lk x m
  where
    go _  Nothing  = mm_nothing
    go lk (Just x) = mm_just >.> lk x

xtMaybe :: TrieMap m => (forall b. k -> XT b -> m b -> m b)
        -> Maybe k -> XT a -> MaybeMap m a -> MaybeMap m a
xtMaybe tr x f m
    | EmptyMM <- m = xtMaybe tr x f wrapEmptyMaybeMap
xtMaybe _  Nothing  f m = m { mm_nothing  = f (mm_nothing m) }
xtMaybe tr (Just x) f m = m { mm_just = mm_just m |> tr x f }

fdMaybe :: TrieMap m => (a -> b -> b) -> MaybeMap m a -> b -> b
fdMaybe _ EmptyMM = \z -> z
fdMaybe k m = foldMaybe k (mm_nothing m)
            . foldTM k (mm_just m)

foldMaybe :: (a -> b -> b) -> Maybe a -> b -> b
foldMaybe _ Nothing  b = b
foldMaybe k (Just a) b = k a b

-------------------------------------------------------------------------------
-- List
data ListMap m a
  = EmptyLM
  | LM { lm_nil  :: Maybe a
       , lm_cons :: m (ListMap m a) }

instance TrieMap m => TrieMap (ListMap m) where
   type Key (ListMap m) = [Key m]
   emptyTM  = EmptyLM
   lookupTM = lkList lookupTM
   alterTM  = xtList alterTM
   foldTM   = fdList

wrapEmptyListMap = LM { lm_nil = Nothing, lm_cons = emptyTM }

lkList :: TrieMap m => (forall b. k -> m b -> Maybe b)
        -> [k] -> ListMap m a -> Maybe a
lkList lk xs m
    | m <- EmptyLM = Nothing
    | otherwise = go lk xs m
  where
    go :: TrieMap m => (forall b. k -> m b -> Maybe b)
        -> [k] -> ListMap m a -> Maybe a
    go _  []     = lm_nil
    go lk (x:xs) = lm_cons >.> lk x >=> lkList lk xs

xtList :: TrieMap m => (forall b. k -> XT b -> m b -> m b)
        -> [k] -> XT a -> ListMap m a -> ListMap m a
xtList tr xs f m
    | EmptyLM <- m = xtList tr xs f wrapEmptyListMap
xtList _  []     f m = m { lm_nil  = f (lm_nil m) }
xtList tr (x:xs) f m = m { lm_cons = lm_cons m |> tr x |>> xtList tr xs f }

fdList :: forall m a b. TrieMap m
       => (a -> b -> b) -> ListMap m a -> b -> b
fdList _ EmptyLM = \z -> z
fdList k m = foldMaybe k          (lm_nil m)
           . foldTM    (fdList k) (lm_cons m)

-------------------------------------------------------------------------------
-- IntMap

instance TrieMap IntMap.IntMap where
    type Key IntMap.IntMap = Int
    emptyTM = IntMap.empty
    lookupTM k m = IntMap.lookup k m
    alterTM = xtInt
    foldTM k m z = IntMap.fold k z m

xtInt :: Int -> XT a -> IntMap.IntMap a -> IntMap.IntMap a
xtInt k f m = IntMap.alter f k m

-------------------------------------------------------------------------------
-- Map

instance Ord k => TrieMap (Map.Map k) where
  type Key (Map.Map k) = k
  emptyTM = Map.empty
  lookupTM = Map.lookup
  alterTM k f m = Map.alter f k m
  foldTM k m z = Map.fold k z m

-------------------------------------------------------------------------------
-- Unique

type Unique = Int

class Uniquable a where
    getUnique :: a -> Unique

getKey :: Unique -> Int
getKey x = x

-------------------------------------------------------------------------------
-- UniqKM

newtype UniqKM k a = UKM { unUKM :: IntMap.IntMap (k, a) }
    deriving (Show)

instance Uniquable k => TrieMap (UniqKM k) where
    type Key (UniqKM k) = k
    emptyTM = emptyUKM
    lookupTM k m = lookupUKM m k
    alterTM k f m = alterUKM f m k
    foldTM k m z = foldUKM k z m

emptyUKM :: UniqKM k a
emptyUKM = UKM M.empty

isNullUKM :: UniqKM k a -> Bool
isNullUKM (UKM m) = M.null m

unitUKM :: Uniquable k => k -> a -> UniqKM k a
unitUKM k v = UKM (M.singleton (getKey $ getUnique k) (k, v))

alterUKM :: Uniquable k => XT a -> UniqKM k a -> k -> UniqKM k a
alterUKM f (UKM m) k = UKM (M.alter (liftSnd k f) (getKey $ getUnique k) m)

addToUKM :: Uniquable k => UniqKM k a -> k -> a -> UniqKM k a
addToUKM (UKM m) k v   = UKM (M.insert (getKey $ getUnique k) (k, v) m)

lookupUKM :: Uniquable k => UniqKM k a -> k -> Maybe a
lookupUKM (UKM m) k = fmap snd (M.lookup (getKey $ getUnique k) m)

elemUKM :: Uniquable k => k -> UniqKM k a -> Bool
elemUKM k (UKM m) = M.member (getKey $ getUnique k) m

elemUKM_Directly :: Int -> UniqKM k a -> Bool
elemUKM_Directly u (UKM m) = M.member u m

foldUKM :: (a -> r -> r) -> r -> UniqKM k a -> r
foldUKM k z (UKM m) = M.fold (k . snd) z m

xtUKM :: Uniquable k => k -> XT a -> UniqKM k a -> UniqKM k a
xtUKM k f m = alterUKM f m k

-------------------------------------------------------------------------------
-- AST

data Type
    = TyVarTy Var
    | ForAllTy Var Type
    | TyConApp TyCon [KindOrType]
    | TyBox -- for our supervenience
    deriving Show

data TyCon
    = FunTyCon {
        tyConName :: Name,
        tc_kind :: Kind }
    | PrimTyCon {
        tyConName :: Name,
        tc_kind :: Kind }
    deriving (Show)
instance Eq TyCon where
    tc1 == tc2 = tyConName tc1 == tyConName tc2
instance Uniquable TyCon where
    getUnique tc = tyConName tc

data Var = Var
    { varName :: Name
    , varType :: Kind
    }
instance Show Var where
    show (Var n _) = show n
instance Eq Var where
    v1 == v2 = varName v1 == varName v2
instance Uniquable Var where
    getUnique = varName

type KindOrType = Type
type TyLit = String
type Name = Int
type Kind = Type

-------------------------------------------------------------------------------
-- VarSet

type VarSet = IntMap.IntMap Var
extendVarSet s k = IntMap.insert (varName k) k s
emptyVarSet = IntMap.empty
elemVarSet k s = IntMap.member (varName k) s
elemVarSetByKey k s = IntMap.member k s
varSetElems = IntMap.elems
unitVarSet k = IntMap.singleton (varName k) k
unionVarSet = IntMap.union
delVarSet s k = IntMap.delete (varName k) s
mapUnionVarSet get_set xs = foldr (unionVarSet . get_set) emptyVarSet xs

-------------------------------------------------------------------------------
-- VarEnv

type VarEnv a = UniqKM Var a

emptyVarEnv = emptyUKM
extendVarEnv = addToUKM
lookupVarEnv = lookupUKM
alterVarEnv = alterUKM
elemVarEnv = elemUKM
elemVarEnvByKey = elemUKM_Directly

data InScopeSet = InScope VarSet
    deriving (Show)

emptyInScopeSet :: InScopeSet
emptyInScopeSet = InScope emptyVarSet

elemInScopeSet :: Var -> InScopeSet -> Bool
elemInScopeSet v (InScope in_scope) = v `elemVarSet` in_scope

extendInScopeSet :: InScopeSet -> Var -> InScopeSet
extendInScopeSet (InScope in_scope) v = InScope (extendVarSet in_scope v)

uniqAway' :: InScopeSet -> Var -> Var
uniqAway' (InScope set) var = try 1
    where try k
            | k `elemVarSetByKey` set = try (k + 1)
            | otherwise = var { varName = k }

uniqAway'' :: InScopeSet -> Type -> Var
uniqAway'' (InScope set) ty = try 1
    where try k
            | k `elemVarSetByKey` set = try (k + 1)
            | otherwise = Var { varName = k, varType = ty }

-------------------------------------------------------------------------------
-- The AST (stuff)

typeKind :: Type -> Kind
typeKind orig_ty = go orig_ty
  where
    go (ForAllTy _ ty) = go ty
    go (TyVarTy tyvar) = tyVarKind tyvar
    go (TyConApp tc _) = tc_kind tc
    go TyBox = TyBox

tyVarKind = varType

type TyVarEnv elt = VarEnv elt
type TvSubstEnv = TyVarEnv Type

tyVarsOfType :: Type -> VarSet
tyVarsOfType (TyVarTy v) = unitVarSet v
tyVarsOfType (ForAllTy tyvar ty) = delVarSet (tyVarsOfType ty) tyvar `unionVarSet` tyVarsOfType (tyVarKind tyvar)
tyVarsOfType (TyConApp _ tys) = tyVarsOfTypes tys
tyVarsOfType TyBox = emptyVarSet

tyVarsOfTypes :: [Type] -> VarSet
tyVarsOfTypes = mapUnionVarSet tyVarsOfType

-------------------------------------------------------------------------------
-- TyLitMap

type TyLitMap = Map.Map String

lkTyLit :: TyLit -> TyLitMap a -> Maybe a
lkTyLit n = Map.lookup n

xtTyLit :: TyLit -> XT a -> TyLitMap a -> TyLitMap a
xtTyLit n f m = Map.alter f n m

-------------------------------------------------------------------------------
-- BoundVarMap

type BoundVar = Int  -- Bound variables are deBruijn numbered (ezyang: actually it's de Bruijn levels)
type BoundVarMap a = IntMap.IntMap a
emptyBoundVarMap = IntMap.empty
lookupBoundVarMap m k = IntMap.lookup k m
extendBoundVarMap m k v = IntMap.insert k v m

data CmEnv = CME { cme_next :: BoundVar
                 , cme_env  :: VarEnv BoundVar }
    deriving (Show)

emptyCME :: CmEnv
emptyCME = CME { cme_next = 0, cme_env = emptyVarEnv }

extendCME :: CmEnv -> Var -> CmEnv
extendCME (CME { cme_next = bv, cme_env = env }) v
  = CME { cme_next = bv+1, cme_env = extendVarEnv env v bv }

extendCMEs :: CmEnv -> [Var] -> CmEnv
extendCMEs env vs = foldl extendCME env vs

lookupCME :: CmEnv -> Var -> Maybe BoundVar
lookupCME (CME { cme_env = env }) v = lookupVarEnv env v

-- Inverse of CmEnv (core "fold" environment)
-- This is VERY similar to rnEnv2, except since we're deBruijn indexed
-- we get to use BoundVarMap
data CfEnv = CFE { cfe_next :: BoundVar
                 , cfe_env :: BoundVarMap Var
                 , cfe_in_scope :: InScopeSet
                 }
    deriving (Show)

emptyCFE :: CfEnv
emptyCFE = CFE { cfe_next = 0, cfe_env = emptyBoundVarMap, cfe_in_scope = emptyInScopeSet }

extendCFE :: CfEnv -> Type -> (CfEnv, Var)
extendCFE CFE { cfe_next = bv, cfe_env = env, cfe_in_scope = in_scope } tb
    = (CFE { cfe_next = bv + 1
           , cfe_env = extendBoundVarMap env bv new_b
           , cfe_in_scope = extendInScopeSet in_scope new_b
           }, new_b)
          where new_b = uniqAway'' in_scope tb

lookupCFE :: CfEnv -> BoundVar -> Maybe Var
lookupCFE env = lookupBoundVarMap (cfe_env env)

-------------------------------------------------------------------------------
-- VarMap

data VarMap a = VM { vm_bvar   :: BoundVarMap a  -- Bound variable
                   , vm_fvar   :: VarEnv a }      -- Free variable
    deriving (Show)

instance TrieMap VarMap where
   type Key VarMap = Var
   emptyTM  = VM { vm_bvar = IntMap.empty, vm_fvar = emptyVarEnv }
   lookupTM = lkVar emptyCME
   alterTM  = xtVar emptyCME
   foldTM   = fdVar

lkVar :: CmEnv -> Var -> VarMap a -> Maybe a
lkVar env v
  | Just bv <- lookupCME env v = vm_bvar >.> lookupTM bv
  | otherwise                  = vm_fvar >.> lkFreeVar v

xtVar :: CmEnv -> Var -> XT a -> VarMap a -> VarMap a
xtVar env v f m
  | Just bv <- lookupCME env v = m { vm_bvar = vm_bvar m |> xtInt bv f }
  | otherwise                  = m { vm_fvar = vm_fvar m |> xtFreeVar v f }

lkFreeVar :: Var -> VarEnv a -> Maybe a
lkFreeVar var env = lookupVarEnv env var

xtFreeVar :: Var -> XT a -> VarEnv a -> VarEnv a
xtFreeVar v f m = alterVarEnv f m v

fdVar :: (a -> b -> b) -> VarMap a -> b -> b
fdVar k m = foldTM k (vm_bvar m)
          . foldTM k (vm_fvar m)

-------------------------------------------------------------------------------
-- TypeMap

data TypeMap a
    = EmptyTM -- you NEED this otherwise you get an infinite data structure
    | TM { tm_var :: VarMap a
         , tm_forall :: BndrMap (TypeMap a)
         , tm_tc_app :: UniqKM TyCon (ListMap TypeMap a)
         , tm_box :: Maybe a
         }
-- Hmm, this is awkward. For efficiency reasons, we want to defer
-- running the BndrMap until after we've investigated the body of
-- the forall.  However, this means we can't seem to get the right
-- 'bv' when we recursively call fdkT...

instance TrieMap TypeMap where
   type Key TypeMap = Type
   emptyTM  = EmptyTM
   lookupTM = lkT emptyCME
   alterTM  = xtT emptyCME
   foldTM   = fdT

wrapEmptyTypeMap :: TypeMap a
wrapEmptyTypeMap = TM { tm_var  = emptyTM
                      , tm_forall = EmptyTM
                      , tm_tc_app = emptyUKM
                      , tm_box = Nothing
                      }

lkT :: CmEnv -> Type -> TypeMap a -> Maybe a
lkT env ty m
  | EmptyTM <- m = Nothing
  | otherwise    = go ty m
  where
    go (TyVarTy v)       = tm_var    >.> lkVar env v
    go (ForAllTy tv ty)  = tm_forall >.> lkBndr env tv >=> lkT (extendCME env tv) ty
    go (TyConApp tc tys) = tm_tc_app >.> lookupTM tc >=> lkList (lkT env) tys
    go TyBox             = tm_box

xtT :: CmEnv -> Type -> XT a -> TypeMap a -> TypeMap a
xtT env ty f m
  | EmptyTM <- m = xtT env ty  f wrapEmptyTypeMap

xtT env (TyVarTy v)         f  m = m { tm_var    = tm_var m |> xtVar env v f }
xtT env (ForAllTy tv ty)  f  m = m { tm_forall = tm_forall m |> xtBndr env tv
                                                 |>> xtT (extendCME env tv) ty f }
xtT env (TyConApp tc tys) f  m = m { tm_tc_app = tm_tc_app m |> xtUKM tc
                                                 |>> xtList (xtT env) tys f }
xtT env TyBox f m = m { tm_box = f (tm_box m) }

fdT :: (a -> b -> b) -> TypeMap a -> b -> b
fdT _ EmptyTM = \z -> z
fdT k m = foldTM k (tm_var m)
        . foldTM (foldTM k) (tm_tc_app m)
        . foldTM (foldTM k) (tm_forall m)
        . foldMaybe k (tm_box m)

-------------------------------------------------------------------------------
-- BndrMap

type BndrMap = TypeMap

lkBndr :: CmEnv -> Var -> BndrMap a -> Maybe a
lkBndr env v m = lkT env (varType v) m

xtBndr :: CmEnv -> Var -> XT a -> BndrMap a -> BndrMap a
xtBndr env v f = xtT env (varType v) f

-------------------------------------------------------------------------------
-- RnEnv2

data RnEnv2
  = RV2 { envL     :: VarEnv Var        -- Renaming for Left term
        , envR     :: VarEnv Var        -- Renaming for Right term
        , in_scope :: InScopeSet }      -- In scope in left or right terms

rnBndr2 :: RnEnv2 -> Var -> Var -> RnEnv2
-- ^ @rnBndr2 env bL bR@ goes under a binder @bL@ in the Left term,
--                       and binder @bR@ in the Right term.
-- It finds a new binder, @new_b@,
-- and returns an environment mapping @bL -> new_b@ and @bR -> new_b@
rnBndr2 (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL bR
  = RV2 { envL     = extendVarEnv envL bL new_b   -- See Note
        , envR     = extendVarEnv envR bR new_b   -- [Rebinding]
        , in_scope = extendInScopeSet in_scope new_b }
  where
        -- Find a new binder not in scope in either term
    new_b | not (bL `elemInScopeSet` in_scope) = bL
          | not (bR `elemInScopeSet` in_scope) = bR
          | otherwise                          = uniqAway' in_scope bL

        -- Note [Rebinding]
        -- If the new var is the same as the old one, note that
        -- the extendVarEnv *deletes* any current renaming
        -- E.g.   (\x. \x. ...)  ~  (\y. \z. ...)
        --
        --   Inside \x  \y      { [x->y], [y->y],       {y} }
        --       \x  \z         { [x->x], [y->y, z->x], {y,x} }

rnOccL, rnOccR :: RnEnv2 -> Var -> Var
-- ^ Look up the renaming of an occurrence in the left or right term
rnOccL (RV2 { envL = env }) v = lookupVarEnv env v `orElse` v
rnOccR (RV2 { envR = env }) v = lookupVarEnv env v `orElse` v

infixr 4 `orElse`
orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

inRnEnvL, inRnEnvR :: RnEnv2 -> Var -> Bool
-- ^ Tells whether a variable is locally bound
inRnEnvL (RV2 { envL = env }) v = v `elemVarEnv` env
inRnEnvR (RV2 { envR = env }) v = v `elemVarEnv` env

eqTypeX :: RnEnv2 -> Type -> Type -> Bool
eqTypeX env (TyVarTy tv1) (TyVarTy tv2) = rnOccL env tv1 == rnOccR env tv2
eqTypeX env (ForAllTy tv1 t1) (ForAllTy tv2 t2) = eqTypeX env (tyVarKind tv1) (tyVarKind tv2) && eqTypeX (rnBndr2 env tv1 tv2) t1 t2
eqTypeX env (TyConApp tc1 tys1) (TyConApp tc2 tys2) = tc1 == tc2 && eqTypesX env tys1 tys2
eqTypeX _ _ _ = False

eqTypesX :: RnEnv2 -> [Type] -> [Type] -> Bool
eqTypesX env tys1 tys2 = or (zipWith (eqTypeX env) tys1 tys2)

-------------------------------------------------------------------------------
-- MatchEnv

data MatchEnv
    = ME { me_tmpls :: VarSet
         , me_env :: RnEnv2
         }

match :: MatchEnv
      -> TvSubstEnv
      -> Type -> Type
      -> Maybe TvSubstEnv
match menv subst (TyVarTy tv1) ty2
    | Just ty1' <- lookupVarEnv subst tv1'
    = if eqTypeX rn_env ty1' ty2
        then Just subst
        else Nothing
    | tv1' `elemVarSet` me_tmpls menv
    = if any (inRnEnvR rn_env) (varSetElems (tyVarsOfType ty2))
        then Nothing
        else do subst1 <- match menv subst (tyVarKind tv1) (typeKind ty2)
                return (extendVarEnv subst1 tv1' ty2)
    | otherwise
    = case ty2 of
        TyVarTy tv2 | tv1' == rnOccR rn_env tv2 -> Just subst
        _ -> Nothing
  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1
match menv subst (ForAllTy tv1 ty1) (ForAllTy tv2 ty2)
    = do subst' <- match menv subst (tyVarKind tv1) (tyVarKind tv2)
         match menv' subst' ty1 ty2
  where
    menv' = menv { me_env = rnBndr2 (me_env menv) tv1 tv2 }
match menv subst (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  | tc1 == tc2 = match_tys menv subst tys1 tys2
match _ _ _ _ = Nothing

match_tys :: MatchEnv -> TvSubstEnv -> [Type] -> [Type] -> Maybe TvSubstEnv
match_tys menv subst tys1 tys2 = matchList (match menv) subst tys1 tys2

matchList :: (env -> a -> b -> Maybe env)
           -> env -> [a] -> [b] -> Maybe env
matchList _  subst []     []     = Just subst
matchList fn subst (a:as) (b:bs) = do { subst' <- fn subst a b
                                      ; matchList fn subst' as bs }
matchList _  _     _      _      = Nothing

-------------------------------------------------------------------------------
-- The BIG DADDY

dmatchT :: VarSet -> Type -> TypeMap a -> [(a, TvSubstEnv)]
dmatchT tmpls = matchT tmpls emptyCME emptyCFE emptyVarEnv

matchT :: VarSet -> CmEnv -> CfEnv -> TvSubstEnv -> Type -> TypeMap a -> [(a, TvSubstEnv)]
matchT tmpls menv fenv subst t m
    | EmptyTM <- m = []
    | otherwise = go t m
  where
    accept = maybeToList >.> fmap (,subst)
    -- The original match strategy maintained a left/right renaming
    -- which it used to work around alpha-equivalence issues.  Our
    -- strategy is to use on-the-fly deBruijn renaming.  However,
    -- this means the order we check things is a bit delicate.
    -- Suppose x is a template variable and we have \x. x. To process
    -- the binder, we'll add x to CmEnv; then when we process the
    -- variable x, x will be in both CmEnv and the set of template
    -- variables: but it's NOT a template variable.
    --
    -- By the way, checking if lkVar returns Nothing is not good enough,
    -- since that just might mean that we didn't store anything for
    -- a bound variable; not that it isn't bound.  So we
    -- semi-reimplement lkVar here
    go (TyVarTy tv)
        | Just bv <- lookupCME menv tv
        = tm_var >.> vm_bvar >.> lookupTM bv >.> accept
        -- OK, it's a free variable. A few possibilities...
        -- 1. It's a template variable, AND we already have a
        -- substitution for it.
        | Just ty <- lookupVarEnv subst tv
        = go ty
        -- 2. It's a template variable, but we don't have a
        -- substitution.  Accept all valid substitutions.
        | tv `elemVarSet` tmpls
        -- (\m -> trace (show (foldTM (const (+1)) m 0)) m) >.> 
        = undefined -- flip (fdkT fenv (\k x r -> (x, extendVarEnv subst tv k):r)) []
        -- TODO occurs check!!
        -- 3. It's just a plain old free variable.
        | otherwise
        = tm_var >.> vm_fvar >.> lkFreeVar tv >.> accept
    go (ForAllTy tv ty)
        = tm_forall >.> lkBndr menv tv >.> maybeToList
            >=> matchT tmpls
                       (extendCME menv tv)
                       (fst (extendCFE fenv (varType tv)))
                       subst ty
    go (TyConApp tc tys)
        = tm_tc_app >.> lookupTM tc >.> maybeToList >=> matchListT tmpls menv fenv subst tys
    go TyBox = tm_box >.> accept

-- BLAH, this should be generalized, but HOW... (the big problem is
-- threading the TvSubstEnv through)
matchListT :: VarSet -> CmEnv -> CfEnv -> TvSubstEnv -> [Type] -> ListMap TypeMap a -> [(a, TvSubstEnv)]
matchListT tmpls menv fenv subst ts m
    | EmptyLM <- m = []
    | otherwise = go subst ts m
  where
    go subst [] = lm_nil >.> maybeToList >.> fmap (,subst)
    go subst (x:xs) = lm_cons >.> matchT tmpls menv fenv subst x
                              >=> \(m', subst') -> go subst' xs m'

-------------------------------------------------------------------------------
-- Test

box = TyBox
star = TyBox -- TyConApp (PrimTyCon 201 box) []
fn = FunTyCon 202 TyBox
(a:b:c:d:e:f:g:_) = [Var i star | i <- [100..]]
t1 = ForAllTy a (TyVarTy a)
t2 = TyVarTy b
t3 = TyConApp fn [TyBox, TyBox]
t4 = TyConApp fn [t2, t2]

test1 :: TypeMap String
test1 = insertTM t3 "BOX -> BOX"
      . insertTM t1 "forall (a :: *). a"
      $ emptyTM

