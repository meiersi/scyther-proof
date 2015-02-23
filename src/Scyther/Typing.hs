{-# LANGUAGE TypeSynonymInstances, DeriveDataTypeable, FlexibleInstances #-}
-- | Building typing invariants for security protocol in order to enable
-- verification in an untyped model.
module Scyther.Typing (
  -- * Type
    Type(..)
  , normType

  -- ** Type annotations
  , TypeAnn
  , typeAnnTIDs
  , typeAnnAMIDs
  , substTypeAnn

  -- ** Type assertions
  , Typing
  , mscTyping

  -- ** Pretty Printing
  , isaType
  , sptType
  , sptTypeAnn
  , sptTyping
) where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.DAG.Simple
import Data.Data

import Control.Basics
import Control.Monad.State

import Scyther.Protocol
import Scyther.Message
import qualified Scyther.Equalities as E
import Text.Isar


data Type =
    AgentT 
  | ConstT Id
  | NonceT Role Id
  | HashT Type
  | EncT  Type Type
  | TupT Type Type
  | SymKT Type Type
  | AsymPKT Type
  | AsymSKT Type
  | KnownT RoleStep
  | SumT Type Type
  deriving( Eq, Ord, Show, Data, Typeable )

-- | Partial normalization: rewrites with 
--
-- > SumT ty (KnownT _) = SumT (KnownT _) ty
--
normType :: Type -> Type
normType (SumT ty1 ty2@(KnownT _)) = SumT ty2 (normType ty1)
normType (SumT ty1 ty2)            = SumT (normType ty1) (normType ty2)
normType (EncT ty1 ty2)            = EncT (normType ty1) (normType ty2)
normType (TupT ty1 ty2)            = TupT (normType ty1) (normType ty2)
normType (SymKT ty1 ty2)           = SymKT (normType ty1) (normType ty2)
normType (HashT ty)                = HashT ty
normType (AsymPKT ty)              = AsymPKT ty
normType (AsymSKT ty)              = AsymSKT ty
normType ty                        = ty

-- | Split all sums in a type term and return the basic types.
splitSums :: Type -> [Type]
splitSums (SumT ty1 ty2) = splitSums ty1 `mplus` splitSums ty2
splitSums ty             = pure ty


------------------------------------------------------------------------------
-- Type annotations on messages
------------------------------------------------------------------------------

-- | A type annotation states that a message is a member of a type interpreted
-- with respect to a specific thread.
type TypeAnn = (Message, Type, TID)

-- | The TIDs of a type annotation.
typeAnnTIDs :: TypeAnn -> [TID]
typeAnnTIDs (m, _, tid) = tid : msgTIDs m 

-- | The AMIDs of a type annotation.
typeAnnAMIDs :: TypeAnn -> [ArbMsgId]
typeAnnAMIDs (m, _, _) = msgAMIDs m 

-- | Substitute a type annotation.
substTypeAnn :: E.Equalities -> TypeAnn -> TypeAnn
substTypeAnn eqs (m, ty, tid) = (E.substMsg eqs m, ty, E.substTID eqs tid)


------------------------------------------------------------------------------
-- Typings
------------------------------------------------------------------------------

-- | A type assignment for variables of several roles.
type Typing = M.Map (Id, Role) Type

-- | Compute a typing from the message sequence chart of the protocol
-- implicitly given by the corresponding labels.
--
-- FIXME: This is quite a hack and could be done much better: do it!
mscTyping :: Protocol -> Maybe Typing
mscTyping proto = 
    (`execStateT` M.empty) $ foldM typeStep E.empty steps
  where
    roleeqs = M.fromList $ zip [1..] (protoRoles proto)
    rolemap = M.fromList $ zip (protoRoles proto) [1..]
    steps = map (second (rolemap M.!)) . toposort $ protoOrd proto

    typeStep eqs (Send _ _, _) = return eqs
    typeStep eqs step@(Match _ True v pt, tidM) = do
        eqs' <- lift $ E.solve [E.MsgEq (instVar tidM v, inst tidM pt)] eqs
        lty <- variable (const . return $ AgentT) (lookupType step) v
        typeMatchVars step lty (E.getMVarEqs eqs')
        return eqs'
    typeStep eqs (Match _ _ _ _, _) = return eqs
    typeStep eqs step@(Recv lR ptR, tidR) =
        case [ send | send@(Send lS _, _) <- steps, lS == lR ] of
          []                   -> do
              -- no matching send: assume intruder knows all message variables
              -- in the received pattern that are not yet mapped.
              sequence_ $ do PMVar v <- S.toList $ subpatterns ptR
                             return (knownAtRecv step v)
              return eqs
          ((Send _ ptS, tidS):_) -> do
              eqs' <- lift $ E.solve [E.MsgEq (inst tidR ptR, inst tidS ptS)] eqs
              mapM_ (typeMVar step) (E.getMVarEqs eqs')
              -- variables not mapped yet are mapped to they known type.
              sequence_ $ do PMVar v <- S.toList $ subpatterns ptR
                             return (knownAtRecv step v)
              return eqs'
          _ -> error "mscTyping: the impossible happened"

    lookupType (_step, tid) v = gets (M.! (v, roleeqs M.! tid))

    keepExisting _new old = old

    typeMVar (step, tid) (MVar (LocalId (v, vTid)), m)
      | vTid == tid && PMVar v `S.member` splitpatterns (stepPat step) =
          noteType (KnownT step)
      | otherwise =
          noteType $ maybe (KnownT step) (SumT (KnownT step)) (typeMsg m)
      where
        noteType = modify . M.insertWith keepSimpler (v, roleeqs M.! vTid)
        -- prefer non-sum-types and then the existing one
        keepSimpler _  x@(KnownT _) = x
        keepSimpler x@(KnownT _) _  = x
        keepSimpler _            x  = x

    knownAtRecv (step, tid) v =
        modify (M.insertWith keepExisting (v, roleeqs M.! tid) (KnownT step))

    -- Infer types of variables on RHS of a matching step. We use both the type
    -- of the LHS variable and the types implied by the message equalities.
    typeMatchVars (step, tid) lty meqs = mapM_ noteType vars
      where
        vars = [v | PMVar v <- S.toList $ subpatterns $ stepPat step]
        noteType v = modify $ M.insertWith keepExisting (v, roleeqs M.! tid) (inferType v)
        inferType v = case known ++ structuralTypesOf v of
                          []  -> error $ "mscTyping: Cannot infer type. Impossible match?"
                          tys -> foldr1 SumT tys
        structuralTypesOf v = S.toList $ M.findWithDefault S.empty v structuralTypes
        -- Due to deficiencies of the well-typedness proof strategy, use the
        -- current match step in KnownT types.
        known = case [ty | ty@(KnownT _) <- splitSums lty] of
                    [] -> []
                    _  -> [KnownT step]

        structuralTypes = transfer lty (stepPat step) eqTypes
        eqTypes = foldr eqType1 M.empty meqs
        eqType1 (MVar (LocalId (v, vTid)), msg)
          | vTid == tid = maybe id (M.insert v . S.singleton) (typeMsg msg)
          | otherwise   = id

        transfer (SumT ty1 ty2)  pt            = transfer ty1 pt . transfer ty2 pt
        transfer (KnownT _)      _             = id
        transfer ty              (PMVar v)     = M.insertWith S.union v (S.singleton ty)
        transfer (HashT ty)      (PHash pt)    = transfer ty pt
        transfer (EncT ty1 ty2)  (PEnc p1 p2)  = transfer ty1 p1 . transfer ty2 p2
        transfer (TupT ty1 ty2)  (PTup p1 p2)  = transfer ty1 p1 . transfer ty2 p2
        transfer (SymKT ty1 ty2) (PSymK p1 p2) = transfer ty1 p1 . transfer ty2 p2
        transfer (AsymPKT ty)    (PAsymPK pt)  = transfer ty pt
        transfer (AsymSKT ty)    (PAsymSK pt)  = transfer ty pt
        transfer _               _             = id


    typeMsg (MFresh (Fresh fr)) = pure $ NonceT (roleeqs M.! lidTID fr) (lidId fr)
    typeMsg (MConst c)    = pure $ ConstT c
    typeMsg (MAVar _)     = pure $ AgentT
    typeMsg (MMVar _)     = Nothing
    typeMsg (MHash m)     = HashT   <$> typeMsg m
    typeMsg (MTup m1 m2)  = TupT    <$> typeMsg m1 <*> typeMsg m2
    typeMsg (MEnc m1 m2)  = EncT    <$> typeMsg m1 <*> typeMsg m2
    typeMsg (MSymK m1 m2) = SymKT   <$> typeMsg m1 <*> typeMsg m2
    typeMsg (MAsymPK m)   = AsymPKT <$> typeMsg m
    typeMsg (MAsymSK m)   = AsymSKT <$> typeMsg m
    typeMsg (MArbMsg _)    = error $ "mscTyping: logical variable encountered"
    typeMsg (MInvKey _)   = error $ "mscTyping: key inversion encountered"
    typeMsg (MShrK _ _)   = error $ "mscTyping: bi-directional shared key encountered"


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a type in Isar syntax; paramatrized over the role of the
-- variable that this type describes. This role is used for abbreviating role
-- steps by the 'role_label' constant symbols defined in Isabelle.
isaType :: IsarConf -> Maybe Role -> Type -> Doc
isaType conf optRole = go
  where
  go ty = case ty of
    AgentT        -> text "AgentT"
    ConstT i      -> parens $ text "ConstT" <-> isar conf i
    NonceT role i -> parens $ text "NonceT" <-> text (roleName role) <-> isar conf i
    HashT ty1     -> parens $ text "HashT" <-> go ty1
    EncT ty1 ty2  -> parens $ text "EncT" <-> go ty1 <-> go ty2
    TupT ty1 ty2  -> parens $ text "TupT" <-> go ty1 <-> go ty2
    AsymPKT ty1   -> parens $ text "PKT" <-> go ty1
    AsymSKT ty1   -> parens $ text "SKT" <-> go ty1
    SymKT ty1 ty2 -> parens $ text "KT" <-> go ty1 <-> go ty2
    KnownT step   -> parens $ text "KnownT" <-> isaRoleStep conf optRole step
    SumT ty1 ty2  -> parens $ text "SumT" <-> go ty1 <-> go ty2

-- | Pretty print a type in security protocol theory format. If the role is
-- given then the type describes a variable of this role. The steps of this
-- role are abbreviated accordingly.
sptType :: Maybe Role -> Type -> Doc
sptType optRole = go
  where
  go ty = case ty of
    AgentT        -> text "Agent"
    ConstT i      -> text $ "'" ++ getId i ++ "'"
    NonceT role i -> text $ getId i ++ "@" ++ roleName role
    HashT ty1     -> text "h" <> parens (go ty1)
    EncT ty1 ty2  -> braces (go ty1) <> go ty2
    TupT ty1 ty2  -> parens (go ty1 <> comma <-> go ty2)
    AsymPKT ty1   -> text "pk" <> parens (go ty1)
    AsymSKT ty1   -> text "sk" <> parens (go ty1)
    SymKT ty1 ty2 -> text "k"  <> parens (go ty1 <> comma <-> go ty2)
    KnownT step   -> text "Known" <> parens (sptRoleStep optRole step)
    SumT ty1 ty2  -> parens (sep [go ty1 <-> text "|", go ty2])

sptTypeAnn :: (TID -> Maybe Role) -> TypeAnn -> Doc
sptTypeAnn tidToRole (m,ty,i) = hsep 
    [sptMessage m, text "::", parens (sptType (tidToRole i) ty) <> sptTID i]

sptTyping :: Typing -> Doc
sptTyping = vcat . map ppTyEq . M.toList 
  where
    ppTyEq ((v,role),ty) = 
      sep [ text $ getId v ++ "@" ++ roleName role
          , nest 2 $ text "::" <-> sptType (Just role) ty ]

instance Isar Type where
  isar conf = isaType conf Nothing

instance Isar Typing where
  isar conf = 
      ($$ rbrack) . vcat . zipWith (<->) seps . map ppTyEq . M.toList
    where
      seps = map char $ '[' : repeat ','
      ppTyEq ((v,role),ty) = parens $
        sep [ parens (text (roleName role) <> comma <-> isar conf v) <> comma
            , isaType conf (Just role) ty ]

