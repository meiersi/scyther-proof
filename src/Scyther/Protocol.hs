{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-- | Security protocol represented as a set of roles which are sequences of
-- send and receive steps.
module Scyther.Protocol (

-- * Types
    Id(..)
  , Pattern(..)
  , Label(..)
  , RoleStep(..)
  , Role(..)
  , Protocol(..)
  , RoleStepOrder

-- * Queries

  -- ** Patterns
  , patFMV
  , patFAV
  , subpatterns
  , patternparts
  , splitpatterns

  -- ** Role Steps
  , stepPat
  , stepLabel
  , stepFMV
  , stepFAV

  -- ** Roles
  , roleFMV
  , roleFAV
  , lookupRoleStep
  , wfRole
  , roleOrd

  -- ** Protocols
  , lookupRole
  , stateLocale
  , restrictedStateLocale
  , labelOrd
  , protoOrd

  -- ** Wellformedness
  , ProtoIllformedness
  , wfProto
  , sptProtoIllformedness

-- * Output
  , isaRoleStep
  , sptId 
  , sptLabel
  , sptPattern
  , sptRoleStep
  , sptRole
  , sptProtocol
) where

import Safe
import Data.List
import qualified Data.Set as S
import Data.Data

import Control.Monad

import Extension.Prelude
import Text.Isar

-- Datatypes
------------

-- | An identifier.
newtype Id = Id { getId :: String }
  deriving( Eq, Ord, Data, Typeable {-! NFData !-} )

instance Show Id where
  show (Id i) = i

-- | A message pattern.
data Pattern = 
    PConst  Id                -- ^ A global constant.
  | PFresh  Id                -- ^ A message to be freshly generated.
  | PAVar   Id                -- ^ An agent variable.
  | PMVar   Id                -- ^ A message variable.
  | PHash   Pattern           -- ^ Hashing
  | PTup    Pattern Pattern   -- ^ Pairing
  | PEnc    Pattern Pattern   -- ^ Symmetric or asymmetric encryption (depent on the key).
  | PSign   Pattern Pattern   -- ^ A signature to be verified with the given key.
  | PSymK   Pattern Pattern   -- ^ A long-term unidirectional symmetric key.
  | PShrK   Pattern Pattern   -- ^ A long-term bi-directional symmetric key.
  | PAsymPK Pattern           -- ^ A long-term public key.
  | PAsymSK Pattern           -- ^ A long-term private key
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )

-- | A label of a role step.
newtype Label = Label { getLabel :: String }
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )

-- | A role step.
data RoleStep = 
    Send Label Pattern  -- ^ A send step.
  | Recv Label Pattern  -- ^ A receive step.
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )

-- | A role of a protocol. Its name has no operational meaning, but is carried
-- along to allow for human readable printing.
data Role = Role { 
    roleName  :: String
  , roleSteps :: [RoleStep] 
  }
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )

-- | A protocol. As for roles, its name has no operational meaning, but is
-- carried along to allow for human readable printing.
data Protocol = Protocol { 
    protoName  :: String
  , protoRoles :: [Role]
  }
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )


-- Queries
----------


-- | Find a role in a protocol according to its name.
lookupRole :: String -> Protocol ->  Maybe Role
lookupRole name = find ((== name) . roleName) . protoRoles

-- | Find a role step in a role according to its label.
lookupRoleStep :: String -> Role -> Maybe RoleStep
lookupRoleStep lbl = find ((== lbl) . stepLabel) . roleSteps

-- | Pattern of of a role step
stepPat :: RoleStep -> Pattern
stepPat (Send _ pt) = pt
stepPat (Recv _ pt) = pt

-- | The string label of a role step.
stepLabel :: RoleStep -> String
stepLabel (Send l _) = getLabel l
stepLabel (Recv l _) = getLabel l

-- | Pattern subterms.
subpatterns :: Pattern -> S.Set Pattern
subpatterns pt@(PHash pt1)     = S.insert pt $ subpatterns pt1
subpatterns pt@(PTup pt1 pt2)  = S.insert pt $ subpatterns pt1 `S.union` subpatterns pt2
subpatterns pt@(PEnc pt1 pt2)  = S.insert pt $ subpatterns pt1 `S.union` subpatterns pt2
subpatterns pt@(PSign pt1 pt2) = S.insert pt $ subpatterns pt1 `S.union` subpatterns pt2
subpatterns pt@(PSymK pt1 pt2) = S.insert pt $ subpatterns pt1 `S.union` subpatterns pt2
subpatterns pt@(PShrK pt1 pt2) = S.insert pt $ subpatterns pt1 `S.union` subpatterns pt2
subpatterns pt@(PAsymPK pt1)   = S.insert pt $ subpatterns pt1
subpatterns pt@(PAsymSK pt1)   = S.insert pt $ subpatterns pt1
subpatterns pt                 = S.singleton pt

-- | Accessible pattern subterms.
patternparts :: Pattern -> S.Set Pattern
patternparts pt@(PTup pt1 pt2)  = S.insert pt $ patternparts pt1 `S.union` patternparts pt2
patternparts pt@(PEnc pt1 _)    = S.insert pt $ patternparts pt1
patternparts pt@(PSign pt1 _)   = S.insert pt $ patternparts pt1
patternparts pt                 = S.singleton pt

-- | Splitting top-level pairs.
splitpatterns :: Pattern -> S.Set Pattern
splitpatterns (PTup pt1 pt2)  = splitpatterns pt1 `S.union` splitpatterns pt2
splitpatterns (PSign pt _  )  = splitpatterns pt
splitpatterns pt              = S.singleton pt

-- | Free message variables of a pattern.
patFMV :: Pattern -> S.Set Id
patFMV (PMVar v)        = S.singleton v
patFMV (PHash pt)       = patFMV pt
patFMV (PTup pt1 pt2)   = patFMV pt1 `S.union` patFMV pt2
patFMV (PEnc pt1 pt2)   = patFMV pt1 `S.union` patFMV pt2
patFMV (PSign pt1 pt2)  = patFMV pt1 `S.union` patFMV pt2
patFMV (PSymK pt1 pt2)  = patFMV pt1 `S.union` patFMV pt2
patFMV (PShrK pt1 pt2)  = patFMV pt1 `S.union` patFMV pt2
patFMV (PAsymPK pt)     = patFMV pt
patFMV (PAsymSK pt)     = patFMV pt
patFMV _                = S.empty

-- | Frees message variables of a role step.
stepFMV :: RoleStep -> S.Set Id
stepFMV = patFMV . stepPat

-- | Free message variables of a role.
roleFMV :: Role -> S.Set Id
roleFMV = S.unions . map (patFMV . stepPat) . roleSteps

-- | Free agent variables of a pattern.
patFAV :: Pattern -> S.Set Id
patFAV (PAVar v)        = S.singleton v
patFAV (PHash pt)       = patFAV pt
patFAV (PTup pt1 pt2)   = patFAV pt1 `S.union` patFAV pt2
patFAV (PEnc pt1 pt2)   = patFAV pt1 `S.union` patFAV pt2
patFAV (PSign pt1 pt2)  = patFAV pt1 `S.union` patFAV pt2
patFAV (PSymK pt1 pt2)  = patFAV pt1 `S.union` patFAV pt2
patFAV (PShrK pt1 pt2)  = patFAV pt1 `S.union` patFAV pt2
patFAV (PAsymPK pt)     = patFAV pt
patFAV (PAsymSK pt)     = patFAV pt
patFAV _                = S.empty


-- | Frees agent variables of a role step.
stepFAV :: RoleStep -> S.Set Id
stepFAV = patFAV . stepPat

-- | Free agent variables of a role.
roleFAV :: Role -> S.Set Id
roleFAV = S.unions . map (patFAV . stepPat) . roleSteps

-- Well-formedness of protocols and roles
-----------------------------------------

data ProtoIllformedness =
    NonUnique Role
  | SendBeforeReceive Role RoleStep Id
  | AccessibleLongTermKey Role RoleStep Pattern
  deriving( Eq, Ord, Show )

-- | Check if a role is well-formed; i.e., all steps are distinct, no
-- message variable is sent before it is received, and patterns do not
-- contain long-term-keys in accessible positions.
wfRole :: Role -> [ProtoIllformedness]
wfRole role = msum
    [ do guard (unique $ roleSteps role)
         return $ NonUnique role
    , recv_before_send S.empty (roleSteps role)
    , msum . map accessibleLongTermKeys $ roleSteps role
    ]
  where
    recv_before_send _                            []  = mzero
    recv_before_send received (step@(Send _ pt) : rs) = 
      do v <- S.toList $ patFMV pt
         guard (v `S.member` received)
         return $ SendBeforeReceive role step v
      `mplus`
      recv_before_send received rs
    recv_before_send received (Recv _ pt : rs) = 
      recv_before_send (patFMV pt `S.union` received) rs

    accessibleLongTermKeys step = do
      m <- S.toList . patternparts $ stepPat step
      key <- case m of
        PSymK _ _ -> return m
        PAsymSK _ -> return m
        _         -> mzero
      return $ AccessibleLongTermKey role step key

-- | Check if a protocol is well-formed; i.e., all roles are well-formed.
wfProto :: Protocol -> [ProtoIllformedness]
wfProto = concatMap wfRole . protoRoles

-- | Pretty print a protocol ill-formedness.
sptProtoIllformedness :: ProtoIllformedness -> Doc
sptProtoIllformedness pif = case pif of
  NonUnique role -> 
    text $ "role '" ++ roleName role ++ "' contains duplicate steps."
  SendBeforeReceive role step v ->
    text (roleName role) <> colon <-> 
    sptRoleStep Nothing step <> colon <->
    text "message variable" <-> quotes (sptId v) <-> text "sent before received."
  AccessibleLongTermKey role step _ ->
    text (roleName role) <> colon <-> 
    sptRoleStep Nothing step <> colon <->
    text "long-term keys must not be accessible."


-- Various orders on role steps
-------------------------------

-- | An order relation on role steps of a role.
type RoleStepOrder = [((RoleStep,Role),(RoleStep,Role))]

-- | The order of role steps as they are given in the role.
roleOrd :: Role -> RoleStepOrder
roleOrd role = zip steps (tailDef [] steps)
  where
  steps = zip (roleSteps role) (repeat role) 

-- | The order of role steps in the protocol such that every send step is
-- occurs before every receive step having the same label.
labelOrd :: Protocol -> RoleStepOrder
labelOrd proto = 
  [ (send, recv) | send@(Send l  _, _) <- steps, 
                   recv@(Recv l' _, _) <- steps, l == l' ]
  where
  steps = concat [ zip (roleSteps role) (repeat role) | role <- protoRoles proto ]
 
-- | The combination of all role orders and the label order of the protocol.
protoOrd :: Protocol -> RoleStepOrder
protoOrd proto = labelOrd proto ++ concatMap roleOrd (protoRoles proto)


------------------------------------------------------------------------------
-- ISAR Output
------------------------------------------------------------------------------

-- | The name of the locale assuming a reachable state of the given protocol.
stateLocale :: Protocol -> String
stateLocale proto = protoName proto ++ "_state"

-- | The name of the locale assuming a reachable state satisfying the axioms of
-- the theory.
restrictedStateLocale :: Protocol -> String
restrictedStateLocale proto = "restricted_" ++ protoName proto ++ "_state"

-- | Pretty print a rolestep in ISAR format. If a role is given, then the label
-- of the role step in this role is used to abbreviate the step name.
isaRoleStep :: IsarConf -> Maybe Role -> RoleStep -> Doc
isaRoleStep conf optRole step = 
  case optRole of
    Just role | step `elem` roleSteps role -> -- abbreviate
      text $ roleName role ++ "_" ++ stepLabel step
    _ ->
      text name <-> isar conf (Label $ stepLabel step) <-> ppPat (stepPat step) 
  where
  name = case step of Send _ _ -> "Send"; Recv _ _ -> "Recv"
  ppPat pt@(PTup _ _) = isar conf pt
  ppPat pt            = nestShort' "(" ")" (isar conf pt)

instance Isar Id where
  isar _ (Id i) = text $ "''"++i++"''"

instance Isar Label where
  isar _ (Label l) = text $ "''"++l++"''"

instance Isar Pattern where
  isar conf x = case x of
      (PConst i)                  -> text "sC" <-> isar conf i
      (PFresh i)                  -> text "sN" <-> isar conf i
      (PAVar i)                   -> text "sAV" <-> isar conf i
      (PMVar i)                   -> text "sMV" <-> isar conf i
      (PHash pt)                  -> text "PHash" <-> ppTup pt
      pt@(PTup _ _)               -> ppTup pt
      (PEnc m k)                  -> text "PEnc" <-> sep [ppTup m, ppTup k]
      (PSign m k)                 -> text "PSign" <-> sep [ppTup m, ppTup k]
      (PSymK (PAVar a) (PAVar b)) -> text "sK" <-> isar conf a <-> isar conf b
      (PSymK a b)                 -> text "PSymK" <-> sep [ppTup a, ppTup b]
      (PShrK a b)                 -> text "sKbd" <-> keyVar a <-> keyVar b
      (PAsymPK (PAVar a))         -> text "sPK" <-> isar conf a
      (PAsymPK a)                 -> text "PAsymPK" <-> ppTup a
      (PAsymSK (PAVar a))         -> text "sSK" <-> isar conf a
      (PAsymSK a)                 -> text "PAsymSK" <-> ppTup a
    where
      -- pretty print a tuple as right associate list
      ppTup pt@(PTup _ _) = nestShort n left right (fsep $ punctuate comma $ map (isar conf) $ split pt)
      ppTup pt = nestShort' "(" ")" (isar conf pt)
      -- split right associate nested tuples
      split (PTup pt1 pt2) = pt1 : split pt2
      split pt = [pt]
      -- determine output parameters
      (n,left,right)
        | isPlainStyle conf = (3, text "<|", text "|>")
        | otherwise         = (2, symbol "\\<langle>", symbol "\\<rangle>") 
      -- extract a variable of a bi-directional key
      keyVar (PAVar v) = parens $ text "AVar" <-> isar conf v
      keyVar (PMVar v) = parens $ text "MVar" <-> isar conf v
      keyVar _         = error $ "bi-directional key '" ++ show x ++ "' not supported."


instance Isar RoleStep where
  isar conf = isaRoleStep conf Nothing

instance Isar Role where
  isar conf (Role name steps) = 
    text "role" <-> text name $-$
    text "where" <-> text "\"" <> text name <-> text "=" $-$
    nest 2 (
      (vcat $ zipWith (<->) separators (map (isar conf) steps)) $-$
      text "]\""
    )
    where
    separators = map text ("[" : replicate (length steps - 1) ",")

instance Isar Protocol where
  isar conf (Protocol name roles) =
    vcat (map (($-$ text "") . isar conf) roles) $-$
    text "protocol" <-> text name $-$
    sep [text "where" <-> text "\"" <> text name <-> text "=", roleSet]
    where
    roleSet = nestShort' "{" "}\"" 
      (fsep $ punctuate comma $ map (text . roleName) roles)


------------------------------------------------------------------------------
-- SP Theory Output
------------------------------------------------------------------------------

sptId :: Id -> Doc
sptId = text . getId

sptLabel :: Label -> Doc
sptLabel = text . getLabel

sptPattern :: Pattern -> Doc
sptPattern x = case x of
    (PConst i)    -> char '\'' <> sptId i <> char '\''
    (PFresh i)    -> char '~'  <> sptId i
    (PAVar i)     ->              sptId i
    (PMVar i)     -> char '?'  <> sptId i
    (PHash m)     -> text "h" <> ppBetween 3 "(" ")" m
    pt@(PTup _ _) -> ppBetween 1 "(" ")" pt
    (PEnc m k)    -> fcat [ppBetween 1 "{" "}" m, sptPattern k]
    (PSign m k)   -> fcat [ppBetween 1 "sign{" "}" m, sptPattern k]
    (PSymK a b)   -> fcat [text "k(", sptPattern a, comma, sptPattern b, text ")"]
    (PShrK a b)   -> fcat [text "k[", sptPattern a, comma, sptPattern b, text "]"]
    (PAsymPK a)   -> text "pk" <> ppBetween 1 "(" ")" a
    (PAsymSK a)   -> text "sk" <> ppBetween 1 "(" ")" a
  where
    -- pretty print a tuple as right associate list
    ppBetween n lead finish pt@(PTup _ _) = 
      fcat . (text lead :) . (++[text finish]) . map (nest n) . punctuate (text ", ") . map sptPattern $ split pt
    ppBetween _ lead finish pt = text lead <> sptPattern pt <> text finish
    -- split right associate nested tuples
    split (PTup pt1 pt2) = pt1 : split pt2
    split pt = [pt]

-- | Pretty print a rolestep. If a role is given, then the label of the role
-- step in this role is used to abbreviate the step name.
sptRoleStep :: Maybe Role -> RoleStep -> Doc
sptRoleStep optRole step = 
  case optRole of
    Just role | step `elem` roleSteps role -> -- abbreviate
      text $ roleName role ++ "_" ++ stepLabel step
    _ ->
      (text $ name ++ "_" ++ stepLabel step) <> ppPat (stepPat step) 
  where
  name = case step of Send _ _ -> "Send"; Recv _ _ -> "Recv"
  ppPat pt@(PTup _ _) = sptPattern pt
  ppPat pt            = nestShort' "(" ")" (sptPattern pt)

-- | Pretty print a role in SP theory format.
sptRole :: Role -> Doc
sptRole(Role name steps) = 
  text "role" <-> text name $-$
  nestBetween 2 lbrace rbrace (
    (vcat $ map (sptRoleStep Nothing) steps)
  )

-- | Pretty print a protocol in SP theory format.
sptProtocol :: Protocol -> Doc
sptProtocol (Protocol name roles) =
  text "protocol" <-> text name $-$
  nestBetween 2 lbrace rbrace (
    vcat (intersperse (text "") $ map sptRole roles)
  )

