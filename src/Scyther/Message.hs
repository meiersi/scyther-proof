{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-- | The actual messages being sent and received over the network are always
-- ground. Here we develop a representation of the denotations of actual
-- messages that may occur during a security proof. This involves symbolically
-- instantiated variables and symbolically inverted keys.
module Scyther.Message (
-- * Messages
    TID(..)
  , LocalId(..)
  , Fresh(..)
  , AVar(..)
  , MVar(..)
  , ArbMsgId(..)
  , Message(..)
  -- ** Queries
  , lidId
  , lidTID
  , avarTID
  , mvarTID
  , msgFMV
  , msgFresh
  , msgAMIDs
  , msgTIDs
  , trivial
  , submessages
  , messageparts
  -- ** Construction/Transformation
  , mapFresh
  , mapAVar
  , mapMVar
  , inst
  , normMsg
  , splitNonTrivial

-- * Output
  , sptTID
  , sptArbMsgId
  , sptFresh
  , sptAVar
  , sptMVar
  , sptMessage
) where

import Control.Monad
import Control.Applicative

import Data.Data

-- workaround new Monoid operator <>
#if __GLASGOW_HASKELL__ < 704
import Data.Monoid
#else
import Data.Monoid hiding ((<>))
#endif

import qualified Data.Set as S

import Text.Isar

import Scyther.Protocol

------------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------------

-- | A logical variable for a thread identifier. Note that these are the only
-- free logical variables being used during proofs. Depending on their context
-- they are either universally or existentially quantified.
newtype TID = TID { getTID :: Int }
  deriving( Eq, Ord, Enum, Num, Data, Typeable {-! NFData !-})

instance Show TID where
  show (TID tid) = '#':show tid

-- | An agent name identifier
newtype ArbMsgId = ArbMsgId { arbMsgId :: Int }
  deriving( Eq, Ord, Enum, Num, Data, Typeable )

instance Show ArbMsgId where
  show (ArbMsgId aid) = 'a':show aid


-- | A local identifier.
newtype LocalId = LocalId { getLocalId :: (Id, TID) }
  deriving( Eq, Ord, Data, Typeable )

instance Show LocalId where
  show (LocalId (i, tid)) = show i ++ show tid

-- | An agent variable.
newtype AVar = AVar { getAVar :: LocalId }
  deriving( Eq, Ord, Show, Data, Typeable )

-- | A message variable.
newtype MVar = MVar { getMVar :: LocalId }
  deriving( Eq, Ord, Show, Data, Typeable )

-- | A fresh message.
newtype Fresh = Fresh { getFresh :: LocalId }
  deriving( Eq, Ord, Show, Data, Typeable )
  

-- | Denotations of messages as they occurr during reasoning. Note that we do
-- not model agents, as in the proofs that we want to do no actual agent
-- reference will be needed.
--
-- Note: This is /no free algebra/ due to the nested equalities on thread
-- identifiers and the key-inversion function. However, there is still a most
-- general unifier. The easiest way to understand these messages is to map 
-- them to the corresponding Isabelle proof states.
data Message = 
    MConst  Id          -- ^ A global constant.
  | MFresh  Fresh       -- ^ A freshly generated message.
  | MAVar   AVar        -- ^ A symbolically instantiated agent variable.
  | MMVar   MVar        -- ^ A symbolically instantiated message variable; 
                        --   @MVar (LocalId (Id \"v\", TID 1))@ corresponds to @s(|MV ''v'' tid1|)@.
  | MArbMsg ArbMsgId    -- ^ An arbitrary message; i.e., a logical message variable.
  | MHash   Message            -- ^ Hashing
  | MTup    Message Message    -- ^ Pairing
  | MEnc    Message Message    -- ^ Encryption or signing depending on the key (the second argument)
  | MSymK   Message Message    -- ^ A long-term uni-directional symmetric key
  | MShrK   Message Message    -- ^ A long-term bi-directional symmetric key.
  | MAsymPK Message            -- ^ A long-term asymmetric public key.
  | MAsymSK Message            -- ^ A long-term asymmetric private key.
  | MInvKey Message            -- ^ An application of the key inversion function.
  deriving( Eq, Ord, Show, Data, Typeable {-! NFData !-} )

-- Queries
----------

-- | Identifier of a local id.
lidId :: LocalId -> Id
lidId = fst . getLocalId

-- | Thread identifier of a local id.
lidTID :: LocalId -> TID
lidTID = snd . getLocalId

-- | The thread corresponding to an agent variable
avarTID :: AVar -> TID
avarTID = snd . getLocalId . getAVar 

-- | The thread corresponding to an message variable
mvarTID :: MVar -> TID
mvarTID = snd . getLocalId . getMVar 

-- | Thread identifiers of a message.
msgTIDs :: Message -> [TID]
msgTIDs (MConst _)    = empty
msgTIDs (MFresh f)    = pure . lidTID . getFresh $ f
msgTIDs (MAVar v)     = pure . avarTID $ v
msgTIDs (MMVar v)     = pure . mvarTID $ v
msgTIDs (MArbMsg _)    = empty
msgTIDs (MHash m)     = msgTIDs m
msgTIDs (MTup m1 m2)  = msgTIDs m1 `mappend` msgTIDs m2
msgTIDs (MEnc m1 m2)  = msgTIDs m1 `mappend` msgTIDs m2
msgTIDs (MSymK m1 m2) = msgTIDs m1 `mappend` msgTIDs m2
msgTIDs (MShrK m1 m2) = msgTIDs m1 `mappend` msgTIDs m2
msgTIDs (MAsymPK m)   = msgTIDs m
msgTIDs (MAsymSK m)   = msgTIDs m
msgTIDs (MInvKey m)   = msgTIDs m

-- | Arbitrary-message identifiers of a message (logical message variables).
msgAMIDs :: Message -> [ArbMsgId]
msgAMIDs (MConst _)    = empty
msgAMIDs (MFresh _)    = empty
msgAMIDs (MAVar _)     = empty
msgAMIDs (MMVar _)     = empty
msgAMIDs (MArbMsg a)    = pure a
msgAMIDs (MHash m)     = msgAMIDs m
msgAMIDs (MTup m1 m2)  = msgAMIDs m1 `mappend` msgAMIDs m2
msgAMIDs (MEnc m1 m2)  = msgAMIDs m1 `mappend` msgAMIDs m2
msgAMIDs (MSymK m1 m2) = msgAMIDs m1 `mappend` msgAMIDs m2
msgAMIDs (MShrK m1 m2) = msgAMIDs m1 `mappend` msgAMIDs m2
msgAMIDs (MAsymPK m)   = msgAMIDs m
msgAMIDs (MAsymSK m)   = msgAMIDs m
msgAMIDs (MInvKey m)   = msgAMIDs m

-- | Free message variables of a message.
msgFMV :: Message -> [MVar]
msgFMV (MMVar v)     = pure v
msgFMV (MHash m)     = msgFMV m
msgFMV (MTup m1 m2)  = msgFMV m1 <|> msgFMV m2
msgFMV (MEnc m1 m2)  = msgFMV m1 <|> msgFMV m2
msgFMV (MSymK m1 m2) = msgFMV m1 <|> msgFMV m2
msgFMV (MShrK m1 m2) = msgFMV m1 <|> msgFMV m2
msgFMV (MAsymPK m)   = msgFMV m
msgFMV (MAsymSK m)   = msgFMV m
msgFMV (MInvKey m)   = msgFMV m
msgFMV _             = empty

-- | Fresh messages of a message.
msgFresh :: Message -> [Fresh]
msgFresh (MFresh lid)  = pure lid
msgFresh (MHash m)     = msgFresh m
msgFresh (MTup m1 m2)  = msgFresh m1 <|> msgFresh m2
msgFresh (MEnc m1 m2)  = msgFresh m1 <|> msgFresh m2
msgFresh (MSymK m1 m2) = msgFresh m1 <|> msgFresh m2
msgFresh (MShrK m1 m2) = msgFresh m1 <|> msgFresh m2
msgFresh (MAsymPK m)   = msgFresh m
msgFresh (MAsymSK m)   = msgFresh m
msgFresh (MInvKey m)   = msgFresh m
msgFresh _             = empty

-- | A message is trivial iff it is a tuple or it is guaranteed to be in the
-- initial intruder knowledge (i.e., global constants and agent variables).
--
-- PRE: Message must be normalized.
trivial :: Message -> Bool
trivial (MConst _) = True
trivial (MAVar _)  = True
trivial (MTup _ _) = True
trivial _          = False

-- | The submessages of message.
submessages :: Message -> S.Set Message
submessages m@(MHash m1)     = S.insert m $ submessages m1
submessages m@(MTup m1 m2)   = S.insert m $ submessages m1 `S.union` submessages m2
submessages m@(MEnc m1 m2)   = S.insert m $ submessages m1 `S.union` submessages m2
submessages m@(MSymK m1 m2)  = S.insert m $ submessages m1 `S.union` submessages m2
submessages m@(MShrK m1 m2)  = S.insert m $ submessages m1 `S.union` submessages m2
submessages m@(MAsymPK m1)   = S.insert m $ submessages m1
submessages m@(MAsymSK m1)   = S.insert m $ submessages m1
submessages   (MInvKey _)    = error "submessages: undefined for key inversion"
submessages m                = S.singleton m

-- | The accessible submessages of message.
messageparts :: Message -> S.Set Message
messageparts m@(MTup m1 m2)   = S.insert m $ messageparts m1 `S.union` messageparts m2
messageparts m@(MEnc m1 m2)   = S.insert m $ messageparts m1 `S.union` messageparts m2
messageparts m                = S.singleton m


-- Construction/Transformaiton
------------------------------

mapFresh :: (LocalId -> LocalId) -> Fresh -> Fresh
mapFresh f = Fresh . f . getFresh

mapAVar :: (LocalId -> LocalId) -> AVar -> AVar
mapAVar f = AVar . f . getAVar

mapMVar :: (LocalId -> LocalId) -> MVar -> MVar
mapMVar f = MVar . f . getMVar

-- | Instantiate a pattern to a message. Variables are instantiated
-- symbolically. The resulting message is guaranteed to be normalized w.r.t
-- `normMsg`.
inst :: TID -> Pattern -> Message
inst _   (PConst i)       = MConst i
inst tid (PFresh i)       = MFresh (Fresh (LocalId (i, tid)))
inst tid (PAVar i)        = MAVar  (AVar (LocalId (i, tid)))
inst tid (PMVar i)        = MMVar  (MVar (LocalId (i, tid)))
inst tid (PHash pt)       = MHash (inst tid pt)
inst tid (PTup pt1 pt2)   = MTup (inst tid pt1) (inst tid pt2)
inst tid (PEnc pt1 pt2)   = MEnc (inst tid pt1) (inst tid pt2)
inst tid (PSign pt1 pt2)  = MTup m1 (MEnc m1 (normMsg $ MInvKey (inst tid pt2)))
  where m1 = inst tid pt1
inst tid (PSymK pt1 pt2)  = MSymK (inst tid pt1) (inst tid pt2)
inst tid (PShrK pt1 pt2)  = MShrK (inst tid pt1) (inst tid pt2)
inst tid (PAsymPK pt)     = MAsymPK (inst tid pt)
inst tid (PAsymSK pt)     = MAsymSK (inst tid pt)

-- | Normalize a message; i.e., apply key-inversion if possible and swap shared
-- key arguments, if required.
normMsg :: Message -> Message
normMsg m@(MConst _)          = m
normMsg m@(MFresh _)          = m
normMsg m@(MAVar _)           = m
normMsg m@(MMVar _)           = m
normMsg m@(MArbMsg _)         = m
normMsg (MInvKey (MInvKey m)) = normMsg m
normMsg (MInvKey (MAsymPK m)) = MAsymSK (normMsg m)
normMsg (MInvKey (MAsymSK m)) = MAsymPK (normMsg m)
normMsg m@(MInvKey (MMVar _)) = m
normMsg (MInvKey m)           = normMsg m
normMsg (MHash  m)            = MHash (normMsg m)
normMsg (MTup  m1 m2)         = MTup (normMsg m1) (normMsg m2)
normMsg (MEnc  m1 m2)         = MEnc (normMsg m1) (normMsg m2)
normMsg (MSymK m1 m2)         = MSymK (normMsg m1) (normMsg m2)
normMsg (MShrK m1 m2)  
  | m1' < m2' = MShrK m1' m2'
  | otherwise = MShrK m2' m1'
  where
    m1' = normMsg m1
    m2' = normMsg m2
normMsg (MAsymPK m)           = MAsymPK (normMsg m)
normMsg (MAsymSK m)           = MAsymSK (normMsg m)


-- | Splits a message into the list of non-'trivial' messages accessible using
-- projection only.
--
-- Postcondition: All messages in the list are non-'trivial'.
splitNonTrivial :: Message -> [Message]
splitNonTrivial (MTup m1 m2) = splitNonTrivial m1 `mplus` splitNonTrivial m2
splitNonTrivial m            = do
  guard (not $ trivial m) 
  return m



------------------------------------------------------------------------------
-- ISAR Output
------------------------------------------------------------------------------

-- | Textual symbolic application of the substitution.
-- TODO: Remove hack about thread identifier to state assignment.
esplSubst :: LocalId -> IsarConf -> Doc -> Doc
esplSubst (LocalId (_,tid)) conf var 
  | tid == 0 = isarSubst conf <> parens var
  | otherwise = text "s" <> parens var

instance Isar TID where
  isar _ tid = text "tid" <> int (getTID tid)

instance Isar ArbMsgId where
  isar _ aid = text "a" <> int (arbMsgId aid)

instance Isar LocalId where
  isar conf (LocalId (i, tid)) = isar conf i <-> isar conf tid

instance Isar Fresh where
  isar conf (Fresh i) = text "LN" <-> isar conf i

instance Isar AVar where
  isar conf (AVar i) = esplSubst i conf (text "AV" <-> isar conf i)

instance Isar MVar where
  isar conf (MVar i) = esplSubst i conf (text "MV" <-> isar conf i)

instance Isar Message where
  isar conf x = case x of
      (MConst i)    -> text "LC" <-> isar conf i
      (MFresh i)    -> isar conf i 
      (MAVar i)     -> isar conf i
      (MMVar i)     -> isar conf i
      (MArbMsg i)   -> isar conf i
      (MHash m)     -> text "Hash" <-> ppTup m
      pt@(MTup _ _) -> ppTup pt
      (MEnc m k)    -> text "Enc" <-> sep [ppTup m, ppTup k]
      (MSymK a b)   -> text "K" <-> sep [ppTup a, ppTup b]
      (MShrK a b)   -> text "Kbd" <-> sep [ppTup a, ppTup b]
      (MAsymPK a)   -> text "PK" <-> ppTup a
      (MAsymSK a)   -> text "SK" <-> ppTup a
      (MInvKey m)   -> text "inv" <> parens (isar conf m)
    where
      -- pretty print a tuple as right associate list
      ppTup m@(MTup _ _) = nestShort n ldelim rdelim (fsep $ punctuate comma $ map (isar conf) $ split m)
      ppTup m = nestShort' "(" ")" (isar conf m)
      -- split right associate nested tuples
      split (MTup m1 m2) = m1 : split m2
      split m = [m]
      -- determine output parameters
      (n,ldelim,rdelim) 
        | isPlainStyle conf = (3, text "{|", text "|}")
        | otherwise        = (2, symbol "\\<lbrace>", symbol "\\<rbrace>") 


------------------------------------------------------------------------------
-- SP Theory Output
------------------------------------------------------------------------------

sptTID :: TID -> Doc
sptTID = text . show

sptArbMsgId :: ArbMsgId -> Doc
sptArbMsgId = (char 'a'  <>) . int . arbMsgId

sptLocalId :: LocalId -> Doc
sptLocalId (LocalId (i, tid)) = sptId i <> sptTID tid

sptFresh :: Fresh -> Doc
sptFresh = (char '~'  <>) . sptLocalId . getFresh

sptAVar :: AVar -> Doc
sptAVar = sptLocalId . getAVar

sptMVar :: MVar -> Doc
sptMVar = (char '?'  <>) . sptLocalId . getMVar

sptMessage :: Message -> Doc
sptMessage x = case x of
  (MConst i)    -> char '\'' <> sptId i <> char '\''
  (MFresh i)    -> sptFresh i
  (MAVar i)     -> sptAVar i
  (MArbMsg i)    -> sptArbMsgId i
  (MMVar i)     -> sptMVar i
  (MHash m)     -> text "h" <> ppBetween 1 "(" ")" m
  pt@(MTup _ _) -> ppBetween 1 "(" ")" pt
  (MEnc m k)    -> fcat [ppBetween 1 "{" "}" m, sptMessage k]
  (MSymK a b)   -> fcat [text "k(", sptMessage a, comma, sptMessage b, text ")"]
  (MShrK a b)   -> fcat [text "k[", sptMessage a, comma, sptMessage b, text "]"]
  (MAsymPK a)   -> text "pk" <> ppBetween 1 "(" ")" a
  (MAsymSK a)   -> text "sk" <> ppBetween 1 "(" ")" a
  (MInvKey m)   -> text "inv" <> ppBetween 1 "(" ")" m
  where
  -- pretty print a tuple as right associate list
  ppBetween n lead finish m@(MTup _ _) = 
    fcat . (text lead :) . (++[text finish]) . map (nest n) . punctuate (text ", ") . map sptMessage $ split m
  ppBetween _ lead finish m = text lead <> sptMessage m <> text finish
  -- split right associate nested tuples
  split (MTup m1 m2) = m1 : split m2
  split m = [m]

