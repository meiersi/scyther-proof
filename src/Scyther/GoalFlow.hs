-- | Dependency analysis of goals occurring during security proofs.
module Scyther.GoalFlow where

import Control.Monad

import Data.DAG.Simple
import Data.Maybe
import Data.List
import qualified Data.Set as S

import Text.Isar

import Scyther.Protocol
import Scyther.Message
import Scyther.Equalities
import Scyther.Theory

unifiable :: Message -> Message -> Bool
unifiable m1 m2 = isJust $ solve [MsgEq (m1, m2)] empty

-- | All flows from a sent pattern to a received pattern.
patternFlows :: Pattern -> Pattern -> [(Message, Message, Equalities)]
patternFlows ptSend ptRecv = do
  m1 <- S.toList $ messageparts mSend
  m2 <- S.toList $ submessages mRecv
  guard (isEncOrHash m1 && isEncOrHash m2)
  eqs <- solve [MsgEq (m1, m2)] empty
  return (m1, m2, eqs)
  where
  mSend = inst 0 ptSend
  mRecv = inst 1 ptRecv
  isEncOrHash (MEnc _ _) = True
  isEncOrHash (MHash _)  = True
  isEncOrHash _          = False

-- | All flows between different protocols
protoFlows :: Protocol -> [(((Role,RoleStep),Message),((Role,RoleStep),Message),Equalities)]
protoFlows proto = do
  send@(_, Send _ ptSend) <- steps
  recv@(_, Recv _ ptRecv) <- steps
  (mSend, mRecv, eqs) <- patternFlows ptSend ptRecv
  return ((send, mSend), (recv, mRecv), eqs)
  where
  steps = concat [ zip (repeat role) (roleSteps role) | role <- protoRoles proto ]

sptProtoFlows :: Protocol -> Doc
sptProtoFlows = vcat . map ppFlow . protoFlows
  where
  ppFlow ((send, mSend), (recv, mRecv), eqs) =
    ppLoc send <-> char '<' <-> ppLoc recv <> char ':' $-$
    nest 4 (sep [sptMessage mSend, char '=' <-> sptMessage mRecv]) $-$
    nest 2 (text "==>") $-$
    nest 4 (fsep . punctuate comma . map sptAnyEq $ toAnyEqs eqs)
  ppLoc (role, step) = sptRoleStep (Just role) step

type MsgVarNonces = S.Set ((Role, Id), (Role, Id))

roleRel :: Protocol -> [((Role,RoleStep),(Role,RoleStep))]
roleRel = concatMap rel . protoRoles
  where
  rel role = zip steps (tail steps)
    where
    steps = zip (repeat role) (roleSteps role)

-- computing the msg-variable-nonces
--
--   1. determine combined relation: roleOrd + msgFlow
--   2. toposort
--   3. in order of toposort, for every receive determine
--      first received msg. vars
--   4. for every first received msg. var, for every flow
--      equating it, transfer assignments
--
sptMsgVarAnn :: Protocol -> Doc
sptMsgVarAnn proto =
  (if acyclic then emptyDoc else text "WARNING: full relation is cyclic") $-$
  (fsep . punctuate (text " <") $ map ppStep steps)
  where
  fullRel = roleRel proto ++ flowRel proto
  steps = toposort fullRel
  ppStep (role, step) = sptRoleStep (Just role) step
  acyclic = True -- TODO: Implement check

{-
  findTargets :: Message -> [AnyEq] -> [Either Fresh MsgVar]
  findTargets v eqs = do
    MsgEq (m1, m2) <- eqs
    (do guard (m1 == v)
        extractTarget m2
     `mplus`
     do guard (m2 == v)
        extractTarget m1)
    where
    extractTarget m = case m of
      Fresh  _ -> return . Left $ m2
      MsgVar _ -> return . Right $ m2
      _        -> mzero -- TODO: Make this more precise; i.e. its not
                        -- always safe to ignore.

  updateAnn :: (Role,RoleStep) -> MsgVarNonces -> MsgVarNonces
  updateAnn (role, step) ann = do
    v <- firstRecvs role step
    (send, (mSend, sendTid), (mRecv, recvTid), eqs) <- inFlows proto (stepPat step)
    x <- findTargets (MsgVar (LocalId (v, recvTid))) $ toAnyEqs eqs
    case x of
      --- ... seems like the wrong approach.
      --  simulate algorithm more precisely, over-approximating some structures
      --  and use fixpoint
    ann `S.union`
    S.fromList [
    where

inFlows :: Protocol -> Pattern ->
           [(((Role,RoleStep),(Message,TID),(Message,TID),Equalities)]
inFlows proto ptRecv = do
  send@(_, Send _ ptSend) <- protoSteps proto
  mSend <- S.toList $ messageparts $ inst sendTID ptSend
  mRecv <- S.toList $ submessages  $ inst recvTID ptRecv
  guard (isEnc mSend && isEnc mRecv)
  eqs <- solve [MsgEq (mSend, mRecv)] empty
  return ((send, (mSend,sendTid), (mRecv,recvTid), eqs)
  where
  sendTid = 0
  recvTid = 1
  steps = protoSteps proto
  isEnc (MEnc _ _) = True
  isEnc _          = False

-}

firstRecvs :: Role -> RoleStep -> S.Set Id
firstRecvs role recv@(Recv _ pt) =
  patFMV pt `S.difference`
  (S.unions . map (patFMV . stepPat) $ takeWhile (/= recv) (roleSteps role))
firstRecvs _         _           = S.empty

-- | The role steps of a protocol.
protoSteps :: Protocol -> [(Role, RoleStep)]
protoSteps proto =
  concat [ zip (repeat role) (roleSteps role) | role <- protoRoles proto ]

sptFirstRecvs :: Protocol -> Doc
sptFirstRecvs proto = vcat $ map ppStep steps
  where
  steps = concat [ zip (repeat role) (roleSteps role) | role <- protoRoles proto ]
  ppStep (role, step) =
    sptRoleStep (Just role) step <> char ':' <->
    (fsep . punctuate comma . map sptId . S.toList $ firstRecvs role step)

existsFlow :: Pattern -> Pattern -> Bool
existsFlow ptSend ptRecv = or
  [ unifiable m1 m2
  | m1 <- S.toList $ messageparts mSend,
    m2 <- S.toList $ submessages mRecv,
    isEncOrHash m1,
    isEncOrHash m2
  ]
  where
  mSend = inst 0 ptSend
  mRecv = inst 1 ptRecv
  isEncOrHash (MEnc _ _) = True
  isEncOrHash (MHash _)  = True
  isEncOrHash _          = False


-- | Compute the message flow relation.
--
-- TLS has a backwards flow but only in the same thread, it depends on the
-- precise nature of such flow a if it is a problem or not; i.e. if it can be
-- used to introduce a cyclic new thread dependency.
--
-- The argument to use here is to incorporate the intra-thread flow into the
-- flow-induced-role-step-dependency computation
flowRel :: Protocol -> [((Role,RoleStep), (Role,RoleStep))]
flowRel proto = do
  [ (send, recv) | send@(_, Send _ ptSend) <- steps,
                   recv@(_, Recv _ ptRecv) <- steps, existsFlow ptSend ptRecv ]
  where
  steps = protoSteps proto

sptProtoOrders :: Protocol -> Doc
sptProtoOrders proto =
  text "role ord:" $-$
  nest 2 (ppRel $ roleRel proto) $-$
  text "flow rel:" $-$
  nest 2 (ppRel $ flowRel proto) $-$
  text "annotated flows:" $-$
  nest 2 (sptProtoFlows proto) $-$
  text "first receives:" $-$
  nest 2 (sptFirstRecvs proto) $-$
  text "topological sort according to flow:" $-$
  nest 2 (sptMsgVarAnn  proto)
  where
  ppRel = fsep . punctuate comma . map ppPair
  ppPair (x,y) = ppStep x <-> char '<' <-> ppStep y
  ppStep (role, step) = sptRoleStep (Just role) step


goalFlowAnalysis :: Theory -> Doc
goalFlowAnalysis (Theory _ items) =
  vcat . intersperse (text "") $ [ analyzeProto p | ThyProtocol p <- items ]
  where
  analyzeProto proto =
    sptProtocol proto $-$
    text "" $-$
    sptProtoOrders proto
