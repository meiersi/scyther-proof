{-# LANGUAGE DeriveDataTypeable #-}
-- | Symbolic events that we are reasoning about
module Scyther.Event (
-- * Events
    Event(..)
  , substEv
  , substEvOrd
  , evTIDs
  , evOrdTIDs

  -- ** Event Order
  , EventOrder
  , cyclic
  , before

-- * Output
  , isaEvent
  , isaEventOrd
  , sptEvent
  , sptRawEvent
  , sptEventOrd
) where

import qualified Data.Set as S
import Data.Data

import Control.Arrow ( (***) )
import Control.Monad

import Text.Isar

import Scyther.Protocol
import Scyther.Message
import Scyther.Equalities

------------------------------------------------------------------------------
-- Events
------------------------------------------------------------------------------

-- | The logical denotation of an event of the execution of a security
-- protocol.
data Event =
    Step TID RoleStep -- ^ The thread executed the role step.
  | Learn Message     -- ^ The message was learnt by the intruder.
  deriving( Eq, Ord, Show, Data, Typeable )

-- | The event order induced by the trace of the reachable state we are
-- reasoning about.
type EventOrder = S.Set (Event,Event)

-- | Is the event order cyclic?
cyclic :: EventOrder -> Bool
cyclic evord =
  maybe True (const False) $ foldM visitForest S.empty (map fst evPairs)
  where
  evPairs = S.toList evord
  visitForest visited x
    | x `S.member` visited = return visited
    | otherwise            = findLoop S.empty visited x

  -- findLoop :: Ord n => S.Set n -> S.Set n -> n -> Maybe (S.Set n)
  findLoop parents visited x
    | x `S.member` parents = mzero
    | x `S.member` visited = return visited
    | otherwise            =
        S.insert x `liftM` foldM (findLoop parents') visited next
    where
    next = [ e' | (e,e') <- evPairs, e == x ]
    parents' = S.insert x parents

-- | Must an event have happened before another one with respect to the given
-- event order.
--
-- /before evord from to/ holds iff the event order /evord/ implies that the
-- event /from/ must have happened before the event /to/ in the reachable state
-- we are reasoning about.
before :: EventOrder -> Event -> Event -> Bool
before evord from to = existsPath S.empty [from]
  where
  evPairs = S.toList evord
  existsPath _ [] = False
  existsPath visited (x:xs)
    | x == to              = True
    | x `S.member` visited = existsPath visited xs
    | otherwise            =
        existsPath (S.insert x visited) (next ++ xs)
    where
    next = [ e' | (e,e') <- evPairs, e == x ]

-- | Substitute an event according to the equalities.
substEv :: Equalities -> Event -> Event
substEv eqs (Learn m)       = Learn (substMsg eqs m)
substEv eqs (Step tid step) = Step (substTID eqs tid) step

-- | Substitute an event order according to the equalities.
substEvOrd :: Equalities -> (Event, Event) -> (Event, Event)
substEvOrd eqs = substEv eqs *** substEv eqs

-- | The threads associated to an event.
evTIDs :: Event -> [TID]
evTIDs (Step tid _) = return tid
evTIDs (Learn m)    = msgTIDs m

-- | The threads associated to an event order.
evOrdTIDs :: (Event, Event) -> [TID]
evOrdTIDs (e1, e2) = evTIDs e1 `mplus` evTIDs e2


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- Helper function
------------------

eventTag :: (Event -> Doc) -- ^ Raw pretty printing function
         -> (Doc -> Doc)   -- ^ Modifier for learn events
         -> (Doc -> Doc)   -- ^ Modifier for step events
         -> Event -> Doc
eventTag pp ln _  ev@(Learn _)  = ln (pp ev)
eventTag pp _  st ev@(Step _ _) = st (pp ev)

-- Isar Output
--------------

-- | Pretty print the before order predicate.
esplBefore :: IsarConf -> Doc -> Doc -> Doc
esplBefore conf e1 e2
  | isPlainStyle conf = sep [text "predOrd t", nest 2 (parens e1), nest 2 (parens e2)]
  | otherwise         = sep [e1 <-> symbol "\\<prec>", e2]

-- | Render an event in the Isar format.
isaRawEvent :: Bool -> IsarConf -> Mapping -> Event -> Doc
isaRawEvent addParens conf _       (Learn m)       =
    (if addParens then parens else id) $ isar conf m
isaRawEvent _         conf mapping (Step tid step) =
    nestShort 2 lparen rparen (fsep [isar conf tid <> comma, ppStep])
  where
    ppStep = isaRoleStep conf (threadRole tid (getMappingEqs mapping)) step

-- | Render an event in the Isar format.
isaEvent :: IsarConf
         -> Mapping   -- ^ A mapping of the logical variables. The thread id to
                      -- role assigment is used for resolving steps to their
                      -- abbreviated notation consisting of role name plus step
                      -- label.
         -> Event -> Doc
isaEvent conf m =
    eventTag (isaRawEvent False conf m) (inSet "knows t") (inSet "steps t")
  where
    inSet set d = d <-> isaIn conf <-> text set

-- | Render an event order in the Isar format. See 'isaEvent' for an
-- explanation of the mapping.
isaEventOrd :: IsarConf -> Mapping -> (Event, Event) -> Doc
isaEventOrd conf m (e1, e2) =
    esplBefore conf (ppEv e1) (ppEv e2)
  where
    ppEv = eventTag (isaRawEvent True conf m) (text "Ln" <>) (text "St" <>)

instance Isar Event where
  isar conf = isaEvent conf (Mapping empty)


-- SP Theory Output
-------------------

-- | Render an event in security protocol theory format without any added
-- tagging; i.e. learned messages are rendered as is, and executed steps are
-- rendered as a tuple of thread identifier and role step (abbreviated if
-- possible).
sptRawEvent :: Mapping -> Event -> Doc
sptRawEvent _       (Learn m)       = sptMessage m
sptRawEvent mapping (Step tid step) =
    parens $ fsep [sptTID tid <> comma, ppStep]
  where
    ppStep = sptRoleStep (threadRole tid (getMappingEqs mapping)) step

-- | Render a fact that an event happened in security protocol theory format.
sptEvent :: Mapping -> Event -> Doc
sptEvent m = eventTag (sptRawEvent m) ((text "knows" <>) . parens) (text "step" <>)

-- | Render an event order in security protocol theory format.
sptEventOrd :: Mapping -> [Event] -> Doc
sptEventOrd m =
    fcat . punctuate (text " < ") . map ppEv
  where
    ppEv = eventTag (sptRawEvent m) ((text "Ln" <>) . parens) (text "St" <>)


