{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Pretty printing a security protocol theory.
module Scyther.Theory.Pretty (
    TaggedIdentityT(..)
  , runTaggedIdentityT
  , SlimOutput(..)
  , MarkupMonad(..)
  , PrettyMonad(..)
  , prettyTheory
  , prettySoundness
) where

import Data.Maybe
import Data.List
import qualified Data.Set as S
import Data.Traversable (sequenceA)

import Control.Basics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

import Extension.Prelude (sortednub)

import Text.Isar
import Text.Dot (Dot)

import qualified Scyther.Equalities as E
import Scyther.Facts
import Scyther.Sequent
import Scyther.Proof
import Scyther.Theory
import Scyther.Theory.Dot

------------------------------------------------------------------------------
-- Additional Helper Functions
------------------------------------------------------------------------------

-- FIXME: Remove this too general instance.
instance (Document d, Applicative f) => Document (f d) where
  char = pure . char
  text = pure . text
  zeroWidthText = pure . zeroWidthText
  emptyDoc = pure emptyDoc
  (<>)  = liftA2 (<>)
  (<->) = liftA2 (<->)
  hcat  = liftA hcat . sequenceA
  hsep  = liftA hsep . sequenceA
  ($$)  = liftA2 ($$)
  ($-$) = liftA2 ($-$)
  vcat  = liftA vcat  . sequenceA
  sep   = liftA sep   . sequenceA
  cat   = liftA cat   . sequenceA
  fsep  = liftA fsep  . sequenceA
  fcat  = liftA fcat  . sequenceA
  nest  = liftA2 nest . pure
  caseEmptyDoc = liftA3 caseEmptyDoc



------------------------------------------------------------------------------
-- A type-tagging identity monad transformer
------------------------------------------------------------------------------

newtype TaggedIdentityT t m a = TaggedIdentityT { unTaggedIdentityT :: m a }
  deriving( Functor, Applicative, Monad )

instance MonadTrans (TaggedIdentityT t) where
  lift = TaggedIdentityT

runTaggedIdentityT :: t -> TaggedIdentityT t m a -> m a
runTaggedIdentityT _ = unTaggedIdentityT


------------------------------------------------------------------------------
-- Monad Classes
------------------------------------------------------------------------------

-- | A monad for inserting markup into output.
class (Applicative m, Monad m) => MarkupMonad m where
  withGraph       :: Document d => Dot a -> m d -> m d
  withExplanation :: Document d => String -> m d -> m d
  theoremRef      :: Document d => Protocol -> String -> m d
  theoremDef      :: Document d => Theorem -> m d -> m d
  keyword         :: Document d => String -> m d -> m d
  noteCases       :: Document d => Dot a
                                -> [(String, Dot b)]  -- ^ named non-trivial cases
                                -> [(String, Dot b)]  -- ^ named trivial cases
                                -> m d -> m d

  withGraph _       = id
  withExplanation _ = id
  theoremRef _      = text
  theoremDef _      = id
  keyword _         = id
  noteCases _ _ _   = id

-- | A pretty printing monad allowing for economically replacing parts of the
-- pretty printer.
class MarkupMonad m => PrettyMonad m where
  -- components output
  prettyTID :: TID -> m Doc
  prettyArbMsgId :: ArbMsgId -> m Doc
  prettyMessage :: Message -> m Doc
  prettyFacts   :: Facts -> m ([Doc],[Doc],[Doc])
  prettyFormula :: E.Mapping -> Formula -> m Doc
  prettySequent :: Sequent -> m Doc
  -- proof output
  ensureProofMode :: (Bool, Bool) -> m Doc
  withFactsMode   :: (Bool, Bool) -> m Doc -> m Doc
  prettyTrivial :: TrivReason -> m Doc
  prettyMissing :: Sequent -> String -> m Doc
  prettySaturate :: Sequent -> m Doc
  prettyReduceInjectivity :: m Doc -> m Doc
  prettyForwardContradiction :: m Doc -> m Doc
  prettyForwardResolution :: m Doc -> Sequent -> E.Mapping -> m Doc
  prettyNextCase :: m Doc
  prettyChainRuleSplitCases :: [ChainRuleCase] -> m ([ChainRuleCase],[ChainRuleCase])
  prettyChainRuleApplication :: m Doc -> m Doc
  prettyChainRuleCase :: (String, [Either TID ArbMsgId]) -> m Doc
  prettyChainRuleQED :: Message -> [ChainRuleCase] -> m Doc
  prettyTypeCheckInduction :: String -> (m Doc, m Doc -> m Doc, m Doc)
  prettyTypingCase :: String -> String -> m Doc
  prettySplitEqCase :: PrettyMonad m => String -> m Doc
  prettySplitEqApplication :: PrettyMonad m => E.MsgEq -> m Doc
  prettySplitEqQed :: PrettyMonad m => m Doc
  -- theory output
  prettyComment  :: String -> m Doc
  prettyFormalComment  :: String -> String -> m Doc
  prettyProtoDef :: Protocol -> [Theorem] -> m Doc
  prettyTheorem :: Theorem -> m Doc
  prettyTheoryDef :: String -> Doc -> m Doc

-- | Abbreviation for one of the signature of 'prettyChainRuleSplitCases'.
type ChainRuleCase = ((String, [Either TID ArbMsgId]), Proof)

------------------------------------------------------------------------------
-- Functions shared by the different monad instances
------------------------------------------------------------------------------

-- Markup Monad
---------------

explainSequent :: Sequent -> String
explainSequent =
  render . runIdentity . runTaggedIdentityT SlimOutput . prettySequent

withExplainedSequent :: (Document d, MarkupMonad m) => Sequent -> m d -> m d
withExplainedSequent = withExplanation . explainSequent

withSequent :: (MarkupMonad m, Document d) => Sequent -> m d -> m d
withSequent se = withGraph (dotSequentMarked S.empty se) . withExplainedSequent se

withProofSequent :: (MarkupMonad m, Document d) => Proof -> m d -> m d
withProofSequent = withSequent . prfSequent


-- Pretty Printing Monad
------------------------

-- | Split a list of cases that can be converted to a proof into cases being
-- trivial due to one of the given triviality reasons, non trivial cases, and a
-- list of the trivial sequents together with the reasons occurring.
genericChainRuleSplitCases :: (a -> Proof) -> [a] -> (([a],[a]), [TrivReason])
genericChainRuleSplitCases sel cases =
  (partition (isNothing . check) cases, mapMaybe check cases)
  where
  check = extractTrivial . sel
  extractTrivial (Trivial se reason) = case reason of
    TrivContradictoryPremises   -> Just reason
    TrivLongTermKeySecrecy _    -> Nothing
    TrivPremisesImplyConclusion ->
      case seConcl se of
        FAtom (AHasType _) -> Just reason
        _                  -> Nothing
  extractTrivial _ = Nothing

-- | Pretty print a sequent with quantifiers, logical, and meta-logical facts for
-- the premise and a single document representing the conclusion.
prettySequentParts :: PrettyMonad m
                   => Sequent
                   -> m (([Doc], [Doc], [Doc]), SequentQualifier, Doc)
prettySequentParts (Sequent prem concl qualifier) = do
    ppPrem  <- prettyFacts prem
    ppConcl <- prettyFormula (eqsToMapping prem) concl
    return (ppPrem, qualifier, ppConcl)

-- | Pretty-print a sequent qualifier.
prettySequentQualifier :: PrettyMonad m => SequentQualifier -> m Doc
prettySequentQualifier Standard = emptyDoc
prettySequentQualifier Injective = text "injectively"

-- | Pretty print a proof.
prettyProof :: PrettyMonad m =>
            String       -- ^ Name of the theorem that is proven
         -> (Bool, Bool) -- ^ (facts are loaded, thesis is being proven)
         -> Proof
         -> m Doc
prettyProof _ _ (Axiom _) = emptyDoc

prettyProof _ prfConf (Trivial _ reason) =
  ensureProofMode prfConf <-> prettyTrivial reason

prettyProof _ _ (Missing se reason showSequent)
  | showSequent = withSequent se $ prettyMissing se reason
  | otherwise   = withSequent se $ prettyComment reason

prettyProof _ _ (PossibleAttack _ attack) =
  withSequent attack $ prettyMissing attack "possible attack found:"

prettyProof thName prfConf (RuleApp se Saturate [prf]) =
  withFactsMode prfConf $
    withProofSequent prf (prettySaturate se) $-$
    prettyProof thName (True, False) prf

prettyProof thName prfConf (RuleApp _ ReduceInjectivity [prf]) =
  withFactsMode prfConf $
    withProofSequent prf $
      prettyReduceInjectivity $ prettyProof thName (True, False) prf

--  A forward resolution that lead to no further proofs
prettyProof _ prfConf (RuleApp se (ForwardResolution (thName, _) _) []) =
  ensureProofMode prfConf <->
    prettyForwardContradiction (theoremRef (seProto se) thName)
-- a forward resolution with a single successor.
prettyProof outerThName prfConf (RuleApp se (ForwardResolution (thName, thSe) tideqs) [prf]) =
    wrapper $
      withProofSequent prf
        (prettyForwardResolution (theoremRef (seProto se) thName) thSe tideqs) $-$
      prettyProof outerThName newMode prf
  where
    isTyping = isTypingFormula . seConcl $ thSe
    (wrapper, newMode) | isTyping  = (id,                    prfConf      )
                       | otherwise = (withFactsMode prfConf, (True, False))
-- Note that all our forward resolutions currently have zero or one successor
-- proofs. Hence, this case is impossible.
prettyProof _ _ (RuleApp _ (ForwardResolution _ _) _) =
  error "prettyProof: forward resolution with more than one successors"

prettyProof thName prfConf (RuleApp se (ChainRule m names) prfs) = do
  (nonTrivialCases, trivialCases) <- prettyChainRuleSplitCases $ zip names prfs
  ppCases <- mapM selectCase nonTrivialCases
  let mkDot dotSe = dotSequentMarked (S.singleton . substEv (sePrem dotSe) $ Learn m) dotSe
      mkInfo ((caseName, _), prf) = (caseName, mkDot $ prfSequent prf)
  noteCases (mkDot se) (map mkInfo nonTrivialCases) (map mkInfo trivialCases)
    (withExplanation (explainSequent se)
      (ensureProofMode prfConf <-> prettyChainRuleApplication (prettyMessage m)))
    $-$
    vcat (intersperse prettyNextCase (map (pure . nest 2) ppCases)) $-$
    prettyChainRuleQED m trivialCases
  where
  selectCase (info, prf) =
    withProofSequent prf (prettyChainRuleCase info) $-$ prettyProof thName (True, False) prf

prettyProof thName _ (RuleApp se (TypingCases names) prfs) = do
    ppCases <- mapM ppCase $ zip names prfs
    let mkDot = dotSequentMarked S.empty . prfSequent
        nonTrivialCases = zip names $ map mkDot prfs
    noteCases (dotSequentMarked S.empty se) nonTrivialCases []
      (withExplanation (explainSequent se) pre)
      $-$
      modifier (vcat . intersperse prettyNextCase $ map (nest 2 . pure) ppCases) $-$
      post
  where
    (pre, modifier, post) = prettyTypeCheckInduction thName
    ppCase (name, prf) =
      let caseDoc = prettyTypingCase thName name
      in  withProofSequent prf caseDoc $-$ prettyProof thName (True, True) prf

prettyProof thName _ (RuleApp se (SplitEq eq@(MShrK _ _, MShrK _ _) [True,True]) prfs) = do
    ppCases <- mapM ppCase $ zip ["noswap","swapped"] prfs
    withExplanation (explainSequent se) (prettySplitEqApplication eq) $-$
      (vcat . intersperse prettyNextCase $ map (nest 2 . pure) ppCases) $-$
      prettySplitEqQed
  where
    ppCase (name, prf) =
        withProofSequent prf (prettySplitEqCase name) $-$
        prettyProof thName (True, False) prf

prettyProof _ _ (RuleApp _ rule _) = error $ "prettyProof: unmatched rule\n" ++ show rule

-- | Pretty print a theory item.
--
-- Note that this also ensures that quantifiers are made unique.
prettyThyItem :: PrettyMonad m => [ThyItem] -> ThyItem -> m Doc
prettyThyItem items (ThyProtocol proto) = prettyProtoDef proto
  [th | ThyTheorem th <- items, isAxiom th, thmProto th == proto]
prettyThyItem _ (ThySequent (name, se)) =
  prettyTheorem (name, Missing (uniqueTIDQuantifiers se) ("proof to be done") False)
prettyThyItem _ (ThyTheorem (name, prf)) =
  prettyTheorem (name, prf)
prettyThyItem _ (ThyText header txt) = prettyFormalComment header txt

-- | Pretty print a theory.
prettyTheory :: PrettyMonad m => Theory -> m Doc
prettyTheory (Theory name items) = do
  ppItems <- mapM (prettyThyItem items) items
  prettyTheoryDef name (vcat $ intersperse (text "") ppItems)

-- | Pretty print soundness information.
prettySoundness :: Applicative f => Theory -> f Doc
prettySoundness thy = case unsoundTheorems thy of
    []  -> emptyDoc
    ths -> vcat $
      map text ["", "(* NOTE that the proofs of the following theorems are UNSOUND:", ""] ++
      map ppThm ths ++
      map text ["*)"]
  where
    ppThm (p, name) = nest 5 $ text $ name ++ " (of " ++ protoName p ++ ")"

------------------------------------------------------------------------------
-- Monad Instances
------------------------------------------------------------------------------

-- Markup Monad
---------------

instance MarkupMonad Identity where
  -- deliberately empty: use default implementations

instance MarkupMonad m => MarkupMonad (ReaderT r m) where
  withGraph dot d       = ReaderT $ \r -> withGraph dot (runReaderT d r)
  withExplanation e d   = ReaderT $ \r -> withExplanation e (runReaderT d r)
  theoremRef proto      = lift . theoremRef proto
  theoremDef thm d      = ReaderT $ \r -> theoremDef thm (runReaderT d r)
  keyword tag d         = ReaderT $ \r -> keyword tag (runReaderT d r)
  noteCases se ntc tc d = ReaderT $ \r -> noteCases se ntc tc (runReaderT d r)

instance MarkupMonad m => MarkupMonad (TaggedIdentityT t m) where
  withGraph dot       = TaggedIdentityT . withGraph dot . unTaggedIdentityT
  withExplanation e   = TaggedIdentityT . withExplanation e . unTaggedIdentityT
  theoremRef proto    = lift . theoremRef proto
  theoremDef thm      = TaggedIdentityT . theoremDef thm . unTaggedIdentityT
  keyword tag         = TaggedIdentityT . keyword tag . unTaggedIdentityT
  noteCases se ntc tc  = TaggedIdentityT . noteCases se ntc tc . unTaggedIdentityT


-- ISAR Pretty Printing
-----------------------

-- | Convert a triviality reason to a string representing the corresponding
-- Isabelle tactic.
isaTactic :: TrivReason -> String
isaTactic TrivContradictoryPremises   = "((clarsimp, order?) | order | fast)"
isaTactic (TrivLongTermKeySecrecy _)  = "(auto dest!: ltk_secrecy)"
isaTactic TrivPremisesImplyConclusion = "(fastforce intro: event_predOrdI split: if_splits)"

-- | Isabelle proof of long-term key secrecy.
isaLongTermKeySecrecyProof :: Protocol -> Doc
isaLongTermKeySecrecyProof p = vcat $ map text
    [ "text{* Prove secrecy of long-term keys. *}"
    , "context " ++ stateLocale p ++ " begin"
    , ""
    , "  (* This rule is unsafe in general, but OK here, \n     as we are only reasoning about static compromise. \n  *)\n  lemma static_longterm_key_reveal[dest!]:\n    \"predOrd t (LKR a) e ==> RLKR a : reveals t\"\n    by (auto intro: compr_predOrdI)\n\n  lemma longterm_private_key_secrecy:\n    assumes facts:\n      \"SK m : knows t\"\n      \"RLKR m ~: reveals t\"\n    shows \"False\"\n  using facts by (sources \"SK m\")\n\n  lemma longterm_sym_ud_key_secrecy:\n    assumes facts:\n      \"K m1 m2 : knows t\"\n      \"RLKR m1 ~: reveals t\"\n      \"RLKR m2 ~: reveals t\"\n    shows \"False\"\n  using facts by (sources \"K m1 m2\")\n\n  lemma longterm_sym_bd_key_secrecy:\n    assumes facts:\n      \"Kbd m1 m2 : knows t\"\n      \"RLKR m1 ~: reveals t\"\n      \"RLKR m2 ~: reveals t\"\n      \"m1 : Agent\"\n      \"m2 : Agent\"\n    shows \"False\"\n  proof -\n    from facts \n    have \"KShr (agents {m1, m2}) : knows t\"\n      by (auto simp: Kbd_def)\n    thus ?thesis using facts\n    proof (sources \"KShr (agents {m1, m2})\")\n    qed (auto simp: agents_def Agent_def)\n  qed\n\n  lemmas ltk_secrecy =\n    longterm_sym_ud_key_secrecy\n    longterm_sym_ud_key_secrecy[OF in_knows_predOrd1]\n    longterm_sym_bd_key_secrecy\n    longterm_sym_bd_key_secrecy[OF in_knows_predOrd1]\n    longterm_private_key_secrecy\n    longterm_private_key_secrecy[OF in_knows_predOrd1]"
    , ""
    , "end"
    ]

-- | Pretty print a sequent as an Isabelle proposition.
isaSequentProp :: MarkupMonad m => Sequent -> ReaderT IsarConf m Doc
isaSequentProp se = do
  conf <- ask
  ( (premTids,  ppPremFacts, _), _qualifier, ppConcl ) <- prettySequentParts se
  let quantify q vs = case vs of
        [] -> id
        _  -> ((q conf <> fsep vs <> char '.') $$) . nest 2
      doc | nullFacts (sePrem se) = ppConcl
          | otherwise             = quantify isaMetaAll premTids . sep $
              [ fsep . (isaLBrack conf:) . map (nest 2) $ punctuate semi ppPremFacts
              , fsep [ isaRBrack conf <-> isaLongRightArrow conf , ppConcl ]
              ]
  pure doc

-- | Convert the name of the typing theorem to the name of the corresponding
-- locale.
typingLocale :: String -> String
typingLocale = (++ "_state")

-- | Pretty printing as an ISAR theory file is accomplished by using a reader
-- monad transformer with an ISAR output configuration as the environment.
instance MarkupMonad m => PrettyMonad (ReaderT IsarConf m) where
  -- components output
  prettyTID tid = isar <$> ask <*> pure tid
  prettyArbMsgId aid = isar <$> ask <*> pure aid
  prettyMessage m = isar <$> ask <*> pure m
  prettyFacts f = isaFacts <$> ask <*> pure f
  prettyFormula mapping form = do
    conf <- ask
    pure $ isaFormula conf mapping form
    -- case form of
      -- FFalse         -> singleFact $ text "False"
      -- (FFacts facts) -> isaFacts <$> ask <*> pure moreRoleEqs <*> pure facts
      -- (FHasType lid Nothing) -> do
        -- conf <- ask
        -- singleFact $ text "weakly-atomic" <> parens (isar conf lid)
      -- (FHasType lid (Just ty)) -> do
        -- conf <- ask
        -- singleFact $ text "has-type" <> parens (isar conf lid <> comma <-> isar conf ty)
      -- FTyping Nothing -> singleFact $ text "weakly-atomic"
      -- FTyping (Just typing) -> do
        -- conf <- ask
        -- singleFact $ isar conf typing
      -- where
      -- singleFact f = return ([], [f], [])
  prettySequent se = do
    ( (_, ppPremFacts, _), _qualifier, ppConcl) <- prettySequentParts se
    let doc | nullFacts (sePrem se) = doubleQuotes ppConcl
            | otherwise =
                text "assumes facts:" $-$
                (nest 2 . vcat $ map doubleQuotes ppPremFacts) $-$
                sep [text "shows", nest 2 $ doubleQuotes ppConcl]
    pure doc
  -- proof output
  ensureProofMode (factsLoaded, proofMode) =
    (if proofMode then emptyDoc else text "thus ?thesis") <->
    (if factsLoaded then emptyDoc else text "using facts")

  withFactsMode (_, proofMode) doc
    | proofMode = vcat [kwProof <-> text "-", nest 2 doc, kwQED]
    | otherwise = doc

  prettyTrivial reason = kwBy <-> text (isaTactic reason)
  prettyMissing se reason =
    nestShort' "(*" "*)" (text reason $-$ prettySequent se) <-> text "oops"
  prettySaturate _ =
    text "note_prefix_closed facts = facts"

  -- NOTE: Proof script works only for two-party authentication.
  prettyReduceInjectivity inner =
      ask >>= pp
    where
      pp conf = vcat
        [ lbrace
        , nest 2 $ vcat
          [ text "fix tid0 tid1"
          , text "assume facts: \"?prems tid0\""
          , text "have \"" <-> isaExists conf <> text "tid1. ?concs tid0 tid1\""
          , text "proof -"
          , nest 2 $ vcat
            [ text "note_unified facts = facts"
            , inner
            ]
          , text "qed"
          ]
        , rbrace
        , text "note niagree = this"
        , lbrace
        , nest 2 $ vcat
          [ text "fix i1 i2 j"
          , text "assume \"?concs i1 j" <-> isaAnd conf <-> text "?concs i2 j\""
          , text "note_unified facts = this"
          , text "have \"i1 = i2\" using facts by simp"
          ]
        , rbrace
        , text "note conc_inj = this"
        , text "show ?thesis"
        , text "  by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)"
        ]


  prettyForwardContradiction thRef =
    kwBy <-> text "(fastforce dest:" <-> thRef <-> text "intro: event_predOrdI)"
  prettyForwardResolution thRef thSe mapping
    | isJust . destTypingFormula . seConcl $ thSe = emptyDoc
    | otherwise = do
        conf <- ask
        let mappedPrems = applyMapping mapping $ sePrem thSe
            ppPrems = zip [1..] . map (isaAtom conf (eqsToMapping mappedPrems)) $
                      toAtoms mappedPrems
            ppPremProve (i, premFact) =
              text "have f" <> int i <> colon <-> doubleQuotes premFact <->
              text "using facts by (auto intro: event_predOrdI)"
            ppProven = pure . vcat $ map ppPremProve ppPrems
            ppResolve =
              thRef <> text "[OF" <> (hcat $ map ((text " f" <>) . int . fst) ppPrems) <>
                       text ", simplified]"
        ppProven $-$
          kwNote <-> text ("facts = facts") <-> ppResolve

  prettyNextCase = kwNext
  prettyChainRuleSplitCases = return . fst . genericChainRuleSplitCases snd
  prettyChainRuleApplication m =
    sep [ kwProof <> text "(sources! \"", nest 4 m <-> text "\")"]
  prettyChainRuleCase (name, newVars) =
    kwCase <-> selector <-> text "note_unified facts = this facts"
    where
    ppNewVar (Left tid)  = prettyTID tid
    ppNewVar (Right aid) = prettyArbMsgId aid
    selector
      | any (`isPrefixOf` name) ["ik0", "fake"] || null newVars = text name
      | otherwise = parens $ text name <-> hsep (map ppNewVar newVars)
  prettyChainRuleQED _ trivCases
    | null tactics = kwQED <-> text "(safe?, simp_all?, insert facts, (fastforce+)?)" -- be conservative
    | otherwise    =
        kwQED <-> text "(safe?, simp_all?, insert facts, ((" <> hsep (intersperse (text "|") tactics) <> text ")+)?)"
    where
      tactics = map text . nub . map isaTactic . snd $ genericChainRuleSplitCases snd trivCases

  prettyTypeCheckInduction typName =
    ( kwProof <-> text "-" $$
      ( nest 2 $ vcat
          [ text "have" <-> doubleQuotes
              (text "(t,r,s)" <-> (isaIn <$> ask) <-> text wellTypedStates)
          , kwProof <> text "(cases rule: reachable_in_approxI_ext"
          , text "      [OF" <-> text monoTyp <> text ", completeness_cases_rule])"
          ]
      )
    , nest 2
    , (nest 2 $ vcat
        [ kwQED
        , text "thus" <-> doubleQuotes (text (typingLocale typName) <-> text "t r s") <->
            text "by unfold_locales auto"
        ]
      ) $$ kwQED
    )
    where
      wellTypedStates = "approx " ++ typName
      monoTyp         = typName ++ ".monoTyp"

  prettyTypingCase typName name =
      kwCase <-> text ("("++ name ++" t r s") <-> prettyTID 0 <> text") note facts = this" $-$
          text ("then interpret state: "++ typingLocale typName ++" t r s") $-$
          nest 2 (text "by unfold_locales auto") $-$
          text "show ?case using facts"

  -- equality splitting
  prettySplitEqCase name =
      text "case" <-> text name <-> text "note_unified facts = this facts"

  prettySplitEqApplication eq =
    (fsep [ text "hence" <-> pure (doubleQuotes (isar defaultIsarConf (E.MsgEq eq)))
          , nest 2 $ text "by simp"
          , text "note facts = this facts" ]
    ) $-$
    (text "thus ?thesis proof(cases rule: Kbd_cases)")

  prettySplitEqQed = text "qed (fastforce+)?"

  -- theory output
  prettyComment comment = text "(*" <-> text comment <-> text "*)"
  prettyFormalComment header comment =
    text "(*" <-> text header <> colon <-> text comment <-> text "*)"
  prettyProtoDef proto axioms =
    withGraph (dotProtocol proto) $
      (isar <$> ask <*> pure proto) $-$
      text "" $-$
      (text restrictedLocaleDecl) $-$
      (nest 2 . vcat . map ppAxiom $ axioms)
    where
    restrictedLocaleDecl = concat
      [ "locale ", restrictedStateLocale proto, " = "++stateLocale proto
      , if null axioms then "" else " +" ]
    ppAxiom axiom =
      text "assumes" <-> text (thmName axiom) <> colon $-$
      (nest 2 . doubleQuotes . isaSequentProp $ thmSequent axiom)

  prettyTheorem th@(name, prf)
    | isAxiom th = emptyDoc
    | otherwise  =  case destTypingFormula (seConcl se) of
        Just typ -> ppTypingLocale typ
        Nothing  -> ask >>= ppLemma
    where
      p  = prfProto prf
      se = prfSequent prf
      ppPrf = prettyProof name (False, True) prf

      -- pretty print a lemma
      ppLemma conf =
          ppProp $-$ ppPrf
        where
          locale = "(in " ++ restrictedStateLocale (seProto $ prfSequent prf) ++ ") "
          ppName = keyword "property" (text "lemma") <-> text (locale ++ name ++ ":")
          ppProp = withProofSequent prf $ theoremDef th ppName $-$
            case seQualifier se of
              Standard  -> nest 2 (prettySequent se)
              Injective -> nest 2 (pure $ isaInjectivitySequent conf se)

      -- pretty print a typing locale definition
      ppTypingLocale typ = do
        conf <- ask
        vcat
          [ keyword "property" (text "type_invariant") <->
              text name <->
              text "for" <-> text (protoName p)
          , text "where \"" <> text name <-> text "= mk_typing" $$
              nest 2 (pure $ isar conf typ) <> char '"'
          , text ""
          , keyword "property" (text "sublocale") <->
              text (stateLocale p) <-> isaSublocale conf <-> text (typingLocale name)
          , ppPrf
          , text ""
          , pure $ isaLongTermKeySecrecyProof p
          ]

  prettyTheoryDef name body =
    text "theory" <-> doubleQuotes (text name) $-$
    text "imports" $-$
    nest 2 (vcat $ map (text . (++"\"") . ('"':)) imports) $-$
    text "begin" $-$ text "" $-$
    pure body $-$
    text "" $-$ text "end"
    where
    imports = ["ESPLogic"]


-- | Pretty-print an injectivity sequent. Works only for two-party
-- authentication; i.e., sequents that have one TID in the premise and one
-- additional, existentially quantified TID in the conclusion.
isaInjectivitySequent :: IsarConf -> Sequent -> Doc
isaInjectivitySequent conf se =
    doubleQuotes (
      vcat [ text "let"
           , nest 2 (sep [text "prems =", nest 2 $ ppPrems <> semi])
           , nest 2 (sep [text "concs =", nest 2 $ ppConcs])
           , text "in" <->
               isaExists conf <> text "f. inj_on f (Collect prems)" <-> isaAnd conf <->
               parens ( isaForall conf <> text "i. prems i" <->
                        isaImplies conf <-> text "concs i (f i)" )
           ]
    ) $-$
    text "(is \"let prems = ?prems; concs = ?concs in ?P prems concs\")"
  where
    premFormula = toFormula $ sePrem se
    premTIDs    = sortednub $ formulaTIDs premFormula
    premMapping = extendMapping premTIDs premFormula E.emptyMapping
    ppPrems     = abstract premMapping premTIDs premFormula

    (concTIDs0, concFormula) = dropTIDs [] $ seConcl se
    concTIDs = premTIDs ++ filter (not . (`elem` premTIDs)) concTIDs0
    concMapping = extendMapping concTIDs0 concFormula premMapping
    ppConcs  = abstract concMapping concTIDs concFormula

    abstract mapping tids fm = parens $ sep
        [ isaLambda conf <> hsep (map (isar conf) tids) <> text "."
        , nest 2 (isaFormula conf mapping fm)
        ]

    extendMapping tids fm mapping = foldr ($) mapping $
        [ maybe id (E.addTIDRoleMapping tid) (findRole tid fm) | tid <- tids ]

    dropTIDs tids (FExists (Left tid) fm) = dropTIDs (tid : tids) fm
    dropTIDs tids fm                      = (reverse tids, fm)


-- Slim Pretty Printing
-----------------------

-- | Phantom type marking slim output.
data SlimOutput = SlimOutput

-- | A slim output mode for better readability.
instance MarkupMonad m => PrettyMonad (TaggedIdentityT SlimOutput m) where
  -- components output
  prettyTID = pure . sptTID
  prettyArbMsgId = pure . sptArbMsgId
  prettyMessage = pure . sptMessage
  prettyFacts = pure . sptFacts
  prettyFormula mapping form = pure $ sptFormula mapping form
    -- case form of
      -- FFalse                 -> singleFact $ text "False"
      -- FFacts facts           -> pure $ sptFacts moreRoleEqs facts
      -- FHasType lid Nothing   -> singleFact $ text "weakly-atomic" <> parens (sptLocalId lid)
      -- FHasType lid (Just ty) ->
        -- singleFact $ text "hasType" <> parens (sptLocalId lid <> comma <-> sptType sptRoleStep ty)
      -- FTyping Nothing        -> singleFact $ text "weakly-atomic"
      -- FTyping (Just typing)  -> singleFact $ sptTyping typing
      -- where
      -- singleFact f = return ([], [f], [])
  prettySequent se = do
    ((premQuantified,  ppPremRepr, ppPremNonRepr), qualifier, ppConclRaw)
        <- prettySequentParts se
    let ppPremFacts  = ppPremRepr ++ ppPremNonRepr
        premQuantifier = pure $ case premQuantified of
          [] -> text "premises"
          _  -> text "for all" <-> fsep premQuantified <-> text "the premises"
        ppConcl =  kwFact . pure $ doubleQuotes ppConclRaw
        doc | nullFacts (sePrem se) = ppConcl
            | otherwise =
                premQuantifier $-$
                (nest 2 . vcat $ map (kwFact . pure . doubleQuotes) ppPremFacts) $-$
                (sep [ text "imply" <-> prettySequentQualifier qualifier
                     , nest 2 ppConcl])
    doc
  -- proof output
  ensureProofMode _ = emptyDoc
  withFactsMode _   = id
  prettyTrivial reason = case reason of
    TrivPremisesImplyConclusion -> text "tautology"
    TrivLongTermKeySecrecy key  ->
      text "contradicts secrecy of" <-> pure (sptMessage key)
    _  -> emptyDoc
  prettyMissing se reason =
    nestShort' "(*" "*)" (text reason $-$ prettySequent se)
  prettySaturate _ = keyword "proof" $ text "saturate"
  prettyReduceInjectivity inner =
      keyword "proof" (text "reduce_injectivity") $-$ inner
  prettyForwardContradiction thRef = text "contradictory due to '" <> thRef <> text "'"
  prettyForwardResolution thRef _ mapping =
    keyword "proof" (text "resolve") <-> text "'" <> thRef <> ppMapping
    where
    ppMapping | null (E.toAnyEqs (E.getMappingEqs mapping)) = emptyDoc
              | otherwise = text "' mapping" <-> ppTidEqs
    ppTidEqs = pure . hsep . punctuate comma . map E.sptAnyEq . E.toAnyEqs $
               E.getMappingEqs mapping
  prettyNextCase = kwNext
  prettyChainRuleSplitCases = return . fst . genericChainRuleSplitCases snd
  prettyChainRuleApplication m =
    sep [ keyword "proof" (text "sources") <> lparen,
          nest 4 (m <-> rparen)]
  prettyChainRuleCase (name, newVars) =
    kwCase <-> selector
    where
    ppNewVar (Left tid)  = prettyTID tid
    ppNewVar (Right aid) = prettyArbMsgId aid
    selector
      | any (`isPrefixOf` name) ["ik0", "fake"] || null newVars = text name
      | otherwise = parens $ text name <-> hsep (map ppNewVar newVars)
  prettyChainRuleQED _ trivCases = case trivCases of
    []  -> kwQED
    _   -> kwQED <-> parens (int (length trivCases) <-> text "trivial")

  prettyTypeCheckInduction _ = (kwProof, id, kwQED)
  prettyTypingCase _ name = kwCase <-> text name

  -- equality splitting
  prettySplitEqCase name = text "case" <-> text name

  prettySplitEqApplication eq =
    sep [ keyword "proof" (text "split") <> lparen,
          nest 4 (pure $ E.sptAnyEq (E.MsgEq eq) <-> rparen)]

  prettySplitEqQed = text "qed"

  -- theory output
  prettyComment comment = text "/*" <-> text comment <-> text "*/"
  prettyFormalComment header comment =
      text (header ++ "{*") <> text comment <> text "*}"
  prettyProtoDef proto _ = withGraph (dotProtocol proto) (pure $ sptProtocol proto)

  -- | Pretty print a theorem.
  prettyTheorem th@(name, prf) =
    withProofSequent prf ppProp $-$ ppPrf
    where
    p = prfProto prf
    thmType | isAxiom th = "axiom"
            | otherwise  = "property"
    ppName = keyword "property" (text thmType) <->
             text ("(of "++protoName p++") "++name++":")
    ppProp = theoremDef th ppName $-$ nest 2 (prettySequent $ prfSequent prf)
    ppPrf  = prettyProof name (False, True) prf

  prettyTheoryDef name body = vcat [
      keyword "theory" (text "theory") <-> text name <->
      keyword "theory" (text "begin")
    , text ""
    , pure body
    , text ""
    , keyword "theory" (text "end") ]

kwFact :: (MarkupMonad m, Document d) => m d -> m d
kwFact = keyword "fact"

kwProof :: (MarkupMonad m, Document d) => m d
kwProof = keyword "proof" $ text "proof"

kwCase :: (MarkupMonad m, Document d) => m d
kwCase = keyword "proof" $ text "case"

kwNext :: (MarkupMonad m, Document d) => m d
kwNext = keyword "proof" $ text "next"

kwQED :: (MarkupMonad m, Document d) => m d
kwQED = keyword "proof" $ text "qed"

kwBy  :: (MarkupMonad m, Document d) => m d
kwBy = keyword "proof" $ text "by"

kwNote  :: (MarkupMonad m, Document d) => m d
kwNote = keyword "proof" $ text "note"

------------------------------------------------------------------------------
-- ISAR Output
------------------------------------------------------------------------------

{-
instance Isar Sequent where
  isar conf se = runReader (prettySequent se) conf
instance Isar Proof where
  isar conf prf = runReader (prettyProof "" (False, True) prf) conf

-- instance Isar Theorem where
  -- isar conf thm = runReader (prettyTheorem thm Nothing) conf

instance Isar ThyItem where
  isar conf item = runReader (prettyThyItem [] item) conf

instance Isar Theory where
  isar conf thy = runReader (prettyTheory thy) conf
-}
