module Scyther.Theory.Parser (

  -- * Lexing
    Token
  , Keyword(..)
  , scanString
  , scanFile

  -- * Parsing
  , Parser
  , parseFile

  -- ** Additional combinators
  , liftMaybe
  , liftMaybe'
  , token

  -- ** Keyword combinations
  , kw
  , betweenKWs
  , commaSep
  , commaSep1
  , list
  , braced
  , parens
  , brackets
  , singleQuoted
  , doubleQuoted
  , identifier
  , string
  , strings
  , integer
  , genFunOpen
  , genFunApp
  , funOpen
  , funApp
 
  -- ** Security protocol theorys for the free-algebra
  , protocol
  , claims
  , theory
  , parseTheory

  -- * Extended patterns
  , mkLTSPat
  , mkMultIdentityPat
  , mkExpPat
  , mkMultPat
  , destLTSPat
  , destMultIdentityPat
  , destExpPat
  , destMultPat
  ) where

import Data.Char
import Data.List
import qualified Data.Set as S
import Data.DAG.Simple
import Data.Foldable (asum)

import Control.Arrow ( (***) )
import Control.Monad hiding (sequence)

import Control.Applicative hiding (empty, many, optional)

import           Text.Parsec hiding (token, (<|>), string )
import qualified Text.Parsec as P
import           Text.Parsec.Pos

import qualified Scyther.Equalities as E
import Scyther.Facts as F hiding (protocol)
import Scyther.Sequent
import Scyther.Proof
import Scyther.Theory
import Scyther.Theory.Lexer (Keyword(..), TextType(..), runAlex, AlexPosn(..), alexGetPos, alexMonadScan)

------------------------------------------------------------------------------
-- Specializing Parsec to our needs
------------------------------------------------------------------------------

-- Scanner
----------

-- | The tokens delivered by our Alex based scanner
type Token = (SourcePos, Keyword)

-- | Scan a string using the given filename in the error messages.
--
-- NOTE: Lexical errors are thrown using 'error'.
scanString :: FilePath -> String -> [Token]
scanString filename s = 
  case runAlex s gatherUntilEOF of
    Left err  -> error err
    Right kws -> kws
  where
  gatherUntilEOF = do
    AlexPn _ line col <- alexGetPos
    let pos = newPos filename line col
    k <- alexMonadScan
    case k of 
      EOF -> return [(pos,EOF)]
      _   -> do kws <- gatherUntilEOF
                return $ (pos,k) : kws

-- Parser
---------

-- | A parser with an arbitrary user state for a stream of tokens.
type Parser s a = Parsec [Token] s a

-- | Lift a maybe to a monad plus action.
liftMaybe :: MonadPlus m => Maybe a -> m a
liftMaybe = maybe mzero return

-- | Lift a maybe to a monad action with the given failure message.
liftMaybe' :: Monad m => String -> Maybe a -> m a
liftMaybe' msg = maybe (fail msg) return

-- | Parse a token based on the acceptance condition
token :: (Keyword -> Maybe a) -> Parser s a
token p = P.token (show . snd) fst (p . snd)

-- | Parse a term.
kw :: Keyword -> Parser s ()
kw t = token check
  where 
  check t' | t == t' = Just () | otherwise = Nothing

-- | Parse content between keywords.
betweenKWs :: Keyword -> Keyword -> Parser s a -> Parser s a
betweenKWs l r = between (kw l) (kw r)

-- | Between braces.
braced :: Parser s a -> Parser s a
braced = betweenKWs LBRACE RBRACE

-- | Between parentheses.
parens :: Parser s a -> Parser s a
parens = betweenKWs LPAREN RPAREN

-- | Between parentheses.
brackets :: Parser s a -> Parser s a
brackets = betweenKWs LBRACKET RBRACKET

-- | Between single quotes.
singleQuoted :: Parser s a -> Parser s a
singleQuoted = betweenKWs SQUOTE SQUOTE

-- | Between double quotes.
doubleQuoted :: Parser s a -> Parser s a
doubleQuoted = betweenKWs DQUOTE DQUOTE

-- | Parse an identifier as a string
identifier :: Parser s String
identifier = token extract
  where extract (IDENT name) = Just $ name
        extract _            = Nothing

-- | Parse a fixed string which could be an identifier.
string :: String -> Parser s ()
string cs = (try $ do { i <- identifier; guard (i == cs) }) <?> ('`' : cs ++ "'")

-- | Parse a sequence of fixed strings.
strings :: [String] -> Parser s ()
strings = mapM_ string

-- | Parse an integer.
integer :: Parser s Int
integer = do i <- identifier
             guard (all isDigit i)
             return (read i)

-- | A comma separated list of elements.
commaSep :: Parser s a -> Parser s [a]
commaSep = (`sepBy` kw COMMA)

-- | A comma separated non-empty list of elements.
commaSep1 :: Parser s a -> Parser s [a]
commaSep1 = (`sepBy1` kw COMMA)

-- | Parse a list of items '[' item ',' ... ',' item ']'
list :: Parser s a -> Parser s [a]
list p = kw LBRACKET *> commaSep p <* kw RBRACKET


------------------------------------------------------------------------------
-- Lexing, parsing and proving theory files
------------------------------------------------------------------------------

-- Lexing
---------

-- | Scan a file
scanFile :: FilePath -> IO [Token]
scanFile f = do
  s <- readFile f
  return $ scanString f s

-- Parsing
----------

-- | Parser s a theory file.
parseFile :: Parser s a -> s -> FilePath -> IO a
parseFile parser state f = do
  s <- readFile f
  case runParser parser state f (scanString f s) of
    Right p -> return p
    Left err -> error $ show err

-- | Parse a security protocol theory given as a string using the given
-- filename for the error messages 
parseTheory :: FilePath -> IO Theory
parseTheory = parseFile theory ()

------------------------------------------------------------------------------
-- Parsing Patterns and Messages
------------------------------------------------------------------------------

-- | An identifier.
ident :: Parser s Id
ident = Id <$> identifier

-- | Left-hand-side of a function application written with the given delimiter.
genFunOpen :: Parser s a -> Parser s b -> Parser s a
genFunOpen ldelim f = try $ f *> ldelim

-- | Left-hand-side of a function application.
genFunApp :: Parser s a -> Parser s b -> Parser s d -> Parser s c -> Parser s c
genFunApp ldelim rdelim f arg = genFunOpen ldelim f *> arg <* rdelim

-- | Left-hand-side of a function application.
funOpen :: String -> Parser s ()
funOpen = genFunOpen (kw LPAREN) . string

-- | A function application.
funApp :: String -> Parser s a -> Parser s a
funApp = genFunApp (kw LPAREN) (kw RPAREN) . string

-- Extended patterns supported by the parser but not by the underlying free
-- term algebra. They are used in the 'scyther-ac-proof' application.
---------------------------------------------------------------------------

mkLTSPat :: Pattern -> Pattern
mkLTSPat x      = PHash (PTup (PConst (Id "PARSE_LTS")) x)

mkMultIdentityPat :: Pattern
mkMultIdentityPat = PHash (PConst (Id "PARSE_MULT_IDENTITY"))

mkExpPat :: Pattern -> Pattern -> Pattern
mkExpPat x y    = PHash (PTup (PConst (Id "PARSE_EXP")) (PTup x y))

mkMultPat :: Pattern -> Pattern -> Pattern
mkMultPat x y   = PHash (PTup (PConst (Id "PARSE_MULT")) (PTup x y))

destLTSPat :: Pattern -> Maybe Pattern
destLTSPat (PHash (PTup (PConst (Id "PARSE_LTS")) x)) = return x
destLTSPat _ = mzero

destMultIdentityPat :: Pattern -> Maybe ()
destMultIdentityPat (PHash (PConst (Id "PARSE_MULT_IDENTITY"))) = return ()
destMultIdentityPat _ = mzero

destExpPat :: Pattern -> Maybe (Pattern, Pattern)
destExpPat (PHash (PTup (PConst (Id "PARSE_EXP")) (PTup x y))) = return (x,y)
destExpPat _ = mzero

destMultPat :: Pattern -> Maybe (Pattern, Pattern)
destMultPat (PHash (PTup (PConst (Id "PARSE_MULT")) (PTup x y))) = return (x,y)
destMultPat _ = mzero



-- Patterns
-----------

-- | Parse a pattern.
-- NOTE: All local atoms (MFresh, MMVar, MAVar) are set to MMVar with a space
-- preceding the identifier to mark it for later resolution.
--
-- TODO: Remove this ugly string hack.
pattern :: Parser s Pattern
pattern = asum
    [              string "1" *> pure mkMultIdentityPat
    , PConst   <$> singleQuoted ident
    , PMVar    <$> (kw QUESTIONMARK *> ident)
    , PAVar    <$> (kw DOLLAR *> ident)
    , PFresh   <$> (kw TILDE *> ident)
    , parens tuplepattern
    , PHash    <$> funApp "h" tuplepattern
    , mkLTSPat <$> funApp "lts" tuplepattern
    , PSymK    <$> (try (funOpen "k") *> multpattern <* kw COMMA) <*> (multpattern <* kw RPAREN)
    , PShrK    <$> (try (string "k" *> kw LBRACKET) *> multpattern <* kw COMMA)
               <*> (multpattern <* kw RBRACKET)
    , PAsymPK  <$> funApp "pk" tuplepattern
    , PAsymSK  <$> funApp "sk" tuplepattern
    , PEnc     <$> braced tuplepattern <*> pattern
    , PSign    <$> genFunApp (kw LBRACE) (kw RBRACE) (string "sign") tuplepattern <*> pattern
    , PMVar    <$> tempIdentifier
    ]
  where
    tempIdentifier = do i <- identifier
                        if isLetter (head i)
                          then return (Id (' ':i))
                          else fail $ "invalid variable name '" ++ i ++
                                      "': variable names must start with a letter"

-- | Parse multiple ^ applications as a left-associative list of exponentations
-- hackily marked using hashes and constant identifiers.
exppattern :: Parser s Pattern
exppattern = chainl1 pattern (mkExpPat <$ kw HAT)

-- | Parse multiple ^ applications as a left-associative list of
-- multiplications hackily marked using hashes and constant identifiers.
multpattern :: Parser s Pattern
multpattern = chainl1 exppattern (mkMultPat <$ kw STAR)

-- | Parse a comma separated list of patterns as a sequence of
-- right-associative tuples.
tuplepattern :: Parser s Pattern
tuplepattern = chainr1 multpattern (PTup <$ kw COMMA)

-- | Drops the space prefix used for identifying identifiers that need to be
-- resolved later.
dropSpacePrefix :: Id -> Id
dropSpacePrefix (Id (' ':i)) = Id i
dropSpacePrefix i            = i

-- | Resolve the type of a local identifier according to the sets of agent
-- variables and the set of message variables. Fresh messages are the ones
-- which are in none these sets.
resolveId :: S.Set Id -> S.Set Id -> Id -> Pattern
resolveId avars mvars i
  | i `S.member` avars = PAVar i
  | i `S.member` mvars = PMVar i
  | otherwise          = PFresh i

-- | Resolve all identifiers in the pattern.
resolveIds :: S.Set Id -> S.Set Id -> Pattern -> Pattern
resolveIds avars mvars = go
  where 
  resolve = resolveId avars mvars
  go pt@(PConst _)   = pt
  go pt@(PFresh _)   = pt
  go pt@(PAVar _)    = pt
  go pt@(PMVar i)    = case getId i of
                         ' ':i' -> resolve (Id i') -- marked for resolution
                         _      -> pt
  go (PHash pt)      = PHash   (go pt)
  go (PTup pt1 pt2)  = PTup    (go pt1) (go pt2)
  go (PEnc pt1 pt2)  = PEnc    (go pt1) (go pt2)
  go (PSign pt1 pt2) = PSign   (go pt1) (go pt2)
  go (PSymK pt1 pt2) = PSymK   (go pt1) (go pt2)
  go (PShrK pt1 pt2) = PShrK   (go pt1) (go pt2)
  go (PAsymPK pt)    = PAsymPK (go pt)
  go (PAsymSK pt)    = PAsymSK (go pt)

-- | Resolve identifiers as identifiers of the given role.
-- PRE: The role must use disjoint identifiers for fresh messages, agent
-- variables, and message variables.
resolveIdsLocalToRole :: Role -> Pattern -> Pattern
resolveIdsLocalToRole role = resolveIds (roleFAV role) (roleFMV role) 


-- Messages
-----------

-- | Parse a thread identifier.
threadId :: Parser s TID
threadId = TID <$> (kw SHARP *> integer)

-- | Parse a local identifier.
localIdentifier :: Parser s LocalId
localIdentifier = LocalId <$> ((,) <$> ident <*> threadId)

-- | Resolve a thread identifier
resolveTID :: MonadPlus m => E.Mapping -> TID -> m Role
resolveTID mapping tid =
  liftMaybe' ("resolveTID: no role assigned to thread "++show tid) 
             (E.threadRole tid (E.getMappingEqs mapping))

-- | Resolve a local identifier.
-- PRE: Thread id must be in the role equalities.
resolveLocalId :: MonadPlus m => E.Mapping -> LocalId -> m Message
resolveLocalId mapping (LocalId (i, tid)) = 
  do role <- resolveTID mapping tid
     return $ inst tid (resolveId (roleFAV role) (roleFMV role) i)
  `mplus`
  (fail $ "resolveLocalId: no role defined for thread " ++ show tid)

-- | Resolve an executed step.
resolveStep :: MonadPlus m => E.Mapping -> TID -> String -> m RoleStep
resolveStep mapping tid stepId = do
  role <- resolveTID mapping tid
  let roleId = roleName role
  if isPrefixOf roleId stepId
    then liftMaybe' ("resolveStep: step '"++stepId++"' not part of role '"++roleName role++"'") 
                    (lookupRoleStep (drop (length roleId + 1) stepId) role)
    else fail ("resolveStep: role of step '"++stepId++"' does not agree to role '"
               ++roleName role++"' of thread "++show tid) 

-- | Parse an instantiation of a pattern.
instantiation :: MonadPlus m => Parser s (E.Mapping -> m Message)
instantiation = do 
  tid <- TID <$> (funOpen "inst" *> integer <* kw COMMA)
  m <- (do i <- identifier 
           let (stepId, iTyp) = splitAt (length i - 3) i
           when (iTyp /= "_pt") (fail $ "inst: could not resolve pattern '"++i++"'")
           return $ \mapping -> do
             step <- resolveStep mapping tid stepId
             return (inst tid $ stepPat step)
        `mplus`
        do pt <- pattern
           return $ \mapping -> do
             role <- resolveTID mapping tid
             return (inst tid $ resolveIds (roleFAV role) (roleFMV role) pt)
       )
  kw RPAREN
  return m

-- Parse a message.
message :: MonadPlus m => Parser s (E.Mapping -> m Message)
message = asum
  [ instantiation
  , (pure . return . MConst) <$> betweenKWs SQUOTE SQUOTE ident
  , parens tuplemessage
  , (liftA  $ liftM  MHash)   <$> funApp "h" tuplemessage
  , (liftA2 $ liftM2 MSymK)   <$> (funOpen "k" *> message) <*> (kw COMMA *> message <* kw RPAREN)
  , (liftA  $ liftM  MAsymPK) <$> funApp "pk" message
  , (liftA  $ liftM  MAsymSK) <$> funApp "sk" message
  , (liftA2 $ liftM2 MEnc)    <$> braced tuplemessage <*> message
  , (liftA  $ liftM  MInvKey) <$> funApp "inv" tuplemessage
  , (flip resolveLocalId)  <$> localIdentifier
  ]

-- | Parse a comma separated list of patterns as a sequence of
-- right-associative tuples.
tuplemessage :: MonadPlus m => Parser s (E.Mapping -> m Message)
tuplemessage = chainr1 message ((liftA2 $ liftM2 MTup) <$ kw COMMA)


------------------------------------------------------------------------------
-- Parsing Alice and Bob Protocol Specifications
------------------------------------------------------------------------------

{- EBNF for the Alice and Bob protocol language

TODO: Update to new syntax

Protocol := "protocol" Identifier "{" Transfer+ "}"
Transfer := Identifier "->" Identifier ":" Term 
          | Identifier "->" ":" Term  "<-" Identifier ":" Term
          | Identifier "<-" ":" Term  "->" Identifier ":" Term
Term := "{" Term "}" Key
      | Term "," Term
      | Identifier
Key := "sk(" Identifier ")"
     | "pk(" Identifier ")"
     | "k(" Identifier, Identifier ")"
     | Term
Identifier := [A..Za..z-_]

-}

-- | Parse a single transfer.
transfer :: Parser s [(Id, RoleStep)]
transfer = do
  lbl <- Label <$> identifier <* kw DOT
  (do right <- kw RIGHTARROW *> ident <* kw COLON
      pt <- tuplepattern
      return [(right, Recv lbl pt)]
   <|>
   do right <- kw LEFTARROW *> ident <* kw COLON
      ptr <- tuplepattern
      (do left <- try $ ident <* kw LEFTARROW <* kw COLON
          ptl <- tuplepattern
          return [(left, Recv lbl ptl),(right, Send lbl ptr)]
       <|>
       return [(right, Send lbl ptr)]
       )
   <|>
   do left <- ident
      (do kw RIGHTARROW
          (do right <- ident <* kw COLON
              pt <- tuplepattern
              return [(left,Send lbl pt), (right, Recv lbl pt)]
           <|>
           do ptl <- kw COLON *> tuplepattern
              (do right <- kw RIGHTARROW *> ident <* kw COLON
                  ptr <- tuplepattern
                  return [(left,Send lbl ptl), (right, Recv lbl ptr)]
               <|>
               do return [(left, Send lbl ptl)]
               )
           )
       <|>
       do kw LEFTARROW
          (do pt <- kw COLON *> tuplepattern
              return [(left, Recv lbl pt)]
           <|>
           do right <- ident <* kw COLON
              pt <- tuplepattern
              return [(left, Recv lbl pt), (right, Send lbl pt)]
           )
       )
   ) 

-- | Parse a protocol.
protocol :: Parser s Protocol
protocol = do
  name <- string "protocol" *> identifier 
  transfers <- concat <$> braced (many1 transfer)
  -- convert parsed transfers into role scripts
  let roleIds = S.fromList $ map fst transfers
      roles = do
        actor <- S.toList roleIds
        let steps = [ step | (i, step) <- transfers, i == actor ]
        return $ Role (getId actor) 
                      (ensureFreshSteps actor (S.map addSpacePrefix roleIds) steps)
  return $ Protocol name roles
  where
  addSpacePrefix = Id . (' ':) . getId
  dropSpacePrefixes = S.map dropSpacePrefix
  -- | Ensure message variables are received before they are sent.
  ensureFreshSteps actor possibleAvars = 
      go (S.singleton (addSpacePrefix actor)) S.empty S.empty
    where
      go _ _ _ [] = []
      go avars mvars fresh (Send l pt : rs) = 
        let avars' = avars `S.union` (((patFMV pt `S.intersection` possibleAvars) 
                                       `S.difference` mvars) `S.difference` fresh)
            fresh' = fresh `S.union` ((patFMV pt `S.difference` avars') `S.difference` mvars)
            pt' = resolveIds (dropSpacePrefixes avars') (dropSpacePrefixes mvars) pt
        in Send l pt' : go avars' mvars fresh' rs
      go avars mvars fresh (Recv l pt : rs) = 
        let mvars' = mvars `S.union` ((patFMV pt `S.difference` avars) `S.difference` fresh)
            pt' = resolveIds (dropSpacePrefixes avars) (dropSpacePrefixes mvars') pt
        in  Recv l pt' : go avars mvars' fresh rs

------------------------------------------------------------------------------
-- Parse Claims
------------------------------------------------------------------------------

-- | Parse a claim. 
claims :: (String -> Maybe Protocol) -> Parser s [ThyItem]
claims protoMap = do
  let mkAxiom (name, se) = ThyTheorem (name, Axiom se)
  (multiplicity, mkThyItem) <- 
    (string "property"   *> pure (id,                   ThySequent)) <|> 
    (string "properties" *> pure ((concat <$>) . many1, ThySequent)) <|>
    (string "axiom"      *> pure (id,                   mkAxiom   ))
  protoId <- kw LPAREN *> string "of" *> identifier
  proto <- liftMaybe' ("unknown protocol '"++protoId++"'") $ protoMap protoId 
  kw RPAREN
  multiplicity $ do
    claimId <- try $ identifier <* kw COLON
    when ('-' `elem` claimId) (fail $ "hyphen '-' not allowed in property name '"++claimId++"'")
    let mkThySequent (mkClaimId, se) = mkThyItem (mkClaimId claimId, se)
        singleSequents = map (liftM (return . (,) id) . ($ proto))
          [ niagreeSequent, secrecySequent, parseAtomicitySequent, implicationSequent ]
        multiSequents = map ($ proto)
          [ parseNonceSecrecy, parseFirstSends
          , parseTransferTyping, parseAutoProps ]
    sequents <- asum $ multiSequents ++ singleSequents
    return $ map mkThySequent sequents

-- | Auto-generated simple properties: first-sends, ltk-secrecy, nonce-secrecy,
-- weak-atomicity, msc-typing
parseAutoProps :: Protocol -> Parser s [(String -> String,Sequent)]
parseAutoProps proto =
  string "auto" *> kw MINUS *> string "properties" *> 
  pure (concat
    [ transferTyping proto, firstSendSequents proto, nonceSecrecySequents proto ])

-- | Create secrecy claims for nonces and variables.
parseNonceSecrecy :: Protocol -> Parser s [(String -> String,Sequent)]
parseNonceSecrecy proto = 
  string "nonce" *> kw MINUS *> string "secrecy" *> pure (nonceSecrecySequents proto)

-- | Create secrecy claims for nonces and variables.
nonceSecrecySequents :: Protocol -> [(String -> String,Sequent)]
nonceSecrecySequents proto = 
  concatMap mkSequent . toposort $ protoOrd proto
  where
  mkSequent (step, role) = case step of
    Send _ pt -> do
      n@(PFresh i) <- S.toList $ subpatterns pt
      guard (not (plainUse pt n) && firstUse n)
      return $ secrecySe (MFresh . Fresh) i
    Recv _ pt -> do
      v@(PMVar i) <- S.toList $ subpatterns pt
      guard (not (plainUse pt v) && firstUse v)
      return $ secrecySe (MMVar . MVar) i
    where
    (tid, prem0) = freshTID (empty proto)
    (prefix, _) = break (step ==) $ roleSteps role
    firstUse = (`S.notMember` (S.unions $ map (subpatterns . stepPat) prefix))
    plainUse pt = (`S.member` splitpatterns pt)
    avars = [ MAVar (AVar (LocalId (v,tid)))
            | (PAVar v) <- S.toList . S.unions . map (subpatterns.stepPat) $ roleSteps role ]
    secrecySe constr i =
      ( (++("_"++roleName role++"_sec_"++getId i))
      , Sequent prem (FAtom AFalse)
      )
      -- flip (Sequent proto) FFalse $ FFacts $
      -- insertEv (Learn (constr (LocalId (i,tid)))) $ 
      -- insertEv (Step tid step) $ 
      -- foldr uncompromise (insertRole tid role emptyFacts) avars
      where
      -- here we know that conjunction will work, as we build it by ourselves
      Just (Just prem) = conjoinAtoms atoms prem0
      atoms = [ AEq (E.TIDRoleEq (tid, role))
              , AEv (Step tid step)
              , AEv (Learn (constr (LocalId (i, tid))))
              ] ++ map AUncompr avars

parseFirstSends :: Protocol -> Parser s [(String -> String,Sequent)]
parseFirstSends proto =
  string "first" *> kw MINUS *> string "sends" *> pure (firstSendSequents proto)

firstSendSequents :: Protocol -> [(String -> String,Sequent)]
firstSendSequents proto = 
  concatMap mkRoleSequents $ protoRoles proto
  where
  mkRoleSequents role = 
    concatMap mkStepSequents $ zip (inits steps) steps
    where
    steps = roleSteps role
    (tid, prem0) = freshTID (empty proto)
    mkStepSequents (_,            Recv _ _  ) = []
    mkStepSequents (prefix, step@(Send _ pt)) = do
      n@(PFresh i) <- S.toList $ splitpatterns pt
      guard (n `S.notMember` S.unions (map (subpatterns.stepPat) prefix))
      let learn = (Learn (MFresh (Fresh (LocalId (i, tid)))))
          atoms = [ AEq (E.TIDRoleEq (tid, role)), AEv learn ]
          Just (Just prem) = conjoinAtoms atoms prem0
          concl = FAtom (AEvOrd (Step tid step, learn))
      return ( (++("_" ++ getId i)), Sequent prem concl)

parseTransferTyping :: Protocol -> Parser s [(String -> String, Sequent)]
parseTransferTyping proto =
  string "msc" *> kw MINUS *> string "typing" *> pure (transferTyping proto)

transferTyping :: Protocol -> [(String -> String, Sequent)]
transferTyping proto = case mscTyping proto of
  Just typing -> pure
    ((++"_msc_typing"), Sequent (empty proto) (FAtom (ATyping typing)))
  Nothing     -> fail "transferTyping: failed to construct typing"

-- | Parse secrecy formula.
secrecySequent :: Protocol -> Parser s Sequent
secrecySequent proto = do
  let (tid, prem0) = freshTID (empty proto)
  roleId <- funOpen "secret" *> identifier
  role <- liftMaybe' ("could not find role '"++roleId++"'") $ lookupRole roleId proto
  lbl <- kw COMMA *> (identifier <|> kw MINUS *> pure "-")
  stepAtoms <- 
    (do step <- liftMaybe $ lookupRoleStep lbl role
        return $ [AEv (Step tid step)]
     `mplus` return [])
  kw COMMA
  (msgMod, pt) <- asum
    [ ((,) MInvKey) <$> funApp "inv" tuplepattern
    , ((,) id) <$> pattern ]
  let m = msgMod . inst tid . resolveIdsLocalToRole role $ pt
  kw COMMA
  uncompromised <- map (inst tid . resolveIdsLocalToRole role) <$> msgSet
  kw RPAREN
  -- construct secrecy claim 
  let atoms = [ AEq (E.TIDRoleEq (tid, role)), AEv (Learn m) ] ++ stepAtoms ++ 
              map AUncompr uncompromised
      prem  = case conjoinAtoms atoms prem0 of
        Just (Just prem1) -> prem1
        Just Nothing      -> error "secrecySequent: secrecy claim is trivially true"
        Nothing           -> error "secrecySequent: failed to construct secrecy claim"
   
  return $ Sequent prem (FAtom AFalse)
  where
  msgSet = braced $ sepBy pattern (kw COMMA)

-- | Parse non-injective agreement claim.
niagreeSequent :: Protocol -> Parser s Sequent
niagreeSequent proto = do
    funOpen "niagree"
    (roleCom, stepCom, patCom) <- roleStepPattern
    kw RIGHTARROW
    (roleRun, stepRun, patRun) <- roleStepPattern
    kw COMMA
    uncompromised <- map (AUncompr . instPat tidCom roleCom) <$> patSet
    kw RPAREN
    let premAtoms  = [ AEq (E.TIDRoleEq (tidCom, roleCom))
                     , AEv (Step tidCom stepCom) 
                     ] ++ 
                     uncompromised

        conclAtoms = [ AEq (E.TIDRoleEq (tidRun, roleRun))
                     , AEv (Step tidRun stepRun) 
                     , AEq (E.MsgEq ( instPat tidRun roleRun patRun
                                    , instPat tidCom roleCom patCom ))
                     ]
        concl = FExists (Left tidRun) (foldr1 FConj $ map FAtom conclAtoms)
        prem  = case conjoinAtoms premAtoms prem0 of
            Just (Just prem1) -> prem1
            Just Nothing      -> error "niagreeSequent: claim is trivially true"
            Nothing           -> error "niagreeSequent: failed to construct claim"

    return (Sequent prem concl)
  where
    (tidCom, prem0) = freshTID (empty proto)
    tidRun          = succ tidCom
    
    patSet = braced $ sepBy pattern (kw COMMA)
    instPat tid role = inst tid . resolveIdsLocalToRole role

    -- parse a step and a local pattern; e.g., 'B_1[A,B,TNA,Text1]'
    roleStepPattern = do
        stepId <- identifier
        let (lbl, roleId) = (reverse *** (init . reverse)) (break ('_' ==) $ reverse stepId)
        role <- liftMaybe' ("could not find role '" ++ roleId ++ 
                            "' in protocol '" ++ protoName proto ++ "'")
                           (lookupRole roleId proto)

        step <- liftMaybe' ("unknown label '" ++ lbl ++ "' in role '" ++ roleId ++ "'") 
                           (lookupRoleStep lbl role)
        pat  <- kw LBRACKET *> tuplepattern <* kw RBRACKET
        return (role, step, pat)


-- | Parse a weak atomicity formula
parseAtomicitySequent :: Protocol -> Parser s Sequent
parseAtomicitySequent proto = 
  string "weakly" *> kw MINUS *> string "atomic" *> pure (atomicitySequent proto)

atomicitySequent :: Protocol -> Sequent
atomicitySequent proto = Sequent (empty proto) (FAtom (ATyping WeaklyAtomic))

-- General premises parsing
---------------------------

-- | A raw fact: Either a premise modifier parametrized over a set of role
-- equalities or a single role equality. We'll use these facts to allow for
-- late binding of thread ids to roles.
data RawFact m =
    RawAtom (E.Mapping -> m Atom)
  | RawTIDRoleEq TID String

-- | Extract the role equalities from a list of raw facts.
extractRoleEqs :: MonadPlus m => Protocol -> [RawFact m] -> m [(TID, Role)]
extractRoleEqs proto facts =
  mapM mkEq [(tid, roleId) | RawTIDRoleEq tid roleId <- facts]
  where
  mkEq (tid, roleId) = case lookupRole roleId proto of
    Just role -> return (tid, role)
    Nothing   -> fail $ "mkRoleEqs: role '"++roleId++"' does not occur in protocol '"
                        ++protoName proto++"'"

-- | Parse a role equality.
roleEqFact :: MonadPlus m => Parser s (RawFact m)
roleEqFact = RawTIDRoleEq <$> (TID <$> (string "role" *> parens integer))
                          <*> (kw EQUAL *> identifier)

-- | Parse a knowledge fact.
knowsFact :: MonadPlus m => Parser s (RawFact m)
knowsFact = do
    m <- funApp "knows" message
    return $ RawAtom (liftM (AEv . Learn) <$> m)

-- | Parsing an executed role step.
rawStep :: MonadPlus m => Parser s (E.Mapping -> m Event)
rawStep = parens $ do
  tid <- TID <$> integer
  stepId <- kw COMMA *> identifier
  let step = resolveStep <*> pure tid <*> pure stepId
  return $ (liftM (Step tid) <$> step)

-- | Parse a step fact.
stepFact :: MonadPlus m => Parser s (RawFact m)
stepFact = do
    step <- string "step" *> rawStep
    return $ RawAtom (liftM AEv <$> step)

-- | Parse an honesty assumption.
honestFact :: MonadPlus m => Parser s [RawFact m]
honestFact = do
    string "uncompromised"
    msgs <- parens (sepBy1 message (kw COMMA))
    -- let mod prems = foldr uncompromise prems lids
    return $ [RawAtom (liftM AUncompr <$> m) | m <- msgs]

-- | Parses a learn or a step event.
event :: MonadPlus m => Parser s (E.Mapping -> m Event)
event = asum [ string "St" *> rawStep
             , (liftM Learn <$>) <$> (string "Ln" *> message)
             , (liftM Learn <$>) <$> instantiation ]

-- | Parse a series of ordering facts.
orderFacts :: MonadPlus m => Parser s [RawFact m]
orderFacts = do
  ev  <- event <* kw LESS
  evs <- sepBy1 event (kw LESS)
  let mkAtom e1 e2 = RawAtom $ \mapping -> do
        e1' <- e1 mapping
        e2' <- e2 mapping
        return $ AEvOrd (e1', e2')
  return $ zipWith mkAtom (ev:evs) evs

-- | Parse an equality fact.
eqFact :: MonadPlus m => Parser s (RawFact m)
eqFact = do
  m1 <- message <* kw EQUAL
  m2 <- message
  return $ RawAtom (liftM2 (\x y -> AEq (E.MsgEq (x , y))) <$> m1 <*> m2)

-- | Parse a raw fact.
rawFacts :: MonadPlus m => Parser s [RawFact m]
rawFacts = foldl1 (<|>) 
  ( [try orderFacts, honestFact] ++ 
    map (liftM return) [roleEqFact, knowsFact, stepFact, eqFact] )

-- | Parse the conclusion "False".
falseConcl :: Parser s Formula
falseConcl = doubleQuoted (string "False" *> pure (FAtom AFalse))

-- | Parse a conclusion stating existence of some threads of a specific
-- structure.
existenceConcl :: Protocol -> E.Mapping -> Parser s Formula
existenceConcl proto mapping = do
  tids <- map (Left . TID) <$> (threads <|> pure [])
  facts <- concat <$> doubleQuoted (sepBy1 rawFacts (kw AND))
  roleeqs <- extractRoleEqs proto facts
  let mapping' = foldr (uncurry E.addTIDRoleMapping) mapping roleeqs
  atoms <- (map (AEq . E.TIDRoleEq) roleeqs ++) `liftM`
           sequence [ mkAtom mapping' | RawAtom mkAtom <- facts ]
  return $ foldr FExists (foldr1 FConj . map FAtom $ atoms) tids
  where
  singleThread = pure <$> (strings ["a", "thread"] *> integer)
  multiThreads = strings ["threads"] *> sepBy1 integer (kw COMMA) 
  threads = (singleThread <|> multiThreads) <* strings ["such","that"] 
 
-- | Parse a conclusion.
-- currently only contradiction supported
conclusion :: Protocol -> E.Mapping -> Parser s Formula
conclusion proto mapping = asum
  [try falseConcl, existenceConcl proto mapping]

-- | Parse a general implication claim.
implicationSequent :: Protocol -> Parser s Sequent
implicationSequent proto = do 
  facts <- concat <$> (string "premises" *> many (doubleQuoted rawFacts))
  roleeqs <- extractRoleEqs proto facts
  let mapping = foldr (uncurry E.addTIDRoleMapping) (E.Mapping E.empty) roleeqs
      quantifiers = map fst roleeqs
  atoms <- (map (AEq . E.TIDRoleEq) roleeqs ++) `liftM`
           sequence [ mkAtom mapping | RawAtom mkAtom <- facts ]
  prems0 <- foldM (flip quantifyTID) (F.empty proto) quantifiers
  optPrems <- conjoinAtoms atoms prems0
  prems <- maybe (fail "contradictory premises") return optPrems
  string "imply"
  concl <- conclusion proto mapping
  return $ Sequent prems concl

{-
-- | Construct the premise modifier. The given set of role equalities is used
-- for thread identfier lookup.
mkPremiseMod :: MonadPlus m => E.Mapping -> [RawFact m] -> Facts -> m Facts
mkPremiseMod mapping rawfacts facts = do
  atoms <- sequence [ mkAtom mapping | RawAtom mkAtom <- rawfacts ]
  optFacts <- conjoinAtoms atoms facts 
  maybe (error "mkPremiseMod: contradictory facts") return $ optFacts
-}

-- | A formal comment.
formalComment :: Parser s ThyItem
formalComment =
    ThyText <$> text begin 
            <*> (concat <$> many (text content) <* text end)
  where
    text f = token (\t -> case t of TEXT ty -> f ty; _ -> mzero)
    begin (TextBegin str)     = return str
    begin _                   = mzero
    content (TextContent str) = return str
    content _                 = mzero
    end (TextEnd)             = return ()
    end _                     = mzero


 ------------------------------------------------------------------------------ 
 -- Parse a theory
 ------------------------------------------------------------------------------ 

    
-- | Parse a theory.
theory :: Parser s Theory
theory = do
    string "theory"
    thyId <- identifier
    string "begin" *> addItems (Theory thyId []) <* string "end"
  where
    addItems :: Theory -> Parser s (Theory)
    addItems thy = 
      do p <- protocol
         case lookupProtocol (protoName p) thy of
           Just _  -> fail $ "duplicate protocol '" ++ protoName p ++ "'"
           Nothing -> addItems (insertItem (ThyProtocol p) thy)
      <|>
      do item <- formalComment
         addItems (insertItem item thy)
      <|>
      do cs <- claims (flip lookupProtocol thy)
         addItems (foldl' (flip insertItem) thy cs)
      <|>
      do return thy

