-----------------------------------------------------------------------------
-- |
-- Module      :  BuechiStreamAutomaton
-- Maintainer  :  Philippe Heim
--
-- Implementation of the BSA data structure used by the algorithm
--
-----------------------------------------------------------------------------
{-# LANGUAGE LambdaCase, RecordWildCards #-}

-----------------------------------------------------------------------------
module BuechiStreamAutomaton
  ( BSA(..)
  , State
  , updateExplicit
  , postTrans
  , transitionLabels
  , states
  , lazyConstrainted
  , defaultFlags
  , ExplTrans
  , effect
  , transToString
  , bsaToString
  , Literal(..)
  , Conj
  , DNF
  , dnfElems
  , Label
  , SymTrans
  ) where

-----------------------------------------------------------------------------
import Data.Map as Map (Map, empty, insert, lookup, toList)
import Data.Set as Set
  ( Set
  , empty
  , fromList
  , insert
  , map
  , toList
  , union
  , unions
  )
import Terms

-----------------------------------------------------------------------------
--
-- DNFs
--
-----------------------------------------------------------------------------
-- | 'Literal' it the literal datatype of a 'DNF'
--
data Literal a
  = Pos a
  -- ^ 'Pos' indicates a positive literal
  | Neg a
  -- ^ 'Neg' indicates a negative literal
  deriving (Eq, Ord, Show)

-----------------------------------------------------------------------------
-- | 'Conj' represents conjunction of literals (as a list)
--
type Conj a = [Literal a]

-----------------------------------------------------------------------------
-- | 'DNF' represents a logical formula in DNF form as  a disjunction 
-- (as a list) of conjuctions ('Conj')
--
type DNF a = [Conj a]

-----------------------------------------------------------------------------
-- 'dnfElems' returns all variables of a 'DNF' 
--
dnfElems :: Ord a => DNF a -> Set a
dnfElems dnf =
  Set.fromList $
  concatMap
    (concatMap
       (\case
          Pos a -> [a]
          Neg a -> [a]))
    dnf

-----------------------------------------------------------------------------
-- | 'complete' add to an 'DNF' variables, such that each of these variable 
-- occurs in each conjunction of the 'DNF' and the new 'DNF' is logically 
-- equivalent to the old one
--
complete :: Eq a => Set a -> DNF a -> DNF a
complete var = concatMap (compl (Set.toList var))
  where
    compl [] cnf = [cnf]
    compl (v:vr) cnf =
      if any (\l -> (l == Pos v) || (l == Neg v)) cnf
        then compl vr cnf
        else compl vr (Pos v : cnf) ++ compl vr (Neg v : cnf)

-----------------------------------------------------------------------------
--
-- Data Structure Definition
--
-----------------------------------------------------------------------------
-- | 'State' is a state of a 'BSA'
--
type State = Int

-----------------------------------------------------------------------------
-- | 'Label' appearing inside of the 'DNF' of a symbolic transition as a
-- variable, i.e. either an 'PredicateTerm' or an update
-- 
type Label c f p = Either (PredicateTerm c f p) (c, FunctionTerm c f)

-----------------------------------------------------------------------------
-- | 'SymTrans' represents a symbolic transition label of a 'BSA'
--
type SymTrans c f p = DNF (Label c f p)

-----------------------------------------------------------------------------
-- | 'ExplTransLabel' represents an explicit transition label i.e. direct mapping
-- form predicates to truth values and cells to respective update terms
--
type ExplTransLabel c f p
   = (Map (PredicateTerm c f p) Bool, Map c (FunctionTerm c f))

-----------------------------------------------------------------------------
-- | 'ExplTrans' is an identifier for an 'ExplTransLabel'
--
type ExplTrans = Int

-----------------------------------------------------------------------------
-- | 'Guards' describes a set of transition guards
--
type Guards c f p = Set (PredicateTerm c f p)

-----------------------------------------------------------------------------
-- | 'Updates' describes a set of updates
--
type Updates c f = Set (c, FunctionTerm c f)

-----------------------------------------------------------------------------
-- | 'BSA' is the data structure of a Büchi Stream Automaton
--
data BSA c f p =
  BSA
    { stateNum :: Int
      -- ^ 'stateNum' is the number of states. The states range from
      -- 0 to 'stateNum' - 1
    , initial :: Set State
      -- ^ 'initial' is the set of initial states
    , accepting :: Set State
      -- ^ 'accepting' is the set of accepting states
    , cells :: Set c
      -- ^ 'cells' is the set of all cells appearing in the 'BSA'
    , guards :: Guards c f p
      -- ^ 'guards' is the set of all guards appearing in the 'BSA'
    , updates :: Updates c f
      -- ^ 'updates' is the set of all updates appearing in the 'BSA'
    , trans :: State -> Set (SymTrans c f p, State)
      -- ^ 'trans' describes the transition relation, by mapping each
      -- state to it successors with the respective symbolic transition
    , relation :: Map State (Map ExplTrans (Set State))
      -- ^ 'relation' is the explicit transition relation. I can be
      -- computed from the flags and the symbolic transition relation
    , label :: ExplTrans -> ExplTransLabel c f p
      -- ^ 'label' maps 'ExplTrans' identifiers to their respective label
      -- It is computed together with 'relation'
    , flags :: Flags
      -- ^ 'flags' describes the set of optimization flags.
      -- Warning: These flags should be set before generating transitions
      -- and working with the 'BSA' as they might prune away transition
      -- parts and whole transitions
    }

-----------------------------------------------------------------------------
-- | 'Flags' contains optimization flags
-- 
data Flags =
  Flags
    { fullyConstrained :: Bool
      -- ^ 'fullyConstrained' means that if a symbolic transitions is
      -- converted to its explicit ones, all predicate constraints are
      -- added (resulting in more explicit transitions) even if they
      -- did not occur on the original transition
    , removeRedudant :: Bool
      -- ^ 'removeRedundant' indicates to remove 'redundant' transitions
      -- (for satisfiability meaningless self loops)
    }

-----------------------------------------------------------------------------
-- | 'defaultFlags' are the default flags that work well with the full
-- satisfiability search
--
defaultFlags :: Flags
defaultFlags = Flags {fullyConstrained = True, removeRedudant = True}

-----------------------------------------------------------------------------
-- | 'lazyConstrainted' removes the 'fullyContrained' flag, yielding
-- to less explicit transitions for a symbolic one, with less 
-- "information". This can be used for simple SAT search, but not for 
-- UNSAT search
--
lazyConstrainted :: (Ord c, Ord f, Ord p) => BSA c f p -> BSA c f p
lazyConstrainted bsa =
  updateExplicit $ bsa {flags = (flags bsa) {fullyConstrained = False}}

-----------------------------------------------------------------------------
-- | 'states' returns the set of all states of a 'BSA'
--
states :: BSA c f p -> Set State
states bsa = fromList [0 .. stateNum bsa - 1]

-----------------------------------------------------------------------------
--
-- Explicit transitions
--
-----------------------------------------------------------------------------
-- | 'postTrans' returns the successors 'State's and respective 
-- explicit transition labels of some 'State'
--
postTrans :: BSA c f p -> State -> [(ExplTrans, State)]
postTrans bsa q =
  case Map.lookup q (relation bsa) of
    Nothing -> []
    Just edgeMapping ->
      concatMap
        (\(t, qs') -> (\q' -> (t, q')) <$> Set.toList qs')
        (Map.toList edgeMapping)

-----------------------------------------------------------------------------
-- | 'transitionLabels' returns all explicit transition label identifiers
-- of a 'BSA'
--
transitionLabels :: BSA c f p -> Set ExplTrans
transitionLabels bsa =
  unions $
  (\case
     Nothing -> Set.empty
     Just edges -> fromList $ fst <$> Map.toList edges) <$>
  ((`Map.lookup` relation bsa) <$> Set.toList (states bsa))

-----------------------------------------------------------------------------
-- | 'transitionRelation' computes the explicit transition relation and the 
-- label mapping as 'Map's
--
transitionRelation ::
     (Ord c, Ord f, Ord p)
  => BSA c f p
  -> ( Map State (Map ExplTrans (Set State))
     , Map ExplTrans (ExplTransLabel c f p))
transitionRelation bsa =
  let labels =
        Set.toList
          (Set.fromList (concatMap (fmap fst . transitions bsa) (states bsa)))
      labelMap =
        fst $
        foldl (\(m, i) t -> (Map.insert i t m, i + 1)) (Map.empty, 0) labels
      labelInvMap =
        fst $
        foldl (\(m, i) t -> (Map.insert t i m, i + 1)) (Map.empty, 0) labels
      labelInvFunc l =
        case Map.lookup l labelInvMap of
          Nothing -> error "Assertion: Inverse label map should be complete"
          Just t -> t
      transitionMap =
        foldl
          (\m q ->
             Map.insert
               q
               (edgeMapping
                  Map.empty
                  ((\(t, q) -> (labelInvFunc t, q)) <$> transitions bsa q))
               m)
          Map.empty
          (states bsa)
   in (transitionMap, labelMap)
  where
    edgeMapping ::
         Map ExplTrans (Set State)
      -> [(ExplTrans, State)]
      -> Map ExplTrans (Set State)
    edgeMapping edgeMap =
      \case
        [] -> edgeMap
        (t, q'):tr ->
          case Map.lookup t edgeMap of
            Nothing -> edgeMapping (Map.insert t (fromList [q']) edgeMap) tr
            Just sts ->
              edgeMapping (Map.insert t (Set.insert q' sts) edgeMap) tr

-----------------------------------------------------------------------------
-- | 'transitions' computes the explicit transition labels of 
-- some 'BSA' 'State'
--
transitions ::
     (Ord c, Ord f, Ord p)
  => BSA c f p
  -> State
  -> [(ExplTransLabel c f p, State)]
transitions bsa q =
  let post = Set.toList (trans bsa q)
      explicits =
        (\(sym, q') ->
           Set.map (\exp -> (exp, q')) $
           dnfMakeExplicit
             (fullyConstrained (flags bsa))
             (guards bsa)
             (updates bsa)
             sym) <$>
        post
      transformed = Set.toList (unions explicits)
   in if removeRedudant (flags bsa)
        then filter (not . reduantant bsa q) transformed
        else transformed

-----------------------------------------------------------------------------
-- | 'updateExplicit' updates the explicit transition relation in a BSA
-- (e.g after creation of the symbolic one, or after a change of flags)
--
updateExplicit :: (Ord c, Ord f, Ord p) => BSA c f p -> BSA c f p
updateExplicit bsa =
  let (relationMap, labelMap) = transitionRelation bsa
      labelFunc tid =
        case Map.lookup tid labelMap of
          Nothing ->
            error "Assertion: Label map should map every explicit transition"
          Just l -> l
   in bsa {relation = relationMap, label = labelFunc}

-----------------------------------------------------------------------------
-- | 'redundant' checks if a transition is a redundant self-loop, i.e.
-- a self-loop that does no change anything if removed (for satisfiability)
-- given the starting and end state of the transition
--
reduantant ::
     (Ord c, Ord f)
  => BSA c f p
  -> State
  -> (ExplTransLabel c f p, State)
  -> Bool
reduantant bsa q0 ((_, assigns), q1) =
  q0 == q1 &&
  q0 `notElem` accepting bsa &&
  all (\(c, ft) -> ft == Cell c) (Map.toList assigns)

-----------------------------------------------------------------------------
--
-- Symbolic to explicit transitions
--
-----------------------------------------------------------------------------
-- | 'consistent' checks if a conjunction over predicates and update
-- literals is not contradictory, i.e. no predicates occur twice with 
-- different signs and for each cell there is at most one updates
--
consistent :: (Eq c, Eq f, Eq p) => Conj (Label c f p) -> Bool
consistent =
  \case
    [] -> True
    Neg (Left pt):xr -> (Pos (Left pt) `notElem` xr) && consistent xr
    Pos (Left pt):xr -> (Neg (Left pt) `notElem` xr) && consistent xr
    Neg (Right _):xr -> consistent xr
    Pos (Right (c, ft)):xr ->
      all
        (\case
           Pos (Right (c', ft')) -> c /= c' || ft == ft'
           _ -> True)
        xr &&
      consistent xr

-----------------------------------------------------------------------------
-- | 'updateComplete' checks if a conjunction over predicates and update
-- literals contains at least one update per cell
--
updateComplete ::
     (Ord c, Ord f, Ord p) => Updates c f -> Conj (Label c f p) -> Bool
updateComplete updates conj =
  let cells = Set.map fst updates
   in all
        (\c ->
           any
             (\case
                Pos (Right (c', _)) -> c == c'
                _ -> False)
             conj)
        cells

-----------------------------------------------------------------------------
-- | 'conjMakeExplicit' a conjunction over predicates and update
-- literals into an explicit transition label
--
conjMakeExplicit ::
     (Ord c, Ord p, Ord f) => Conj (Label c f p) -> ExplTransLabel c f p
conjMakeExplicit conj =
  let guard = predicateMap Map.empty conj
      assign = updateMap Map.empty conj
   in (guard, assign)
  where
    predicateMap m =
      \case
        [] -> m
        Pos (Left pt):xr -> predicateMap (Map.insert pt True m) xr
        Neg (Left pt):xr -> predicateMap (Map.insert pt False m) xr
        _:xr -> predicateMap m xr
    updateMap m =
      \case
        [] -> m
        Pos (Right (c, ct)):xr -> updateMap (Map.insert c ct m) xr
        _:xr -> updateMap m xr

-----------------------------------------------------------------------------
-- | 'dnfMakeExplicit' transforms a symbolic transition label into 
-- a set of explicit ones
--
dnfMakeExplicit ::
     (Ord c, Ord p, Ord f)
  => Bool
  -> Guards c f p
  -> Updates c f
  -> SymTrans c f p
  -> Set (ExplTransLabel c f p)
dnfMakeExplicit full guards updt symTrans =
  let completedUpdates = complete (Set.map Right updt) symTrans
      completed =
        if full
          then complete (Set.map Left guards) completedUpdates
          else completedUpdates
   in fromList
        [ conjMakeExplicit c
        | c <- completed
        , consistent c
        , updateComplete updt c
        ]

-----------------------------------------------------------------------------
--
-- Symbolic evaluation of explicit transitions
--
-----------------------------------------------------------------------------
-- | 'effect' computes the symbolic effect of some transition sequence in
-- a BSA, starting with no constraint and the identity mapping
--
effect ::
     (Ord c, Ord f, Ord p)
  => BSA c f p
  -> [ExplTrans]
  -> (c -> FunctionTerm c f, Set (PredicateTerm c f p, Bool))
effect bsa = effect' (Cell, Set.empty)
  where
    effect' (cellValues, constraints) =
      \case
        [] -> (cellValues, constraints)
        tid:tr ->
          let (p, u) = label bsa tid
              cellValues' =
                substF cellValues .
                (\cell ->
                   case Map.lookup cell u of
                     Just ft -> ft
                     Nothing ->
                       error "Assertion: Incomplete explicit updated map found")
              constraints' =
                foldl
                  (\s (p, mb) ->
                     case mb of
                       Nothing -> s
                       Just b -> Set.insert (p, b) s)
                  Set.empty
                  (Set.map
                     (\t -> (substP cellValues t, Map.lookup t p))
                     (guards bsa))
           in effect' (cellValues', constraints `union` constraints') tr

-----------------------------------------------------------------------------
--
-- Pretty printing
--
-----------------------------------------------------------------------------
-- | 'transToString' prints a transition as a 'String' in a pretty manner
--
transToString ::
     (Show c, Show f, Show p)
  => BSA c f p
  -> State
  -> (ExplTrans, State)
  -> String
transToString bsa q (tid, q') =
  let (gr, act) = label bsa tid
   in Prelude.filter (\c -> c /= '\"' && c /= '\\') $
      show q ++
      "-{" ++
      show (fmap (\(a, b) -> (predTermToString a, b)) (Map.toList gr)) ++
      " | " ++
      show (fmap (\(a, b) -> (a, funcTermToString b)) (Map.toList act)) ++
      "}->" ++ show q'

-----------------------------------------------------------------------------
-- | 'bsaToString' prints a 'BSA' in a pretty manner as a 'String' 
--
bsaToString ::
     (Ord c, Ord f, Ord p, Show c, Show f, Show p) => BSA c f p -> String
bsaToString bsa@BSA {..} =
  Prelude.filter (\c -> c /= '\"' && c /= '\\') $
  "States    " ++
  show stateNum ++
  "\n" ++
  "Initial   " ++
  show (Set.toList initial) ++
  "\n" ++
  "Accepting " ++
  show (Set.toList accepting) ++
  "\n" ++
  "Cells     " ++
  show (Set.toList cells) ++
  "\n" ++
  "Updates  " ++
  concatMap
    (\(c, ft) -> " [" ++ show c ++ " <- " ++ funcTermToString ft ++ "]")
    updates ++
  "\n" ++
  "Guards    " ++
  concatMap ((++ "; ") . predTermToString) guards ++
  "\n" ++
  unlines
    (concatMap (\q -> transToString bsa q <$> postTrans bsa q) (states bsa))
-----------------------------------------------------------------------------
