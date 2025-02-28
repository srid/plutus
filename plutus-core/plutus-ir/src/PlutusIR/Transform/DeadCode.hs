{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module PlutusIR.Transform.DeadCode (removeDeadBindings) where

import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.MkPir
import PlutusIR.Transform.Rename ()

import PlutusCore qualified as PLC
import PlutusCore.Constant qualified as PLC
import PlutusCore.Name qualified as PLC

import Control.Lens
import Control.Monad
import Control.Monad.Reader

import Data.Coerce
import Data.Set qualified as Set

import Algebra.Graph qualified as G
import Algebra.Graph.ToGraph qualified as T
import Data.List.NonEmpty qualified as NE

-- | Remove all the dead let bindings in a term.
removeDeadBindings
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique,
       PLC.ToBuiltinMeaning uni fun, PLC.MonadQuote m)
    => Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
removeDeadBindings t = do
    tRen <- PLC.rename t
    runReaderT (transformMOf termSubterms processTerm tRen) (calculateLiveness tRen)

type Liveness = Set.Set Deps.Node

calculateLiveness
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique,
       PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> Liveness
calculateLiveness t =
    let
        depGraph :: G.Graph Deps.Node
        depGraph = fst $ Deps.runTermDeps t
    in Set.fromList $ T.reachable Deps.Root depGraph

live :: (MonadReader Liveness m, PLC.HasUnique n unique) => n -> m Bool
live n =
    let
        u = coerce $ n ^. PLC.unique
    in asks $ Set.member (Deps.Variable u)

liveBinding
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => Binding tyname name uni fun a
    -> m Bool
liveBinding =
    let
        -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        liveVarDecl (VarDecl _ n _) = live n
        liveTyVarDecl (TyVarDecl _ n _) = live n
    in \case
        TermBind _ _ d _ -> liveVarDecl d
        TypeBind _ d _ -> liveTyVarDecl d
        DatatypeBind _ (Datatype _ d _ destr constrs) -> or <$> (sequence $ [liveTyVarDecl d,  live destr] ++ fmap liveVarDecl constrs)

processTerm
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
processTerm = \case
    -- throw away dead bindings
    Let x r bs t -> mkLet x r <$> filterM liveBinding (NE.toList bs) <*> pure t
    x            -> pure x
