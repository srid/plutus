{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module Spec.Eval (tests) where

import Codec.Serialise qualified as CBOR
import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL
import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.Maybe
import Data.Text as Text (pack)
import Data.Text.Encoding as Text (encodeUtf8)
import Plutus.V1.Ledger.Api as Api
import Plutus.V1.Ledger.Scripts as Scripts
import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.MkPlc
import Test.Tasty
import Test.Tasty.Golden
import UntypedPlutusCore as UPLC

{- NOTE: Direct UPLC code
For this test-suite we write the programs directly in UPLC AST,
bypassing the GHC typechecker & compiler, the PIR typechecker & compiler and the PLC typechecker.

The reason is that we want to test the execution of erroneous, "hand-crafted" code (produced w.o. the plutus toolchain).
We want to see if there are any mechanisms *before or during online/offline execution* (e.g. deserialization, validation, undebruijnification) that will
catch any errors coming from such erroneous, hand-crafted code.
-}

one :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
one = mkConstant @Integer () 1

-- a helper to intro a lam, debruijn are always 0-indexed
mkLam :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
mkLam = LamAbs () (DeBruijn 0)

-- a sufficient large debruijn index for testing
outOfScope :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outOfScope = Var () (DeBruijn 9999999)

-- (lam x outOfScope)
outLam :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outLam = mkLam outOfScope

-- [(lam x (lam y x)) (con integer 1) (lam x outOfScope)]
outConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outConst = mkIterApp () (mkLam $ mkLam $ Var () $ DeBruijn 2) [one, outLam]

-- (delay outOfScope)
outDelay :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outDelay = Delay () outOfScope

-- [(force (builtin ifThenElse)) (con bool True) (lam x x) (lam x outOfScope)]
outITE :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outITE = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ mkConstant @Bool () True -- pred
         , mkLam $ Var () $ DeBruijn 1 -- then
         , outLam -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (lam x (con integer 1)) (lam x (con unit ()))]
-- note that Branches have **different** types.
illITE :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITE = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ mkConstant @Bool () True -- pred
         , mkLam one -- then
         , mkLam $ mkConstant @() () () -- else
         ]

tests :: TestTree
tests = testGroup "eval"
    [ testEval "test/offline/" offline
    , testEval "test/online/" online
    ]

testEval :: Show a => TestName -> (UPLC.Program DeBruijn DefaultUni DefaultFun () -> a) -> TestTree
testEval prefix act = testGroup prefix $ fmap (\ (n,t) -> goldenVsResult n (prefix ++ n ++ ".golden") act t) ns
    where
      ns = [("outLam", outLam)
           ,("outConst", outConst)
           ,("outDelay", outDelay)
           ,("outITE", outITE)
           ,("illITE", illITE)
           ]

-- TODO: implement offlineEvalInternal for cek-debruijn branch using Cek.Internal, to show that also no out-of-scope will be caught

-- simulates online code evaluation by going all the way through serialize/deserialize/mkTermToEvaluate
-- currently behaves similar to offlineEvalExternal, because any out-of-scope errors will be caught by
-- the undebruinification step of mkTermToEvaluate. Subject to change by direct debruijn branch.
-- no ill-typed errors will be caught, e.g. `illITE`.
--online :: UPLC.Program DeBruijn DefaultUni DefaultFun () -> Bool
online :: Program DeBruijn DefaultUni DefaultFun () -> Bool
online p =
    -- handcraft a serializedscript
    let ss :: SerializedScript = BSS.toShort . BSL.toStrict . CBOR.serialise $ Script p
    in isRight $ snd $ Api.evaluateScriptRestricting Quiet (fromJust defaultCostModelParams) (unExRestrictingBudget enormousBudget) ss []

goldenVsResult :: Show a
               => TestName
               -> FilePath
               -> (UPLC.Program DeBruijn DefaultUni DefaultFun () -> a)
               -> Term DeBruijn DefaultUni DefaultFun ()
               -> TestTree
goldenVsResult n goldenpath act = goldenVsString n goldenpath . pure . prettyBs . act . mkProg
    where
      mkProg = Program () $ PLC.defaultVersion ()

      prettyBs =  BSL.fromStrict . Text.encodeUtf8 . Text.pack . show -- render . prettyPlcClassicDebug


offline :: UPLC.Program DeBruijn DefaultUni DefaultFun () -> Bool
offline = isRight . runExcept . evaluateScript . Script

-- offlineWithoutAPI :: UPLC.Program DeBruijn DefaultUni DefaultFun () -> Bool
-- offlineWithoutAPI = isRight . runExcept . evaluateScript

-- offlineWithoutAPIInternal :: UPLC.Program DeBruijn DefaultUni DefaultFun () -> Bool
-- offlineWithoutAPIInternal = isRight . runExcept . evaluateScript


