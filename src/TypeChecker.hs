-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for the static type checking.
module TypeChecker where

import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import qualified Data.Map as Map

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

type Env = Map.Map Ident Type
type Eval a = ExceptT String (State Env) a

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) Map.empty) of
    (Right _) -> Nothing
    (Left msg) -> Just msg

checkProgram :: Program -> Eval ()
checkProgram prog = return ()