-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for the static type checking.
module TypeChecker where

import Control.Monad.Trans.Except
import Control.Monad.State
import qualified Data.Map as Map

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data ExtType = NormalType Type | FunType Env Type [Arg] Block
type Env = Map.Map Ident ExtType
type Eval a = ExceptT String (State Env) a

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) Map.empty) of
    (Right _) -> Nothing
    (Left msg) -> Just msg

checkProgram :: Program -> Eval ()
checkProgram (Program topDefs) = do
    mapM_ (checkTopDef) topDefs
    -- TODO find main and typecheck run

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef retType ident args block) = checkFnDef retType ident args block

checkFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
checkFnDef retType ident args block = do
    env <- get
    put $ Map.insert ident (FunType env retType args block) env