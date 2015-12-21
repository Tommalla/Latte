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
    deriving (Show)
type Env = Map.Map Ident ExtType
type Eval a = ExceptT String (State Env) a

typeCheck :: Program -> Maybe String
typeCheck program = case fst (runState (runExceptT (checkProgram program)) Map.empty) of
    (Right _) -> Nothing
    (Left msg) -> Just msg

checkProgram :: Program -> Eval ()
checkProgram (Program topDefs) = do
    mapM_ (checkTopDef) topDefs
    mainType <- getType (Ident "main")
    case mainType of
        (FunType _ retType args block) -> do
            env <- get  -- We need current env b/c of declarations
            checkFnInv retType args block
        _ -> error $ "'main' is not a function. The actual type is: " ++ (show mainType)

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef retType ident args block) = checkFnDef retType ident args block

checkFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
checkFnDef retType ident args block = do
    env <- get
    put $ Map.insert ident (FunType env retType args block) env

getType :: Ident -> Eval ExtType
getType ident = do
    env <- get
    case Map.lookup ident env of
        (Just t) -> return t
        Nothing -> error $ "Identifier " ++ (show ident) ++ " unknown"

checkFnInv :: Type -> [Arg] -> Block -> Eval ()
checkFnInv retType args block = return ()