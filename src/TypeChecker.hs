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
    mainType <- getExtType (Ident "main")
    case mainType of
        (FunType _ retType args block) -> do
            env <- get  -- We need current env b/c of declarations
            -- TODO no top-level args for now
            checkFnInv retType [] [] block
        _ -> error $ "'main' is not a function. The actual type is: " ++ (show mainType)

checkTopDef :: TopDef -> Eval ()
checkTopDef (FnDef retType ident args block) = checkFnDef retType ident args block

checkFnDef :: Type -> Ident -> [Arg] -> Block -> Eval ()
checkFnDef retType ident args block = do
    env <- get
    put $ Map.insert ident (FunType env retType args block) env

getExtType :: Ident -> Eval ExtType
getExtType ident = do
    env <- get
    case Map.lookup ident env of
        (Just t) -> return t
        Nothing -> error $ "Identifier " ++ (show ident) ++ " unknown"

getType :: Ident -> Eval Type
getType ident = do
    extType <- getExtType ident
    case extType of
        (NormalType t) -> return t
        _ -> error $ (show ident) ++ ": basic data type expected, found: " ++ (show extType)

checkFnInv :: Type -> [Arg] -> [Ident] -> Block -> Eval ()
checkFnInv retType args passedIdents block = do
    env <- get
    bindArgs args passedIdents
    actRetType <- checkBlock block
    put env
    if retType == actRetType then
        return ()
    else error $ "TODO wrong return type " ++ (show retType) ++ " is not " ++ (show actRetType)

bindArgs :: [Arg] -> [Ident] -> Eval ()
bindArgs args passedIdents = mapM_ (\(arg, ident) -> bindArg arg ident) $ zip args passedIdents

bindArg :: Arg -> Ident -> Eval ()
bindArg (Arg t ident) passedIdent = do
    env <- get
    passedT <- getType passedIdent
    if passedT == t then
        put $ Map.insert ident (NormalType t) env
    else error $ "TODO passed argument type does not match the declaration."

checkBlock :: Block -> Eval Type
checkBlock (Block stmts) = do
    checkBlockHelper stmts
    where
        checkBlockHelper :: [Stmt] -> Eval Type
        checkBlockHelper (stmt : t) = do
            retType <- checkStmt stmt
            case retType of
                (Just result) -> return result
                Nothing -> checkBlockHelper t
        checkBlockHelper [] = error $ "TODO: No return in the block"

checkStmt :: Stmt -> Eval (Maybe Type)
checkStmt VRet = return (Just Void)
checkStmt _ = return Nothing