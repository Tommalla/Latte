-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for translating the program to assembly code.
module Translator where

import Control.Monad.State
import qualified Data.Map as Map

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data Code = NoIndent String | Indent String | CodeBlock [Code]
type Env = Map.Map Ident Int
type Translation a = State Env a


instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str
    show (CodeBlock code) = let tmp = foldl (\res c -> res ++ (show c) ++ "\n") "" code
        in take (length tmp - 1) tmp

entryProtocol :: Code
entryProtocol = CodeBlock [(Indent "pushl %ebp"), (Indent "movl %esp, %ebp")]

leaveProtocol :: Code
leaveProtocol = CodeBlock [(Indent "leave"), (Indent "ret")]

unpackIdent :: Ident -> String
unpackIdent (Ident str) = str

translate :: Program -> String
translate program = ".globl main\n\n" ++ (show $ fst (runState (translateProgram program) Map.empty)) ++ "\n"

translateProgram :: Program -> Translation Code
translateProgram (Program topDefs) = do
    res <- mapM (translateTopDef) topDefs
    return (CodeBlock res)

translateTopDef :: TopDef -> Translation Code
translateTopDef (FnDef t ident args block) = do
    let header = NoIndent $ (unpackIdent ident) ++ ":"
    env <- get
    bindArgs args
    translateBlock block
    put env
    return $ CodeBlock [header, entryProtocol, leaveProtocol]

translateBlock :: Block -> Translation Code
translateBlock (Block stmts) = do
    -- TODO: allocate vars before the body
    return (Indent "noop")

-- Binds the args in the environment and returns the total size allocated (in Bytes)
bindArgs :: [Arg] -> Translation Int
bindArgs args = bindArgsHelper 0 args
    where
    bindArgsHelper :: Int -> [Arg] -> Translation Int
    bindArgsHelper lastSize ((Arg t ident):rest) = do
        let allocSize = getSize t
        env <- get
        put $ Map.insert ident (lastSize - allocSize) env
        bindArgsHelper (lastSize - allocSize) rest
    bindArgsHelper res [] = return res

-- Returns the variable size in bytes.
getSize :: Type -> Int
getSize Int = 4
getSize Bool = 1
getSize _ = undefined


