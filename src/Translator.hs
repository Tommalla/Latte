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
leaveProtocol = CodeBlock [(Indent "leave")]

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
    -- TODO args
    -- TODO block
    return $ CodeBlock [header, entryProtocol, leaveProtocol]


