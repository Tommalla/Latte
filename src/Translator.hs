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
    blockCode <- translateBlock block
    put env
    return $ CodeBlock [header, entryProtocol, blockCode, leaveProtocol]

translateBlock :: Block -> Translation Code
translateBlock (Block stmts) = do
    allocation <- allocVars stmts
    -- TODO actual stmts
    return $ CodeBlock [allocation]

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
getSize _ = 0   -- TODO

allocVars :: [Stmt] -> Translation Code
allocVars stmts = do
    size <- allocVarsHelper 0 stmts
    return $ Indent ("movl $" ++ (show size) ++ ", %esp")
    where
    allocVarsHelper :: Int -> [Stmt] -> Translation Int
    allocVarsHelper lastSize (h:rest) = do
        case h of
            (Decl t items) -> do
                let size = getSize t
                newSize <- allocItems lastSize size items
                allocVarsHelper newSize rest
            _ -> allocVarsHelper lastSize rest
    allocVarsHelper res [] = return res

allocItems :: Int -> Int -> [Item] -> Translation Int
allocItems lastSize size (h:t) = do
    nextS <- allocItem lastSize size h
    allocItems nextS size t
allocItems res _ [] = return res

allocItem :: Int -> Int -> Item -> Translation Int
allocItem lastSize size item = do
    env <- get
    put $ Map.insert (getIdent item) (lastSize + size) env
    return $ lastSize + size

getIdent :: Item -> Ident
getIdent (NoInit res) = res
getIdent (Init res _) = res

