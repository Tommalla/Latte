-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for translating the program to assembly code.
module Translator where

import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Debug.Trace (trace)

import AbsLatte
import Common
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data Code = NoIndent String | Indent String | CodeBlock [Code] | Noop | EmptyLine
data MetaOp = Mul MulOp | Add AddOp | Rel RelOp
type Env = Map.Map Ident (Type, Int)
type SEnv = Map.Map String String  -- Maps string to its label
type PEnv = Map.Map Ident Type -- Maps procedures to returned type
type Translation a = State (Env, SEnv, PEnv, Int, Int) a  -- Env, -Local stack size, Max label number

instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str
    show (CodeBlock code) = let tmp = foldl (\res c -> res ++ (show c) ++ "\n") "" code
        in take (length tmp - 1) tmp
    show Noop = "  nop"
    show EmptyLine = ""

unpackIdent :: Ident -> String
unpackIdent (Ident str) = str

translate :: Program -> String
translate program = (".globl main\n\n" ++
        (show $ fst (runState (translateProgram program) (Map.empty, Map.empty, Map.empty, 0, 0))) ++ "\n")

translateProgram :: Program -> Translation Code
translateProgram (Program topDefs) = do
    fillPEnv (Program topDefs)
    strings <- stringsData (Program topDefs)
    res <- mapM (translateTopDef) topDefs
    return $ CodeBlock [strings, EmptyLine, CodeBlock res]

fillPEnv :: Program -> Translation ()
fillPEnv (Program topDefs) = do
    mapM_ (registerFunc) topDefs
    mapM_ (registerFunc) (map (\(t, name, args) -> FnDef t (Ident name) args $ Block [Empty]) builtins)
    where
    registerFunc :: TopDef -> Translation ()
    registerFunc (FnDef retType ident _ _) = do
        (env, senv, penv, minSize, nextLabel) <- get
        put (env, senv, Map.insert ident retType penv, minSize, nextLabel)

translateTopDef :: TopDef -> Translation Code
translateTopDef (FnDef t ident args block) = do
    let header = NoIndent $ (unpackIdent ident) ++ ":"
    (env, senv, penv, minSize, _) <- get
    bindArgs args
    blockCode <- translateBlock block
    (_, _, _, _, nextLabel) <- get
    put (env, senv, penv, minSize, nextLabel)
    let (Block stmts) = block
    let doRet = if null stmts then True else
            case last stmts of
                VRet -> False
                (Ret _) -> False
                _ -> True
    let codeList = if doRet
            then [header, entryProtocol, blockCode, leaveProtocol]
            else [header, entryProtocol, blockCode]
    return $ CodeBlock codeList

translateBlock :: Block -> Translation Code
translateBlock (Block stmts) = do
    mem <- get
    allocation <- allocVars stmts
    -- At this point all is allocated, but we need to restore the env
    put mem
    code <- mapM (translateStmt) stmts
    return $ CodeBlock (allocation:code)

translateStmt :: Stmt -> Translation Code
translateStmt Empty = return Noop
translateStmt (BStmt (Block stmts)) = do
    (env, penv, senv, minSize, _) <- get
    res <- mapM (translateStmt) stmts
    (_, _, _, _, nextLabel) <- get
    put (env, penv, senv, minSize, nextLabel)
    return $ CodeBlock res
translateStmt (Decl t items) = do
    (_, _, _, size, _) <- get
    (_, res) <- allocItems size t items
    return res
translateStmt (Ass ident expr) = do
    exprCode <- translateExpr expr
    varCode <- getVarCode ident
    return $ CodeBlock [exprCode, popl varCode]
translateStmt (Incr ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "incl " ++ varCode
translateStmt (Decr ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "decl " ++ varCode
translateStmt (Ret expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, popl eax, leaveProtocol]
translateStmt VRet = return leaveProtocol
translateStmt (Cond expr stmt) = do
    exprCode <- translateExpr expr
    lExit <- getNextLabel
    stmtCode <- translateStmt $ toBlock stmt
    let jmp = CodeBlock [popl eax, Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lExit)]
    return $ CodeBlock [exprCode, jmp, stmtCode, getLabelCode lExit]
translateStmt (CondElse expr stmt1 stmt2) = do
    exprCode <- translateExpr expr
    lTrue <- getNextLabel
    lExit <- getNextLabel
    stmt1Code <- translateStmt $ toBlock stmt1
    stmt2Code <- translateStmt $ toBlock stmt2
    let jmp = CodeBlock [popl eax, Indent "testl %eax, %eax", Indent $ "jnz " ++ (getLabel lTrue)]
    return $ CodeBlock [exprCode, jmp, stmt2Code, Indent $ "jmp " ++ (getLabel lExit),
                        getLabelCode lTrue, stmt1Code, getLabelCode lExit]
translateStmt (While expr stmt) = do
    exprCode <- translateExpr expr
    lBegin <- getNextLabel
    lExit <- getNextLabel
    stmtCode <- translateStmt $ toBlock stmt
    let jmp = CodeBlock [popl eax, Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lExit)]
    return $ CodeBlock [getLabelCode lBegin, exprCode, jmp, stmtCode, Indent $ "jmp " ++ (getLabel lBegin),
                        getLabelCode lExit]
translateStmt (SExp expr) = translateExpr expr

-- Invariant: Every expression ends with pushing the result on the stack
translateExpr :: Expr -> Translation Code
translateExpr (ENewArr t size) = return Noop -- TODO
translateExpr (EArrElem ident idx) = return Noop -- TODO
translateExpr (EVar ident) = do
    varCode <- getVarCode ident
    return $ pushl varCode
translateExpr (ELitInt num) = return $ pushl $ "$" ++ (show num)
translateExpr ELitTrue = return $ pushl "$1"
translateExpr ELitFalse = return $ pushl "$0"
translateExpr (EApp ident args) = do
    exprs <- mapM (translateExpr) args
    retType <- getFnRetType ident
    let remParams = map (\_ -> popl ebx) [1..(length args)]
    if retType /= Void then
        return $ CodeBlock [CodeBlock exprs, call ident, CodeBlock remParams, pushl eax]
    else return $ CodeBlock [CodeBlock exprs, call ident, CodeBlock remParams]
translateExpr (EString str) = do
    lStr <- getStringLabel str
    return $ pushl $ "$" ++ lStr
translateExpr (Neg expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, popl eax, Indent "neg %eax", pushl eax]
translateExpr (Not expr) = do
    exprCode <- translateExpr expr
    lFalse <- getNextLabel
    lExit <- getNextLabel
    let labelFalse = CodeBlock [NoIndent $ (getLabel lFalse) ++ ":", pushl "$1"]
    return $ CodeBlock [exprCode, popl eax, Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lFalse),
                        pushl "$0", jmp $ getLabel lExit, labelFalse, NoIndent $(getLabel lExit) ++ ":"]
translateExpr (EMul expr1 mop expr2) = translateBinaryOp expr1 expr2 (Mul mop)
translateExpr (EAdd expr1 aop expr2) = translateBinaryOp expr1 expr2 (Add aop)
translateExpr (ERel expr1 rop expr2) = translateBinaryOp expr1 expr2 (Rel rop)
translateExpr (EAnd expr1 expr2) = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    lFalse <- getNextLabel
    lExit <- getNextLabel
    let checkRes = CodeBlock [popl eax, Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lFalse)]
    let labelFalse = CodeBlock [NoIndent $ (getLabel lFalse) ++ ":", pushl "$0"]
    return $ CodeBlock [expr1Code, checkRes, expr2Code, checkRes, pushl "$1", jmp $ getLabel lExit,
                        labelFalse, NoIndent $ (getLabel lExit) ++ ":"]
translateExpr (EOr expr1 expr2) = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    lTrue <- getNextLabel
    lExit <- getNextLabel
    let checkRes = CodeBlock [popl eax, Indent "testl %eax, %eax", Indent $ "jnz " ++ (getLabel lTrue)]
    let labelTrue = CodeBlock [NoIndent $ (getLabel lTrue) ++ ":", pushl "$1"]
    return $ CodeBlock [expr1Code, checkRes, expr2Code, checkRes, pushl "$0", jmp $ getLabel lExit, labelTrue,
                        NoIndent $ (getLabel lExit) ++ ":"]

getExprType :: Expr -> Translation Type
getExprType (ENewArr t _) = return (Array t)
getExprType (EArrElem _ _) = undefined -- TODO
getExprType (EVar ident) = getVarType ident
getExprType (ELitInt _) = return Int
getExprType ELitTrue = return Bool
getExprType ELitFalse = return Bool
getExprType (EApp ident _) = getFnRetType ident
getExprType (EString _) = return Str
getExprType (Neg _) = return Int
getExprType (Not _) = return Bool
getExprType (EMul _ _ _) = return Int -- You can only multiply ints.
getExprType (EAdd a Plus _) = getExprType a -- You can add things of the same type
getExprType (EAdd _ Minus _) = return Int -- You can subtract ints.
getExprType (ERel _ _ _) = return Bool
getExprType (EAnd _ _) = return Bool
getExprType (EOr _ _) = return Bool

translateBinaryOp :: Expr -> Expr -> MetaOp -> Translation Code
translateBinaryOp expr1 expr2 metaOp = do
    resT <- getExprType expr1
    if isString resT then
        -- Both have to be string and op has to be addition, otherwise this would fail.
        translateStringAddition expr1 expr2
    else translateBinaryArithmeticOp expr1 expr2 metaOp

translateBinaryArithmeticOp :: Expr -> Expr -> MetaOp -> Translation Code
translateBinaryArithmeticOp expr1 expr2 metaOp = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    opCode <- translateMetaOp metaOp
    return $ CodeBlock [expr1Code, expr2Code, opCode]

translateStringAddition :: Expr -> Expr -> Translation Code
translateStringAddition expr1 expr2 = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    return $ CodeBlock [expr1Code, expr2Code, swapArgs, call concatStrings, pushl eax]

translateMetaOp :: MetaOp -> Translation Code
translateMetaOp (Mul mop) = do
    let divOp = [popl ebx, popl eax, Indent "movl %eax, %edx", Indent "sar $31, %edx",
                 Indent "idiv %ebx"]
    return $ case mop of
            Times -> CodeBlock [popl eax, Indent "imul 0(%esp), %eax", movl eax "0(%esp)"]
            Div -> CodeBlock [CodeBlock divOp, pushl eax]
            Mod -> CodeBlock [CodeBlock divOp, pushl edx]
translateMetaOp (Add aop) = return $ case aop of
            Plus -> CodeBlock [popl eax, Indent "addl 0(%esp), %eax", movl eax "0(%esp)"]
            Minus -> CodeBlock [popl eax, popl ebx, Indent "subl %eax, %ebx", pushl ebx]
translateMetaOp (Rel rop) = do
    lFalse <- getNextLabel
    lExit <- getNextLabel
    let jmp = case rop of
            LTH -> "jge"
            LE -> "jg"
            GTH -> "jle"
            GE -> "jl"
            EQU -> "jne"
            NE -> "je"
    return $ CodeBlock [popl eax, Indent "cmp %eax, 0(%esp)", Indent $ jmp ++ " " ++ (getLabel lFalse),
                        pushl "$1", Indent $ "jmp " ++ (getLabel lExit), getLabelCode lFalse, Indent "pushl $0",
                        getLabelCode lExit]

getVarCode :: Ident -> Translation String
getVarCode ident = do
    offset <- getVarIdx ident
    return $ (show offset) ++ "(%ebp)"

getVarType :: Ident -> Translation Type
-- getVarType ident | trace ("getVarType " ++ show ident) False = undefined
getVarType ident = do
    (env, _, _, _, _) <- get
    return $ fst $ env Map.! ident

getVarIdx :: Ident -> Translation Int
-- getVarIdx ident | trace ("getVarIdx " ++ show ident) False = undefined
getVarIdx ident = do
    (env, _, _, _, _) <- get
    return $ snd $ env Map.! ident

getFnRetType :: Ident -> Translation Type
getFnRetType ident = do
    (_, _, penv, _, _) <- get
    return $ penv Map.! ident

-- Binds the args in the environment and returns the total size allocated (in Bytes)
bindArgs :: [Arg] -> Translation ()
bindArgs args = do
    bindArgsHelper 4 (reverse args)
    return ()
    where
    bindArgsHelper :: Int -> [Arg] -> Translation Int
    bindArgsHelper lastSize ((Arg t ident):rest) = do
        let allocSize = getSize t
        (env, senv, penv, minSize, nextLabel) <- get
        put (Map.insert ident (t, lastSize + allocSize) env, senv, penv, minSize, nextLabel)
        bindArgsHelper (lastSize + allocSize) rest
    bindArgsHelper res [] = return res

-- Returns the variable size in bytes.
getSize :: Type -> Int
getSize Int = 4
getSize Bool = 4    -- Yes, let's use ints for now for consistency [FIXME]
getSize Str = 4     -- Ptr to actual string
getSize _ = 0   -- TODO

allocVars :: [Stmt] -> Translation Code
allocVars stmts = do
    size <- allocVarsHelper 0 stmts
    return $ Indent ("subl $" ++ (show (-size)) ++ ", %esp")
    where
    allocVarsHelper :: Int -> [Stmt] -> Translation Int
    allocVarsHelper lastSize (h:rest) = do
        case h of
            (Decl t items) -> do
                (newSize, _) <- allocItems lastSize t items
                allocVarsHelper newSize rest
            (BStmt (Block nextStmts)) -> do
                newSize <- allocVarsHelper lastSize nextStmts
                allocVarsHelper newSize rest
            (Cond _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            (CondElse _ s1 s2) -> allocVarsHelper lastSize (s1:(s2:rest))
            (While _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            _ -> allocVarsHelper lastSize rest
    allocVarsHelper res [] = return res

-- Alocates items - for every item, inits it and THEN records it in env.
allocItems :: Int -> Type -> [Item] -> Translation (Int, Code)
allocItems lastSize t (h:rest) = do
    (nextS, code) <- allocItem lastSize t h
    (resS, codeRest) <- allocItems nextS t rest
    return (resS, CodeBlock [code, codeRest])
allocItems res _ [] = return (res, Noop)

allocItem :: Int -> Type -> Item -> Translation (Int, Code)
allocItem lastSize t item = do
    let size = getSize t
    initExpr <- getInitExpr t item
    exprCode <- translateExpr initExpr
    let ident = getIdent item
    (env, senv, penv, minSize, nextLabel) <- get
    put (Map.insert ident (t, (lastSize - size)) env, senv, penv, min minSize (lastSize - size), nextLabel)
    varCode <- getVarCode ident
    return $ (lastSize - size, CodeBlock [exprCode, popl varCode])

getInitExpr :: Type -> Item -> Translation Expr
getInitExpr t (NoInit ident) = do
    case t of
        Str -> return $ EString ""
        _ -> return $ ELitInt 0
getInitExpr _ (Init _ expr) = return expr

getIdent :: Item -> Ident
getIdent (NoInit res) = res
getIdent (Init res _) = res

getNextLabel :: Translation Int
getNextLabel = do
    (env, senv, penv, minSize, nextLabel) <- get
    put (env, senv, penv, minSize, nextLabel + 1)
    return nextLabel

getLabel :: Int -> String
getLabel idx = ".L" ++ (show idx)

getLabelCode :: Int -> Code
getLabelCode idx = NoIndent $ (getLabel idx) ++ ":"

stringsData :: Program -> Translation Code
stringsData program = do
    let strings = extractStrings program
    foldM_ (\idx str -> do
            registerString str idx
            return $ idx + 1) 0 strings
    res <- mapM (storeString) strings
    return $ CodeBlock res

storeString :: String -> Translation Code
storeString str = do
    sLabel <- getStringLabel str
    return $ CodeBlock [NoIndent $ sLabel ++ ":", NoIndent $ ".string " ++ (show str)]

getStringLabel :: String -> Translation String
-- getStringLabel str | trace ("getStringLabel " ++ str) False = undefined
getStringLabel str = do
    (_, senv, _, _, _) <- get
    return $ senv Map.! str

registerString :: String -> Int -> Translation ()
registerString str idx = do
    (env, senv, penv, minSize, nextLabel) <- get
    let sLabel = ".S" ++ (show idx)
    put (env, Map.insert str sLabel senv, penv, minSize, nextLabel)

-- Extracting a list of all strings from the program
extractStrings :: Program -> [String]
extractStrings (Program topDefs) = nub $ extractStringsTopDefs topDefs

extractStringsTopDefs :: [TopDef] -> [String]
extractStringsTopDefs = concat . map (extractStringsTopDef)

extractStringsTopDef :: TopDef -> [String]
extractStringsTopDef (FnDef _ _ _ (Block stmts)) = extractStringsStmts stmts

extractStringsStmts :: [Stmt] -> [String]
extractStringsStmts = concat . map (extractStringsStmt)

extractStringsStmt :: Stmt -> [String]
extractStringsStmt (BStmt (Block stmts)) = extractStringsStmts stmts
extractStringsStmt (Decl Str items) = concat $ map (extractStringsItem) items
extractStringsStmt (Ass _ expr) = extractStringsExpr expr
extractStringsStmt (Ret expr) = extractStringsExpr expr
extractStringsStmt (Cond expr stmt) = (extractStringsExpr expr) ++ (extractStringsStmt stmt)
extractStringsStmt (CondElse expr stmt1 stmt2) = (extractStringsExpr expr) ++ (extractStringsStmt stmt1) ++
        (extractStringsStmt stmt2)
extractStringsStmt (While expr stmt) = extractStringsStmt (Cond expr stmt)
extractStringsStmt (SExp expr) = extractStringsExpr expr
extractStringsStmt _ = []

extractStringsItem :: Item -> [String]
extractStringsItem (Init _ expr) = extractStringsExpr expr
extractStringsItem (NoInit _) = [""]

extractStringsExpr :: Expr -> [String]
extractStringsExpr (EString str) = [str]
extractStringsExpr (EApp _ exprs) = concat $ map (extractStringsExpr) exprs
extractStringsExpr (EAdd expr1 Plus expr2) = (extractStringsExpr expr1) ++ (extractStringsExpr expr2)
extractStringsExpr _ = []

-- Assembler Code:
-- Builtins:
concatStrings :: Ident
concatStrings = Ident "__concatStrings"

-- Registers
eax :: String
eax = "%eax"

ebx :: String
ebx = "%ebx"

ecx :: String
ecx = "%ecx"

edx :: String
edx = "%edx"

-- Assembler:
call :: Ident -> Code
call (Ident str) = Indent $ "call " ++ str

pushl :: String -> Code
pushl src = Indent $ "pushl " ++ src

popl :: String -> Code
popl src = Indent $ "popl " ++ src

movl :: String -> String -> Code
movl src dst = Indent $ "movl " ++ src ++ ", " ++ dst

jmp :: String -> Code
jmp label = Indent $ "jmp " ++ label

swapArgs :: Code
swapArgs = CodeBlock [popl eax, popl ebx, pushl eax, pushl ebx]

-- Misc:
entryProtocol :: Code
entryProtocol = CodeBlock [(Indent "pushl %ebp"), (Indent "movl %esp, %ebp")]

leaveProtocol :: Code
leaveProtocol = CodeBlock [(Indent "leave"), (Indent "ret")]

toBlock :: Stmt -> Stmt
toBlock (BStmt block) = BStmt block
toBlock stmt = BStmt $ Block [stmt]