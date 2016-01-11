-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for translating the program to assembly code.
module Translator where

import Control.Monad.State
import Data.List
import qualified Data.Map as Map

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data Code = NoIndent String | Indent String | CodeBlock [Code] | Noop | EmptyLine
data MetaOp = Mul MulOp | Add AddOp | Rel RelOp
type Env = Map.Map Ident (Type, Int)
type SEnv = Map.Map String String  -- Maps string to its label
type Translation a = State (Env, SEnv, Int, Int) a  -- Env, -Local stack size, Max label number

instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str
    show (CodeBlock code) = let tmp = foldl (\res c -> res ++ (show c) ++ "\n") "" code
        in take (length tmp - 1) tmp
    show Noop = "  nop"
    show EmptyLine = ""

entryProtocol :: Code
entryProtocol = CodeBlock [(Indent "pushl %ebp"), (Indent "movl %esp, %ebp")]

leaveProtocol :: Code
leaveProtocol = CodeBlock [(Indent "leave"), (Indent "ret")]

unpackIdent :: Ident -> String
unpackIdent (Ident str) = str

translate :: Program -> String
translate program = (".globl main\n\n" ++
        (show $ fst (runState (translateProgram program) (Map.empty, Map.empty, 0, 0))) ++ "\n")

translateProgram :: Program -> Translation Code
translateProgram (Program topDefs) = do
    strings <- stringsData (Program topDefs)
    res <- mapM (translateTopDef) topDefs
    return $ CodeBlock [strings, EmptyLine, CodeBlock res]

translateTopDef :: TopDef -> Translation Code
translateTopDef (FnDef t ident args block) = do
    let header = NoIndent $ (unpackIdent ident) ++ ":"
    mem <- get
    bindArgs args
    blockCode <- translateBlock block
    put mem
    let (Block stmts) = block
    let doRet = case last stmts of
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
    res <- mapM (translateStmt) stmts
    return $ CodeBlock res
translateStmt (Decl t items) = do
    (_, _, size, _) <- get
    allocItems size t items
    initItems items
translateStmt (Ass ident expr) = do
    exprCode <- translateExpr expr
    varCode <- getVarCode ident
    return $ CodeBlock [exprCode, Indent $ "popl " ++ varCode]
translateStmt (Incr ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "incl " ++ varCode
translateStmt (Decr ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "decl " ++ varCode
translateStmt (Ret expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, Indent "popl %eax", leaveProtocol]
translateStmt VRet = return leaveProtocol
translateStmt (Cond expr stmt) = do
    exprCode <- translateExpr expr
    lExit <- getNextLabel
    stmtCode <- translateStmt stmt
    let jmp = CodeBlock [Indent "popl %eax", Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lExit)]
    return $ CodeBlock [exprCode, jmp, stmtCode, getLabelCode lExit]
translateStmt (CondElse expr stmt1 stmt2) = do
    exprCode <- translateExpr expr
    lTrue <- getNextLabel
    lExit <- getNextLabel
    stmt1Code <- translateStmt stmt1
    stmt2Code <- translateStmt stmt2
    let jmp = CodeBlock [Indent "popl %eax", Indent "testl %eax, %eax", Indent $ "jnz " ++ (getLabel lTrue)]
    return $ CodeBlock [exprCode, jmp, stmt2Code, Indent $ "jmp " ++ (getLabel lExit),
                        getLabelCode lTrue, stmt1Code, getLabelCode lExit]
translateStmt (While expr stmt) = do
    exprCode <- translateExpr expr
    lBegin <- getNextLabel
    lExit <- getNextLabel
    stmtCode <- translateStmt stmt
    let jmp = CodeBlock [Indent "popl %eax", Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lExit)]
    return $ CodeBlock [getLabelCode lBegin, exprCode, jmp, stmtCode, Indent $ "jmp " ++ (getLabel lBegin),
                        getLabelCode lExit]
translateStmt (SExp expr) = translateExpr expr

-- Invariant: Every expression ends with pushing the result on the stack
translateExpr :: Expr -> Translation Code
translateExpr (ENewArr t size) = return Noop -- TODO
translateExpr (EArrElem ident idx) = return Noop -- TODO
translateExpr (EVar ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "pushl " ++ varCode
translateExpr (ELitInt num) = return $ Indent $ "pushl $" ++ (show num)
translateExpr ELitTrue = return $ Indent "pushl $1"
translateExpr ELitFalse = return $ Indent "pushl $0"
translateExpr (EApp ident args) = do
    exprs <- mapM (translateExpr) args
    return $ CodeBlock [CodeBlock exprs, Indent $ "call " ++ (unpackIdent ident), Indent "pushl %eax"]
translateExpr (EString str) = do
    lStr <- getStringLabel str
    return $ Indent $ "pushl $" ++ lStr
translateExpr (Neg expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, Indent "popl %eax", Indent "neg %eax", Indent "pushl %eax"]
translateExpr (Not expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, Indent "popl %eax", Indent "not %eax", Indent "pushl %eax"]
translateExpr (EMul expr1 mop expr2) = translateBinaryOp expr1 expr2 (Mul mop)
translateExpr (EAdd expr1 aop expr2) = translateBinaryOp expr1 expr2 (Add aop)
translateExpr (ERel expr1 rop expr2) = translateBinaryOp expr1 expr2 (Rel rop)
translateExpr (EAnd expr1 expr2) = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    lFalse <- getNextLabel
    lExit <- getNextLabel
    let checkRes = CodeBlock [Indent "popl %eax", Indent "testl %eax, %eax", Indent $ "jz " ++ (getLabel lFalse)]
    let labelFalse = CodeBlock [NoIndent $ (getLabel lFalse) ++ ":", Indent $ "pushl $0"]
    return $ CodeBlock [expr1Code, checkRes, expr2Code, checkRes, Indent "pushl $1",
                        Indent $ "jmp "++ (getLabel lExit), labelFalse, NoIndent $ (getLabel lExit) ++ ":"]
translateExpr (EOr expr1 expr2) = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    lTrue <- getNextLabel
    lExit <- getNextLabel
    let checkRes = CodeBlock [Indent "popl %eax", Indent "testl %eax, %eax", Indent $ "jnz " ++ (getLabel lTrue)]
    let labelTrue = CodeBlock [NoIndent $ (getLabel lTrue) ++ ":", Indent "pushl $1"]
    return $ CodeBlock [expr1Code, checkRes, expr2Code, checkRes, Indent "pushl $0",
                        Indent $ "jmp " ++ (getLabel lExit), labelTrue, NoIndent $ (getLabel lExit) ++ ":"]

translateBinaryOp :: Expr -> Expr -> MetaOp -> Translation Code
translateBinaryOp expr1 expr2 metaOp = do
    expr1Code <- translateExpr expr1
    expr2Code <- translateExpr expr2
    opCode <- translateMetaOp metaOp
    return $ CodeBlock [expr1Code, expr2Code, opCode]

translateMetaOp :: MetaOp -> Translation Code
translateMetaOp (Mul mop) = do
    let divOp = [Indent "popl %ebx", Indent "popl %eax", Indent "movl %eax, %edx", Indent "shr $31, %edx",
                 Indent "idiv %ebx"]
    return $ case mop of
            Times -> CodeBlock [Indent "popl %eax", Indent "imul 0(%esp), %eax", Indent "pushl %eax"]
            Div -> CodeBlock [CodeBlock divOp, Indent "pushl %eax"]
            Mod -> CodeBlock [CodeBlock divOp, Indent "pushl %edx"]
translateMetaOp (Add aop) = return $ case aop of
            Plus -> CodeBlock [Indent "popl %eax", Indent "addl 0(%esp), %eax", Indent "pushl %eax"]
            Minus -> CodeBlock [Indent "popl %eax", Indent "popl %ebx", Indent "subl %eax, %ebx", Indent "pushl %ebx"]
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
    return $ CodeBlock [Indent "popl %eax", Indent "cmp %eax, 0(%esp)", Indent $ jmp ++ " " ++ (getLabel lFalse),
                        Indent "pushl $1", Indent $ "jmp " ++ (getLabel lExit), getLabelCode lFalse, Indent "pushl $0",
                        getLabelCode lExit]

getVarCode :: Ident -> Translation String
getVarCode ident = do
    offset <- getVarIdx ident
    return $ (show offset) ++ "(%ebp)"

getVarType :: Ident -> Translation Type
getVarType ident = do
    (env, _, _, _) <- get
    return $ fst $ env Map.! ident

getVarIdx :: Ident -> Translation Int
getVarIdx ident = do
    (env, _, _, _) <- get
    return $ snd $ env Map.! ident

-- Binds the args in the environment and returns the total size allocated (in Bytes)
bindArgs :: [Arg] -> Translation Int
bindArgs args = bindArgsHelper 4 args
    where
    bindArgsHelper :: Int -> [Arg] -> Translation Int
    bindArgsHelper lastSize ((Arg t ident):rest) = do
        let allocSize = getSize t
        (env, senv, minSize, nextLabel) <- get
        put (Map.insert ident (t, (lastSize + allocSize)) env, senv, minSize, nextLabel)
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
                newSize <- allocItems lastSize t items
                allocVarsHelper newSize rest
            (BStmt (Block nextStmts)) -> do
                newSize <- allocVarsHelper lastSize nextStmts
                allocVarsHelper newSize rest
            (Cond _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            (CondElse _ s1 s2) -> allocVarsHelper lastSize (s1:(s2:rest))
            (While _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            _ -> allocVarsHelper lastSize rest
    allocVarsHelper res [] = return res

allocItems :: Int -> Type -> [Item] -> Translation Int
allocItems lastSize t (h:rest) = do
    nextS <- allocItem lastSize t h
    allocItems nextS t rest
allocItems res _ [] = return res

allocItem :: Int -> Type -> Item -> Translation Int
allocItem lastSize t item = do
    let size = getSize t
    (env, senv, minSize, nextLabel) <- get
    put (Map.insert (getIdent item) (t, (lastSize - size)) env, senv, min minSize (lastSize - size), nextLabel)
    return $ lastSize - size

initItems :: [Item] -> Translation Code
initItems items = do
    initCode <- mapM (initItem) items
    return $ CodeBlock initCode

initItem :: Item -> Translation Code
initItem (NoInit ident) = do
    t <- getVarType ident
    case t of
        Str -> return Noop -- TODO
        _ -> do -- For now we assume numeric, will change with arrays
            varCode <- getVarCode ident
            return $ Indent $ "movl $0, " ++ varCode
initItem (Init ident expr) = translateStmt (Ass ident expr)

getIdent :: Item -> Ident
getIdent (NoInit res) = res
getIdent (Init res _) = res

getNextLabel :: Translation Int
getNextLabel = do
    (env, senv, minSize, nextLabel) <- get
    put (env, senv, minSize, nextLabel + 1)
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
getStringLabel str = do
    (_, senv, _, _) <- get
    return $ senv Map.! str

registerString :: String -> Int -> Translation ()
registerString str idx = do
    (env, senv, minSize, nextLabel) <- get
    let sLabel = ".S" ++ (show idx)
    put (env, Map.insert str sLabel senv, minSize, nextLabel)

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
extractStringsItem _ = []

extractStringsExpr :: Expr -> [String]
extractStringsExpr (EString str) = [str]
extractStringsExpr (EApp _ exprs) = concat $ map (extractStringsExpr) exprs
extractStringsExpr (EAdd expr1 Plus expr2) = (extractStringsExpr expr1) ++ (extractStringsExpr expr2)
extractStringsExpr _ = []