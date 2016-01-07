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

data Code = NoIndent String | Indent String | CodeBlock [Code] | Noop
data MetaOp = Mul MulOp | Add AddOp | Rel RelOp
type Env = Map.Map Ident Int
type Translation a = State (Env, Int, Int) a  -- Env, -Local stack size, Max label number


instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str
    show (CodeBlock code) = let tmp = foldl (\res c -> res ++ (show c) ++ "\n") "" code
        in take (length tmp - 1) tmp
    show (Noop) = "  nop"

entryProtocol :: Code
entryProtocol = CodeBlock [(Indent "pushl %ebp"), (Indent "movl %esp, %ebp")]

leaveProtocol :: Code
leaveProtocol = CodeBlock [(Indent "leave"), (Indent "ret")]

unpackIdent :: Ident -> String
unpackIdent (Ident str) = str

translate :: Program -> String
translate program = ".globl main\n\n" ++ (show $ fst (runState (translateProgram program) (Map.empty, 0, 0))) ++ "\n"

translateProgram :: Program -> Translation Code
translateProgram (Program topDefs) = do
    res <- mapM (translateTopDef) topDefs
    return (CodeBlock res)

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
    (_, size, _) <- get
    let tSize = getSize t
    allocItems size tSize items
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
translateExpr (EString str) = return Noop
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

getVarIdx :: Ident -> Translation Int
getVarIdx ident = do
    (env, _, _) <- get
    return $ env Map.! ident

-- Binds the args in the environment and returns the total size allocated (in Bytes)
bindArgs :: [Arg] -> Translation Int
bindArgs args = bindArgsHelper 4 args
    where
    bindArgsHelper :: Int -> [Arg] -> Translation Int
    bindArgsHelper lastSize ((Arg t ident):rest) = do
        let allocSize = getSize t
        (env, minSize, nextLabel) <- get
        put (Map.insert ident (lastSize + allocSize) env, minSize, nextLabel)
        bindArgsHelper (lastSize + allocSize) rest
    bindArgsHelper res [] = return res

-- Returns the variable size in bytes.
getSize :: Type -> Int
getSize Int = 4
getSize Bool = 4    -- Yes, let's use ints for now for consistency [FIXME]
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
                let size = getSize t
                newSize <- allocItems lastSize size items
                allocVarsHelper newSize rest
            (BStmt (Block nextStmts)) -> do
                newSize <- allocVarsHelper lastSize nextStmts
                allocVarsHelper newSize rest
            (Cond _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            (CondElse _ s1 s2) -> allocVarsHelper lastSize (s1:(s2:rest))
            (While _ stmt) -> allocVarsHelper lastSize (stmt:rest)
            _ -> allocVarsHelper lastSize rest
    allocVarsHelper res [] = return res

allocItems :: Int -> Int -> [Item] -> Translation Int
allocItems lastSize size (h:t) = do
    nextS <- allocItem lastSize size h
    allocItems nextS size t
allocItems res _ [] = return res

allocItem :: Int -> Int -> Item -> Translation Int
allocItem lastSize size item = do
    (env, minSize, nextLabel) <- get
    put (Map.insert (getIdent item) (lastSize - size) env, min minSize (lastSize - size), nextLabel)
    return $ lastSize - size

initItems :: [Item] -> Translation Code
initItems items = do
    initCode <- mapM (initItem) items
    return $ CodeBlock initCode

initItem :: Item -> Translation Code
initItem (NoInit ident) = do
    varCode <- getVarCode ident
    return $ Indent $ "movl $0, " ++ varCode
initItem (Init ident expr) = translateStmt (Ass ident expr)

getIdent :: Item -> Ident
getIdent (NoInit res) = res
getIdent (Init res _) = res

getNextLabel :: Translation Int
getNextLabel = do
    (env, minSize, nextLabel) <- get
    put (env, minSize, nextLabel + 1)
    return nextLabel

getLabel :: Int -> String
getLabel idx = ".L" ++ (show idx)

getLabelCode :: Int -> Code
getLabelCode idx = NoIndent $ (getLabel idx) ++ ":"