-- Tomasz Zakrzewski, tz336079, 2015-2016
-- This module is responsible for translating the program to assembly code.
module Translator where

import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

import AbsLatte
import Common
import ErrM
import LexLatte
import ParLatte
import PrintLatte
import StaticAnalyser (extractStrings)

data Code = NoIndent String | Indent String | CodeBlock [Code] | Noop | EmptyLine
    deriving (Eq)
data MetaOp = Mul MulOp | Add AddOp | Rel RelOp
type ClsType =  (Maybe Ident, Env, Map.Map Ident (Type, Maybe Int, Ident), Int, Int) -- parent, Env, PEnv for classes -
        -- we map every procedure to (retType, maybe id in vtable), the number of virtual methods (initially -1), the
        -- alignment size
type Env = Map.Map Ident (Type, Int)
type SEnv = Map.Map String String  -- Maps string to its label
type PEnv = Map.Map Ident Type -- Maps procedures to returned type
type CEnv = Map.Map Ident ClsType
type Translation a = State (Env, SEnv, PEnv, CEnv, Int, Int, Int) a  -- Env, -Local stack size, Max label number

instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str
    show (CodeBlock code) = let tmp = foldl (\res c -> res ++ (show c) ++ "\n") "" code
        in take (length tmp - 1) tmp
    show Noop = "  nop"
    show EmptyLine = ""

translate :: Program -> String
translate program = (".globl main\n\n" ++
        (show $ fst (runState (translateProgram program) (Map.empty, Map.empty, Map.empty, Map.empty, 0, 0, 0))) ++ "\n")

-- Top-level translation -----------------------------------------------------------------------------------------------

translateProgram :: Program -> Translation Code
translateProgram (Program topDefs) = do
    fillPEnv (Program topDefs)
    fillCEnv (Program topDefs)
    vTablesCode <- prepVTables
    strings <- stringsData (Program topDefs)
    res <- mapM (translateTopDef) topDefs
    vTables <- prepVTables
    return $ CodeBlock [strings, vTables, EmptyLine, CodeBlock res]

prepVTables :: Translation Code
prepVTables = do
    (_, _, _, cenv, _, _, _) <- get
    code <- mapM (prepVTable . fst) $ Map.toList cenv
    return $ CodeBlock $ filter (\c -> c /= EmptyLine) code

prepVTable :: Ident -> Translation Code
prepVTable ident = do
    (_, _, penv, _, _) <- getClass ident
    let virt = map (\(fName, (_, v, cName)) -> (fromJust v, (unpackIdent cName) ++ "$" ++ (unpackIdent fName))) $
            filter (\(fName, (_, v, _)) -> isJust v) $ Map.toList penv
    let virtOrd = sort virt
    let arr = foldl (\acc (_, e) -> acc ++ "," ++ e) "" virtOrd
    if not $ null arr then
        return $ NoIndent $ (getVTableName ident) ++ ": .int " ++ (tail arr)
    else return EmptyLine

translateTopDef :: TopDef -> Translation Code
translateTopDef (FnDef (FunDef t ident args block)) = do
    let header = NoIndent $ (unpackIdent ident) ++ ":"
    size <- bindArgs args
    (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
    when (Map.member (Ident "self") env) (do
        let (selfT, selfAlign) = env Map.! (Ident "self")
        when (selfAlign < 0) (
                put (Map.insert (Ident "self") (selfT, size + (getSize selfT)) env, senv, penv, cenv, minSize,
                     nextLabel, maxTemp)))
    blockCode <- translateBlock block
    (_, _, _, _, _, nextLabel, _) <- get
    put (env, senv, penv, cenv, minSize, nextLabel, maxTemp)
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
translateTopDef (ClassDef (Ident cName) cdefs) = do
    (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
    put (Map.insert (Ident "self") (Class $ Ident cName, -1) env, senv, penv, cenv, minSize, nextLabel,
            maxTemp)
    let methods = filter (\cdef -> case cdef of
            (Method _) -> True
            _ -> False) cdefs
    code <- mapM (\(Method (FunDef t (Ident fName) args block)) ->
            translateTopDef (FnDef $ FunDef t (Ident $ cName ++ "$" ++ fName) args block)) methods
    (_, _, _, _, _, nextLabel, _) <- get
    put (env, senv, penv, cenv, minSize, nextLabel, maxTemp)
    return $ CodeBlock code
translateTopDef (ClassExtDef ident _ cdefs) = translateTopDef (ClassDef ident cdefs)  -- Inheritance matters only for
                                                                                      -- env.

translateBlock :: Block -> Translation Code
translateBlock (Block stmts) = do
    mem <- get
    allocation <- allocVars stmts
    -- At this point all is allocated, but we need to restore the env
    put mem
    code <- mapM (translateStmt) stmts
    return $ CodeBlock (allocation:code)

-- Statements ----------------------------------------------------------------------------------------------------------

translateStmt :: Stmt -> Translation Code
translateStmt Empty = return Noop
translateStmt (BStmt (Block stmts)) = do
    (env, penv, senv, cenv, minSize, _, maxTemp) <- get
    res <- mapM (translateStmt) stmts
    (_, _, _, _, _, nextLabel, _) <- get
    put (env, penv, senv, cenv, minSize, nextLabel, maxTemp)
    return $ CodeBlock res
translateStmt (Decl t items) = do
    (_, _, _, _, size, _, _) <- get
    (_, res) <- allocItems size t items
    return res
translateStmt (Ass lval expr) = do
    t <- getExprType expr
    lvalCode <- translateLVal lval
    exprCode <- translateExpr expr
    let commonCode = CodeBlock [lvalCode, exprCode]
    case t of
        Bool -> do
            lTrue <- getNextLabel
            lFalse <- getNextLabel
            lExit <- getNextLabel
            exprCode <- translateBoolExpr expr lTrue lFalse
            return $ CodeBlock [lvalCode, exprCode, popl eax, getLabelCode lTrue, movl "$1" $ "(%eax)",
                                jmp $ getLabel lExit, getLabelCode lFalse, movl "$0" "(%eax)", getLabelCode lExit]
        (Array _) -> return $ CodeBlock [commonCode, popl eax, popl ebx, popl ecx, movl eax "(%ecx)",
                                         Indent $ "addl $4, " ++ ecx, movl ebx "(%ecx)"]
        _ -> return $ CodeBlock [commonCode, popl eax, popl ebx, movl eax "(%ebx)"]
translateStmt (Incr lval) = do
    lvalCode <- translateLVal lval
    return $ CodeBlock [lvalCode, popl eax, Indent "incl (%eax)"]
translateStmt (Decr lval) = do
    lvalCode <- translateLVal lval
    return $ CodeBlock [lvalCode, popl eax, Indent "decl (%eax)"]
translateStmt (Ret expr) = do
    t <- getExprType expr
    exprCode <- translateExpr expr
    case t of
        (Array _) -> return $ CodeBlock [exprCode, popl eax, popl edx, leaveProtocol]
            -- in case of array, return ptr to array
        _ -> return $ CodeBlock [exprCode, popl eax, leaveProtocol]
translateStmt VRet = return leaveProtocol
translateStmt (Cond expr stmt) = do
    lTrue <- getNextLabel
    lFalse <- getNextLabel
    exprCode <- translateBoolExpr expr lTrue lFalse
    stmtCode <- translateStmt $ toBlock stmt
    return $ CodeBlock [exprCode, getLabelCode lTrue, stmtCode, getLabelCode lFalse]
translateStmt (CondElse expr stmt1 stmt2) = do
    lTrue <- getNextLabel
    lFalse <- getNextLabel
    lExit <- getNextLabel
    exprCode <- translateBoolExpr expr lTrue lFalse
    stmt1Code <- translateStmt $ toBlock stmt1
    stmt2Code <- translateStmt $ toBlock stmt2
    return $ CodeBlock [exprCode, getLabelCode lTrue, stmt1Code, jmp $ getLabel lExit, getLabelCode lFalse, stmt2Code,
                        getLabelCode lExit]
translateStmt (While expr stmt) = do
    lBegin <- getNextLabel
    lLoop <- getNextLabel
    lExit <- getNextLabel
    exprCode <- translateBoolExpr expr lLoop lExit
    stmtCode <- translateStmt $ toBlock stmt
    return $ CodeBlock [getLabelCode lBegin, exprCode, getLabelCode lLoop, stmtCode, jmp $ getLabel lBegin,
                        getLabelCode lExit]
translateStmt (For t ident array stmt) = do
    (env, penv, senv, cenv, minSize, prevNextLabel, maxTemp) <- get
    put (env, penv, senv, cenv, minSize, prevNextLabel, maxTemp + 1)
    let tempCnt = Ident $ "$" ++ (show maxTemp)
    res <- translateStmt $ BStmt $ Block [
            Decl Int [NoInit tempCnt], -- Declare temp counter
            While (ERel (EVar tempCnt) LTH (EAttr (AttrAcc array $ Ident "length"))) $ BStmt $ Block [
                    Decl t [Init ident $ EArrElem $ ArrElem array $ EVar tempCnt], -- ident = array[temp]
                    stmt,  -- code
                    Incr $ LValVal tempCnt]] -- temp ++
    (_, _, _, _, _, nextLabel, _) <- get
    put (env, penv, senv, cenv, minSize, nextLabel, maxTemp)
    return res
translateStmt (SExp expr) = translateExpr expr

-- Expressions ---------------------------------------------------------------------------------------------------------

-- Invariant: Every expression ends with pushing the result on the stack
translateExpr :: Expr -> Translation Code
translateExpr (ENullRef t) = return $ CodeBlock [pushl "$0"]
translateExpr (EAttr (AttrAcc lval ident)) = do
    lvalCode <- translateLVal lval
    t <- getLValType lval
    case t of
        (Array _) -> return $ CodeBlock [lvalCode, popl eax, pushl "4(%eax)"]  -- Array length
        _ -> do
            lvalCode <- translateLVal $ LValAttr $ AttrAcc lval ident
            return $ CodeBlock [lvalCode, popl eax, pushl "(%eax)"]
translateExpr (EMethApp (MethApp lval (FnApp ident exprs))) = do
    lvalCode <- translateLVal lval
    (Class cIdent) <- getLValType lval
    (_, _, penv, _, _) <- getClass cIdent
    let (retType, virt, origCls) = penv Map.! ident
    let popPush = if retType /= Void then [popl ebx, popl ebx, pushl eax] else [popl ebx]
    case virt of
        (Just virtId) -> do
            appCode <- getFnAppCode retType (Ident $ "*" ++ (show (4 * virtId)) ++ "(%edx)") exprs
            return $ CodeBlock [lvalCode, popl eax, movl "(%eax)" ebx, movl "(%ebx)" edx, pushl "(%eax)", appCode, CodeBlock popPush]
        Nothing -> do
            appCode <- getFnAppCode retType (Ident $ (unpackIdent origCls) ++ "$" ++ (unpackIdent ident)) exprs
            return $ CodeBlock [lvalCode, popl eax, pushl "(%eax)", appCode, CodeBlock popPush]
    -- If for this class, this method is virtual then call using vptr
    -- otherwise, just call the right method
translateExpr (ENewArr t expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [pushl $ "$" ++ (show $ getSize t), exprCode, call $ Ident "calloc", popl ebx, popl ecx,
                        pushl ebx, pushl eax]
translateExpr (ENew ident) = do
    (_, _, _, _, align) <- getClass ident
    vTable <- hasVTable ident
    let vPtr = if vTable then ("$" ++ getVTableName ident) else "$0"
    return $ CodeBlock [pushl "$4", pushl $ "$" ++ (show align), call $ Ident "calloc", popl ebx, popl ebx,
            movl vPtr "(%eax)", pushl eax]
translateExpr (EArrElem arrElem) = do
    lvalCode <- translateLVal (LValArrAcc arrElem)
    return $ CodeBlock [lvalCode, popl eax, pushl "(%eax)"]
translateExpr (EVar ident) = do
    t <- getVarType ident
    pushVarCode <- translateVar ident 0
    case t of
        (Array _) -> do
            pushSizeCode <- translateVar ident arrayOffset
            return $ CodeBlock [pushSizeCode, pushVarCode]
        _ -> return pushVarCode
translateExpr (ELitInt num) = return $ pushl $ "$" ++ (show num)
translateExpr ELitTrue = return $ pushl "$1"
translateExpr ELitFalse = return $ pushl "$0"
translateExpr (EApp (FnApp ident args)) = do
    retType <- getFnRetType ident
    getFnAppCode retType ident args
translateExpr (EString str) = do
    lStr <- getStringLabel str
    return $ pushl $ "$" ++ lStr
translateExpr (Neg expr) = do
    exprCode <- translateExpr expr
    return $ CodeBlock [exprCode, popl eax, Indent "neg %eax", pushl eax]
translateExpr (EMul expr1 mop expr2) = translateBinaryOp expr1 expr2 (Mul mop)
translateExpr (EAdd expr1 aop expr2) = translateBinaryOp expr1 expr2 (Add aop)
translateExpr (ERel expr1 rop expr2) = translateBinaryOp expr1 expr2 (Rel rop)
translateExpr expr = do
    -- This has to be a boolean expression which result we want to place on the stack.
    lTrue <- getNextLabel
    lFalse <- getNextLabel
    lExit <- getNextLabel
    exprCode <- translateBoolExpr expr lTrue lFalse
    return $ CodeBlock [exprCode, getLabelCode lTrue, pushl "$1", jmp $ getLabel lExit, getLabelCode lFalse, pushl "$0",
                        getLabelCode lExit]

translateVar :: Ident -> Int -> Translation Code
translateVar ident offset = do
    (env, _, penv, _, _, _, _) <- get
    if Map.member ident env then do
        varCode <- getVarCodeOffset ident offset
        return $ pushl varCode
    else translateExpr (EAttr (AttrAcc (LValVal $ Ident "self") ident))

getFnAppCode :: Type -> Ident -> [Expr] -> Translation Code
getFnAppCode retType ident args = do
    exprs <- mapM (translateExpr) args
    argsSize <- getArgsSize args
    let remParams = map (\_ -> popl ebx) [1..argsSize]
    let commonCode = if not $ null args then (CodeBlock [CodeBlock exprs, call ident, CodeBlock remParams])
                else (call ident)
    case retType of
        (Array _) -> return $ CodeBlock [commonCode, pushl edx, pushl eax]
        Void -> return commonCode
        _ -> return $ CodeBlock [commonCode, pushl eax]
    where
    getArgsSize :: [Expr] -> Translation Int
    getArgsSize = foldM (\res arg -> do
        t <- getExprType arg
        return $ res + (case t of
                (Array _) -> 2   -- Arrays are two 4-byte values on the stack
                _ -> 1)) 0

-- Translates a boolean expression
translateBoolExpr :: Expr -> Int -> Int -> Translation Code
translateBoolExpr (ERel expr1 rop expr2) lTrue lFalse = do
    exprCode <- translateExpr (ERel expr1 rop expr2)
    return $ CodeBlock [exprCode, popl eax, testl eax eax,
                        Indent $ "jnz " ++ (getLabel lTrue), jmp $ getLabel lFalse]
translateBoolExpr (EAnd expr1 expr2) lTrue lFalse = do
    lMid <- getNextLabel
    expr1Code <- translateBoolExpr expr1 lMid lFalse
    expr2Code <- translateBoolExpr expr2 lTrue lFalse
    return $ CodeBlock [expr1Code, getLabelCode lMid, expr2Code]
translateBoolExpr (EOr expr1 expr2) lTrue lFalse = do
    lMid <- getNextLabel
    expr1Code <- translateBoolExpr expr1 lTrue lMid
    expr2Code <- translateBoolExpr expr2 lTrue lFalse
    return $ CodeBlock [expr1Code, getLabelCode lMid, expr2Code]
translateBoolExpr (Not expr) lTrue lFalse = translateBoolExpr expr lFalse lTrue
translateBoolExpr expr lTrue lFalse = do
    exprType <- getExprType expr
    case exprType of
        Bool -> do
            exprCode <- translateExpr expr
            return $ CodeBlock [exprCode, popl eax, testl eax eax, Indent $ "jnz " ++ (getLabel lTrue),
                                jmp $ getLabel lFalse]
        _ -> translateBoolExpr (ERel expr GTH (ELitInt 0)) lTrue lFalse

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
    return $ CodeBlock [expr1Code, expr2Code, swapArgs, call concatStrings, popl ebx, popl ebx, pushl eax]

translateMetaOp :: MetaOp -> Translation Code
translateMetaOp (Mul mop) = do
    let divOp = [popl ebx, popl eax, movl eax edx, Indent "sar $31, %edx",
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

-- Left-values ---------------------------------------------------------------------------------------------------------

-- Translates the whole LVal into the code that leaves a pointer to lval on the stack.
translateLVal :: LVal -> Translation Code
-- translateLVal lval | trace ("translateLVal " ++ show lval) False = undefined
translateLVal (LValVal ident) = do
    (env, _, penv, _, _, _, _) <- get
    if Map.member ident env then do
        varCode <- getVarCodeOffset ident 0
        return $ CodeBlock [Indent $ "leal " ++ varCode ++ ", " ++ eax, pushl eax]
    else translateLVal (LValAttr (AttrAcc (LValVal $ Ident "self") ident))
    -- Single ref
translateLVal (LValFunApp fApp) = translateExpr (EApp fApp)
translateLVal (LValArrAcc (ArrElem lval expr)) = do
    lvalCode <- translateLVal lval
    -- dereference pointer and return value
    exprCode <- translateExpr expr
    return $ CodeBlock [lvalCode, exprCode, popl eax, popl ebx, movl "(%ebx)" ecx,
                        Indent $ "leal (%ecx, %eax, 4), " ++ ebx, pushl ebx]    -- Single ref
translateLVal (LValAttr (AttrAcc lval ident)) = do
    (Class cIdent) <- getLValType lval
    lvalCode <- translateLVal lval
    (_, env, _, _, _) <- getClass cIdent
    let varMove = snd $ env Map.! ident
    return $ CodeBlock [lvalCode, popl eax, movl "(%eax)" ebx, Indent $ "leal " ++ show varMove ++ "(%ebx), %eax",
                        pushl eax]
translateLVal _ = undefined -- TODO

-- Declaration/args ----------------------------------------------------------------------------------------------------

-- Binds the args in the environment and returns the total size allocated (in Bytes)
bindArgs :: [Arg] -> Translation Int
bindArgs args = do
    bindArgsHelper 4 (reverse args)
    where
    bindArgsHelper :: Int -> [Arg] -> Translation Int
    bindArgsHelper lastSize ((Arg t ident):rest) = do
        let allocSize = getSize t
        (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
        let addr = lastSize + allocSize - (case t of
                (Array _) -> 4
                _ -> 0)
        put (Map.insert ident (t, addr) env, senv, penv, cenv, minSize, nextLabel, maxTemp)
        bindArgsHelper (lastSize + allocSize) rest
    bindArgsHelper res [] = return res

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
            (For t ident _ stmt) -> do
                (newSize, _) <- allocItems lastSize t [NoInit ident]
                (maxSize, _) <- allocItems newSize Int [NoInit $ Ident "whatever"] -- temp variable
                allocVarsHelper maxSize (stmt:rest)
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
    let ident = getItemIdent item
    (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
    put (Map.insert ident (t, (lastSize - size)) env, senv, penv, cenv, min minSize (lastSize - size), nextLabel,
         maxTemp)
    varCode <- getVarCode ident
    -- if array - store it's size
    code <- case t of
        (Array _) -> do
            sizeCode <- getVarCodeOffset ident arrayOffset
            return [exprCode, popl varCode, popl sizeCode]
        _ -> return [exprCode, popl varCode]
    return $ (lastSize - size, CodeBlock code)

getInitExpr :: Type -> Item -> Translation Expr
getInitExpr t (NoInit ident) = do
    case t of
        Str -> return $ EString ""
        (Array arrT) -> return $ ENewArr arrT $ ELitInt 0
        _ -> return $ ELitInt 0
getInitExpr _ (Init _ expr) = return expr

-- Type arithmetic for the purpose of translation ----------------------------------------------------------------------

getExprType :: Expr -> Translation Type
getExprType (ENullRef t) = return t
getExprType (EAttr attrAcc) = getLValType (LValAttr attrAcc)
getExprType (EMethApp methApp) = getLValType (LValMethApp methApp)
getExprType (ENewArr t _) = return (Array t)
getExprType (ENew ident) = return (Class ident)
getExprType (EArrElem arrElemAcc) = getLValType (LValArrAcc arrElemAcc)
getExprType (EVar ident) = getVarType ident
getExprType (ELitInt _) = return Int
getExprType ELitTrue = return Bool
getExprType ELitFalse = return Bool
getExprType (EApp (FnApp ident _)) = getFnRetType ident
getExprType (EString _) = return Str
getExprType (Neg _) = return Int
getExprType (Not _) = return Bool
getExprType (EMul _ _ _) = return Int -- You can only multiply ints.
getExprType (EAdd a Plus _) = getExprType a -- You can add things of the same type
getExprType (EAdd _ Minus _) = return Int -- You can subtract ints.
getExprType (ERel _ _ _) = return Bool
getExprType (EAnd _ _) = return Bool
getExprType (EOr _ _) = return Bool

getFnRetType :: Ident -> Translation Type
getFnRetType ident = do
    (_, _, penv, _, _, _, _) <- get
    return $ penv Map.! ident

getLValType :: LVal -> Translation Type
getLValType (LValVal ident) = getVarType ident
getLValType (LValFunApp (FnApp ident exprs)) = getFnRetType ident
getLValType (LValMethApp (MethApp lval (FnApp ident _))) = do
    (Class classT) <- getLValType lval
    (_, _, penv, _, _) <- getClass classT
    let (res, _, _) = penv Map.! ident
    return res
getLValType (LValArrAcc (ArrElem lval expr)) = do
    (Array t) <- getLValType lval
    return t
getLValType (LValAttr (AttrAcc lval ident)) = do
    lvalT <- getLValType lval
    case lvalT of
        (Array _) -> return Int -- typechecker has already checked if ident is "length"
        (Class cIdent) -> do
            (_, env, _, _, _) <- getClass cIdent
            return $ fst $ env Map.! ident

-- Env-related utils ---------------------------------------------------------------------------------------------------

fillCEnv :: Program -> Translation ()
fillCEnv (Program topDefs) = do
    let classDefs = map (\classDef -> case classDef of
            (ClassDef ident cdefs) -> (Nothing, ident, cdefs)
            (ClassExtDef ident parentIdent cdefs) -> (Just parentIdent, ident, cdefs)) $
            filter (\td -> case td of
                    (FnDef _) -> False
                    _ -> True) topDefs
    mapM_ (registerClass) classDefs
    (_, _, _, cenv, _, _, _) <- get
    let cdefsEnv = Map.fromList $ map (\(_, ident, cdefs) -> (ident, cdefs)) classDefs
    let cIdents = map (\(_, ident, _) -> ident) classDefs
    let leaves = filter (\ident -> not $ any (\(parent, _, _, _, _) -> parent == (Just ident)) $ Map.elems cenv) cIdents
    mapM_ (\ident -> initClass (Just ident) Set.empty cdefsEnv) leaves

    where
    registerClass :: (Maybe Ident, Ident, [CDef]) -> Translation ()
    registerClass (parentIdent, ident, cdefs) = do
        -- Register class in CEnv
        (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
        put (env, senv, penv, Map.insert ident (parentIdent, Map.empty, Map.empty, -1, 0) cenv, minSize, nextLabel,
             maxTemp)

    -- This function is responsible for setting env properly and initializing virtual method numbers
    initClass :: Maybe Ident -> Set.Set Ident -> Map.Map Ident [CDef] -> Translation (Env, Int)
    -- initClass cls pset _ | trace ("initClass " ++ show cls ++ " pset: " ++ show pset) False = undefined
    initClass (Just ident) pset cdefsEnv = do
        (parent, cEnv, cPEnv, maxVirt, align) <- getClass ident
        if maxVirt > -1 then return (cEnv, align)
        else do
            let cdefs = cdefsEnv Map.! ident
            let vars = filter (\cdef -> case cdef of
                    (Method _) -> False
                    _ -> True) cdefs
            let methods = filter (\cdef -> case cdef of
                    (Method _) -> True
                    _ -> False) cdefs
            -- Sum all the methods below and our methods
            let newPSet = foldl (\acc (Method (FunDef _ ident _ _)) -> Set.insert ident acc) pset $ methods
            -- Get env and last env size of all classes above
            (superEnv, lastSize) <- initClass parent newPSet cdefsEnv
            let (resEnv, resSize) = foldl (\(cEnv, size) (Attr t classItems) -> let tSize = getSize t in
                    foldl (\(newEnv, newSize) (ClassItem ident) ->
                            (Map.insert ident (t, newSize) newEnv, newSize + tSize)) (cEnv, size) classItems)
                    (superEnv, lastSize) vars
            (superPEnv, superMaxVirt) <- case parent of
                (Just parentIdent) -> do
                    (_, _, resPEnv, resMaxVirt, _) <- getClass parentIdent
                    return (resPEnv, resMaxVirt)
                Nothing -> return (Map.empty, 0)
            let (resPEnv, resMaxVirt) = foldl (\(cPEnv, maxVirt) (Method (FunDef t fIdent _ _)) ->
                    case Map.lookup fIdent cPEnv of
                            (Just (_, Nothing, _)) -> (Map.insert fIdent (t, Just maxVirt, ident) cPEnv,
                                                       maxVirt + 1)
                            Nothing -> (Map.insert fIdent (t, Just maxVirt, ident) cPEnv, maxVirt + 1)
                            (Just (_, v, _)) -> (Map.insert fIdent (t, v, ident) cPEnv, maxVirt))
                                    (superPEnv, superMaxVirt) methods
            -- Get parent's PEnv and for every new method look it up. If it exists as non-virtual, make it virtual and
            -- give it new virtIdx; if it exists as virtual, do not readd, if does not exist, add as non-virtual.
            (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
            put (env, senv, penv, Map.insert ident (parent, resEnv, resPEnv, resMaxVirt, resSize) cenv, minSize, nextLabel,
                 maxTemp)
            return (resEnv, resSize)
    initClass Nothing _ _ = return (Map.empty, 4)  -- 4 bytes for vptr

fillPEnv :: Program -> Translation ()
fillPEnv (Program topDefs) = do
    let fns = map (\(FnDef res) -> res) $ filter (\td -> case td of
                (FnDef _) -> True
                _ -> False) topDefs
    mapM_ (registerFunc) fns
    mapM_ (registerFunc) (map (\(t, name, args) -> FunDef t (Ident name) args $ Block [Empty]) builtins)
    where
    registerFunc :: FuncDef -> Translation ()
    registerFunc (FunDef retType ident _ _) = do
        (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
        put (env, senv, Map.insert ident retType penv, cenv, minSize, nextLabel, maxTemp)

getClass :: Ident -> Translation ClsType
getClass ident = do
    (_, _, _, cenv, _, _, _) <- get
    return $ cenv Map.! ident

getNextLabel :: Translation Int
getNextLabel = do
    (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
    put (env, senv, penv, cenv, minSize, nextLabel + 1, maxTemp)
    return nextLabel

getVarCode :: Ident -> Translation String
getVarCode ident = getVarCodeOffset ident 0

getVarCodeOffset :: Ident -> Int -> Translation String
getVarCodeOffset ident offset = do
    origOffset <- getVarIdx ident
    return $ (show $ origOffset + offset) ++ "(%ebp)"

getVarIdx :: Ident -> Translation Int
-- getVarIdx ident | trace ("getVarIdx " ++ show ident) False = undefined
getVarIdx ident = do
    (env, _, _, _, _, _, _) <- get
    return $ snd $ env Map.! ident

getVarType :: Ident -> Translation Type
getVarType ident = do
    (env, _, _, _, _, _, _) <- get
    if Map.member ident env then
        return $ fst $ env Map.! ident
    else getExprType (EAttr (AttrAcc (LValVal (Ident "self")) ident))

hasVTable :: Ident -> Translation Bool
hasVTable cName = do
    (_, _, penv, _, _) <- getClass cName
    return $ not $ null $ filter (\(_, v, _) -> isJust v) $ Map.elems penv

-- Strings / string labels ---------------------------------------------------------------------------------------------

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
    (_, senv, _, _, _, _, _) <- get
    return $ senv Map.! str

registerString :: String -> Int -> Translation ()
registerString str idx = do
    (env, senv, penv, cenv, minSize, nextLabel, maxTemp) <- get
    let sLabel = ".S" ++ (show idx)
    put (env, Map.insert str sLabel senv, penv, cenv, minSize, nextLabel, maxTemp)

-- Utils ---------------------------------------------------------------------------------------------------------------

getItemIdent :: Item -> Ident
getItemIdent (NoInit res) = res
getItemIdent (Init res _) = res

getLabel :: Int -> String
getLabel idx = ".L" ++ (show idx)

getLabelCode :: Int -> Code
getLabelCode idx = NoIndent $ (getLabel idx) ++ ":"

-- Returns the variable size in bytes.
getSize :: Type -> Int
getSize Int = 4
getSize Bool = 4    -- Yes, let's use ints for now for consistency [FIXME]
getSize Str = 4     -- Ptr to actual string
getSize (Array _) = 8  -- Ptr to allocated space + size
getSize (Class _) = 4   -- Ptr to allocated space
getSize _ = 0

getVTableName :: Ident -> String
getVTableName (Ident str) = "." ++ str ++ "vTable"

toBlock :: Stmt -> Stmt
toBlock (BStmt block) = BStmt block
toBlock stmt = BStmt $ Block [stmt]

unpackIdent :: Ident -> String
unpackIdent (Ident str) = str

-- Assembler Code ------------------------------------------------------------------------------------------------------

arrayOffset :: Int
arrayOffset = 4

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

ebp :: String
ebp = "%ebp"

esp :: String
esp = "%esp"

-- Assembler:
call :: Ident -> Code
call (Ident str) = Indent $ "call " ++ str

pushl :: String -> Code
pushl src = Indent $ "pushl " ++ src

popl :: String -> Code
popl src = Indent $ "popl " ++ src

movl :: String -> String -> Code
movl src dst = Indent $ "movl " ++ src ++ ", " ++ dst

testl :: String -> String -> Code
testl src dst = Indent $ "testl " ++ src ++ ", " ++ dst

jmp :: String -> Code
jmp label = Indent $ "jmp " ++ label

swapArgs :: Code
swapArgs = CodeBlock [popl eax, popl ebx, pushl eax, pushl ebx]

-- Misc:
entryProtocol :: Code
entryProtocol = CodeBlock [(Indent "pushl %ebp"), movl esp ebp]

leaveProtocol :: Code
leaveProtocol = CodeBlock [(Indent "leave"), (Indent "ret")]
