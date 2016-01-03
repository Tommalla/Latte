-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for running Translator and TypeChecker and actual underlying OS-related compilation.
module Compiler where

import Data.List
import Data.List.Split

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte
import TypeChecker (typeCheck)
import Translator (translate)

compile :: String -> String -> IO (Maybe String)
compile code inputFile = do
    let tokens = myLexer code
    case pProgram tokens of
        Bad errorStr -> return $ Just ("Error at parsing: " ++ errorStr ++ "\nTokens: " ++ (show tokens))
        Ok program -> case typeCheck program of
            Nothing -> do
                let res = translate program
                let pathSplit = splitOn "/" inputFile
                let className = head $ splitOn "." $ last $ pathSplit
                let path = intercalate "/" $ take (length pathSplit - 1) pathSplit
                let newPath = path ++ (if path == "" then "" else "/") ++ className
                let asmPath = (newPath ++ ".s")
                putStrLn $ "Writing to: " ++ asmPath
                writeFile asmPath res
                -- TODO execute compilation
                return Nothing
            err -> return err

