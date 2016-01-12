-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for running Translator and TypeChecker and actual underlying OS-related compilation.
module Compiler where

import Data.List
import Data.List.Split
import System.IO
import System.Process

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte
import TypeChecker (typeCheck)
import Translator (translate)

compile :: String -> String -> IO (Maybe String)
compile code inputFile = do
    putStrLn "Parsing code..."
    let tokens = myLexer code
    putStrLn "Running type check..."
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
                let compileCmd = "g++ -m32 lib/runtime.o " ++ asmPath ++ " -o " ++ newPath
                hPutStrLn stderr "OK"
                putStrLn $ "Writing to: " ++ asmPath
                writeFile asmPath res
                putStrLn $ "Running compiler:\n\t" ++ compileCmd
                system $ compileCmd
                putStrLn "Done."
                return Nothing
            err -> return err

