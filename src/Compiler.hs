-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for running Translator and TypeChecker and actual underlying OS-related compilation.
module Compiler where

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte
import TypeChecker (typeCheck)

compile :: String -> Maybe String
compile code = do
    let tokens = myLexer code
    case pProgram tokens of
        Bad errorStr -> Just ("Error at parsing: " ++ errorStr ++ "\nTokens: " ++ (show tokens))
        Ok program -> typeCheck program