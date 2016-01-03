-- Tomasz Zakrzewski, tz336079, 2015
-- This module is responsible for translating the program to assembly code.
module Translator where

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

data Code = NoIndent String | Indent String

instance Show Code where
    show (NoIndent str) = str
    show (Indent str) = "  " ++ str

translate :: Program -> String
translate = show . translateProgram 

translateProgram :: Program -> Code
translateProgram (Program topDefs) = Indent "TODO"