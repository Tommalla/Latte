-- Tomasz Zakrzewski, tz336079, 2015
-- This is the module with common code used by different modules.
module Common where

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

builtins :: [(Type, String, [Arg])]
builtins = [(Void, "printInt", [Arg Int $ Ident ""]),
            (Void, "printString", [Arg Str $ Ident ""]),
            (Void, "error", []),
            (Int, "readInt", []),
            (Str, "readString", [])]

isNumeric :: Type -> Bool
isNumeric Int = True
isNumeric _ = False

isBoolConvertible :: Type -> Bool
isBoolConvertible Bool = True
isBoolConvertible t = isNumeric t

isString :: Type -> Bool
isString Str = True
isString _ = False