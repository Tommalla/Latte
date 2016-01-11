-- Tomasz Zakrzewski, tz336079, 2015
-- This is the module with common code used by different modules.
module Common where

import AbsLatte
import ErrM
import LexLatte
import ParLatte
import PrintLatte

isNumeric :: Type -> Bool
isNumeric Int = True
isNumeric _ = False

isBoolConvertible :: Type -> Bool
isBoolConvertible Bool = True
isBoolConvertible t = isNumeric t

isString :: Type -> Bool
isString Str = True
isString _ = False