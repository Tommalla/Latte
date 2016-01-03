-- Tomasz Zakrzewski, tz336079, 2015
import System.Environment (getArgs)
import System.IO

import Compiler (compile)

main :: IO ()
main = do 
    inputFiles <- getArgs
    case inputFiles of
        [inputFile] -> do
            code <- readFile inputFile
            compileRes <- compile code inputFile
            case compileRes of
                Just err -> putStrLn err
                Nothing -> return ()