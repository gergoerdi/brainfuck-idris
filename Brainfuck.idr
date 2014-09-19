import Parser
import Control.Monad.RWS

Program : Type
data Stmt = IncData | DecData | IncPtr | DecPtr | Loop Program | Print
Program = List Stmt

instance Show Stmt where
  show IncData = "+"
  show DecData = "-"
  show IncPtr = ">"
  show DecPtr = "<"
  show Print = "."
  show (Loop p) = "[" ++ concat (map show p) ++ "]"

parseStmt : Parser Stmt
parseStmt = incData <|> decData <|> incPtr <|> decPtr <|> print <|> loop
  where
    incData = token "+" $> pure IncData
    decData = token "-" $> pure DecData
    incPtr = token ">" $> pure IncPtr
    decPtr = token "<" $> pure DecPtr
    print = token "." $> pure Print
    loop = P $ \s => unP [| Loop (between (token "[") (token "]") parseStmt) |] s

parseProgram : Parser Program
parseProgram = many parseStmt

test : Maybe Program
-- test = runParser parseProgram $
--        ">+++++++++[<++++++++>-]" ++
--        "<.>+++++++[<++++>-]<+.+++++++..+++.[-]" ++
--        ">++++++++[<++++>-]<.>+++++++++++[<++++++++>-]<-.--------.+++" ++
--        ".------.--------.[-]>++++++++[<++++>-]<+.[-]++++++++++."
test = runParser parseProgram "++++[.-]"
-- -- test = Just [IncData, Print]

Byte : Type
Byte = Fin 256

MemorySize : Nat
MemorySize = 10

Ptr : Type
Ptr = Fin MemorySize

Memory : Type
Memory = Vect MemorySize Byte

total inc : {n : Nat} -> Fin n -> Fin n
inc {n = Z} x = absurd x
inc {n = (S n)} x = case strengthen x of
    Right x' => fS x'
    Left _ => fZ

total dec : Fin n -> Fin n
dec fZ = last
dec (fS x) = weaken x

total update : (a -> a) -> Fin n -> Vect n a -> Vect n a
update f fZ (x :: xs) = f x :: xs
update f (fS k) (x :: xs) = x :: update f k xs

eval : Program -> List Byte
eval ss = case runIdentity $ runRWST (evalProgram ss) () (replicate MemorySize fZ, fZ) of
    (_, _, output) => output
  where
    Eval : Type -> Type
    Eval = RWS () (List Byte) (Memory, Fin MemorySize)

    getPointed : Eval Byte
    getPointed = do
        (mem, ptr) <- get
        return $ index ptr mem

    modifyPtr : (Fin MemorySize -> Fin MemorySize) -> Eval ()
    modifyPtr f = do
        (mem, ptr) <- get
        put (mem, f ptr)

    modifyPointed : (Byte -> Byte) -> Eval ()
    modifyPointed f = do
        (mem, ptr) <- get
        put (update f ptr mem, ptr)

    evalProgram : Program -> Eval ()
    evalStmt : Stmt -> Eval ()

    evalProgram [] = return ()
    evalProgram (s::ss) = do
        evalStmt s
        evalProgram ss

    evalStmt IncData = do
        modifyPointed inc
    evalStmt DecData = do
        modifyPointed dec
    evalStmt IncPtr = do
        modifyPtr inc
    evalStmt DecPtr = do
        modifyPtr dec
    evalStmt Print = do
        v <- getPointed
        tell $ List.(::) v []
    evalStmt (Loop body) = do
        v <- getPointed
        case v of
          fZ => return ()
          fS _ => do
             evalProgram body
             evalStmt (Loop body)

main : IO ()
main = case test of
     Nothing => putStrLn "Parse error"
     Just p => do
          putStrLn $ concat . map show $ p
          putStrLn $ show . map finToNat $ eval p

-- main : IO ()
-- main = case test of
--      Nothing => putStrLn "Parse error"
--      Just p => 
