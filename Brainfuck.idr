import Parser

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
eval ss = case evalProgram (replicate MemorySize fZ) fZ ss of
    (_, _, output) => output
  where
    evalProgram : Memory -> Fin MemorySize -> Program -> (Memory, Fin MemorySize, List Byte)
    evalStmt : Memory -> Fin MemorySize -> Stmt -> (Memory, Fin MemorySize, List Byte)
    
    evalProgram mem ptr [] = (mem, ptr, [])
    evalProgram mem ptr (s::ss) = case evalStmt mem ptr s of
        (mem', ptr', output1) => case evalProgram mem' ptr' ss of
          (mem'', ptr'', output2) => (mem'', ptr'', output1 ++ output2)
          
    evalStmt mem ptr IncData = (update inc ptr mem, ptr, [])
    evalStmt mem ptr DecData = (update dec ptr mem, ptr, [])
    evalStmt mem ptr IncPtr = (mem, inc ptr, [])
    evalStmt mem ptr DecPtr = (mem, dec ptr, [])
    evalStmt mem ptr Print = (mem, ptr, [index ptr mem])
    evalStmt mem ptr (Loop body) = case index ptr mem of
        fZ => (mem, ptr, [])
        fS _ => case evalProgram mem ptr body of
           (mem', ptr', output1) => case evalStmt mem' ptr' (Loop body) of
             (mem'', ptr'', output2) => (mem'', ptr'', output1 ++ output2)

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
