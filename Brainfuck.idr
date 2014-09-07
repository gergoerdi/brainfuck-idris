import Parser

Program : Type
data Stmt = IncData | DecData | IncPtr | DecPtr | Loop Program | Print
Program = List Stmt

parseStmt : Parser Stmt
parseStmt = incData <|> decData <|> incPtr <|> decPtr <|> print <|> loop
  where
    incData = token "+" $> pure IncData
    decData = token "-" $> pure DecData
    incPtr = token ">" $> pure IncPtr
    decPtr = token "<" $> pure DecPtr 
    print = token "." $> pure Print
    loop = [| Loop (between (token "[") (token "]") parseStmt) |]

test : Maybe Stmt
test = runParser parseStmt "[+[-]]"

-- Byte : Type
-- Byte = Fin 256

-- MemorySize : Nat
-- MemorySize = 100

-- Ptr : Type
-- Ptr = Fin MemorySize

-- Memory : Type
-- Memory = Vect MemorySize Byte

-- total inc : {n : Nat} -> Fin n -> Fin n
-- inc {n = Z} x = absurd x
-- inc {n = (S n)} x = case strengthen x of
--     Right x' => fS x'
--     Left _ => fZ

-- total dec : Fin n -> Fin n
-- dec fZ = last
-- dec (fS x) = weaken x

-- total update : (a -> a) -> Fin n -> Vect n a -> Vect n a
-- update f fZ (x :: xs) = f x :: xs
-- update f (fS k) (x :: xs) = x :: update f k xs

-- eval : Program -> List Byte
-- eval = go (replicate MemorySize fZ) fZ
--   where
--     go : Memory -> Fin 100 -> Program -> List Byte
--     go mem ptr [] = []
--     go mem ptr (IncData::ss) = go (update inc ptr mem) ptr ss 
--     go mem ptr (DecData::ss) = go (update dec ptr mem) ptr ss
--     go mem ptr (IncPtr::ss) = go mem (inc ptr) ss
--     go mem ptr (DecPtr::ss) = go mem (dec ptr) ss
--     go mem ptr ((Loop body)::ss) = case index ptr mem of
--       fZ => go mem ptr ss
--       fS _ => go mem ptr body ++ go mem ptr ((Loop body) :: ss)
--     go mem ptr (Print::ss) = index ptr mem :: go mem ptr ss

