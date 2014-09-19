module Parser

data Parser : Type -> Type where
     P : (String -> List (a, String)) -> Parser a

unP : Parser a -> String -> List (a, String)
unP (P f) = f

total stripPrefix : (Eq a) => List a -> List a -> Maybe (List a)
stripPrefix [] ys = Just ys
stripPrefix (x::xs) (y::ys) = if (x == y) then stripPrefix xs ys else Nothing
stripPrefix _ _  = Nothing

total token : String -> Parser ()
token tk = P $ \s => case stripPrefix (unpack tk) (unpack s) of
      Just s' => [((), pack s')]
      Nothing => []
      
total skip : Parser ()
skip = P $ \s => case unpack s of
     [] => []
     (_::s') => [((), pack s')]

instance Functor Parser where
  map f p = P $ \s => map (\(x, s') => (f x, s')) (unP p s)

instance Applicative Parser where
  pure x = P $ \s => [(x, s)]
  (P pf) <$> (P px) = P $ \s => concat (map (\(f, s') => map (\(x, s'') => (f x, s'')) (px s')) (pf s))

instance Alternative Parser where
  empty = P $ \s => []
  (P p1) <|> (P p2) = P $ \s => p1 s ++ p2 s

orElse : Parser a -> Lazy (Parser a) -> Parser a
orElse p1 p2 = P $ \s => case unP p1 s of
   [] => unP p2 s
   results => results

-- instance Monad Parser where
--   px >>= f = Parse $ \s => concat (map (\(x, s') => unP (f x) s') (unP px s))

total runParser : Parser a -> String -> Maybe a
runParser (P p) s = case p s of
  [(x, "")] => Just x
  _         => Nothing

between : Parser () -> Parser () -> Parser a -> Parser (List a)
between open close body = open $> loop
  where
    loop = P $ \s => case unP close s of
      [] => unP [| body :: loop |] s
      rs => map (\(_, s') => ([], s')) rs

many : Parser a -> Parser (List a)
many p = P $ \s => case unP p s of
     [] => [([], s)]
     xs => unP [| p :: many p |] s
