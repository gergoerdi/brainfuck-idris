data Parser : Type -> Type where
     Parse : (String -> List (a, String)) -> Parser a

unParser : Parser a -> String -> List (a, String)
unParser (Parse f) s = f s

total stripPrefix : (Eq a) => List a -> List a -> Maybe (List a)
stripPrefix [] ys = Just ys
stripPrefix (x::xs) (y::ys) = if (x == y) then stripPrefix xs ys else Nothing
stripPrefix _ _  = Nothing

total token : String -> Parser ()
token tk = Parse $ \s => case stripPrefix (unpack tk) (unpack s) of
      Just s' => [((), pack s')]
      Nothing => []
      
total skip : Parser ()
skip = Parse $ \s => case unpack s of
     [] => []
     (_::s') => [((), pack s')]

instance Functor Parser where
  map f p = Parse $ \s => map (\(x, s') => (f x, s')) (unParser p s)

instance Applicative Parser where
  pure x = Parse $ \s => [(x, s)]
  pf <$> px = Parse $ \s => concat (map (\(f, s') => map (\(x, s'') => (f x, s'')) (unParser px s')) (unParser pf s))

instance Alternative Parser where
  empty = Parse $ \s => []
  p1 <|> p2 = Parse $ \s => unParser p1 s ++ unParser p2 s

instance Monad Parser where
  px >>= f = Parse $ \s => concat (map (\(x, s') => unParser (f x) s') (unParser px s))

total runParser : Parser a -> String -> Maybe a
runParser p s = case unParser p s of
  [(x, "")] => Just x
  _         => Nothing

between : Parser () -> Parser () -> Parser a -> Parser (List a)
between open close body = open $> loop
  where
    loop = (close $> pure []) <|> [| body :: loop |]
