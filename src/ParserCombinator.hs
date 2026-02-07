-- reminding myself how parser combinators work
module ParserCombinator where

import Prelude hiding ( sequence )
import Data.List
import Data.Char
import Data.Maybe (fromMaybe)
import Control.Monad.Except

newtype Parser a = Parser {unParser :: String -> Either String (a, String)}

fullParse :: Show a => Parser a -> String -> Either String a
fullParse x s =
  case unParser x s of
    Right (v,"") -> Right v
    Right (v,remaining) -> Left $ "incomplete parse:\n" <>
      show v <> "\n\nremaining:\n" <> show (take 200 remaining)
    Left e -> Left e

assertParse x s =
  case fullParse x s of
    Right v -> v
    Left e -> error e

instance Functor Parser where
  fmap f p = Parser $ \s -> do
    (a, b) <- unParser p s
    pure (f a, b )

instance Applicative Parser where
  pure x = Parser $ \s -> Right (x, s)
  liftA2 f p q = Parser $ \s -> do
    (a, s') <- unParser p s
    (b, s'') <- unParser q s'
    pure (f a b, s'')

instance Monad Parser where
  p >>= f = Parser $ \s -> do
    (a, s') <- unParser p s
    (b, s'') <- unParser (f a) s'
    pure (b, s'')

instance MonadError String Parser where
  throwError msg = Parser (\_ -> throwError msg)
  -- ?
  catchError m f = Parser $ \s ->
    case unParser m s of
      Left e -> unParser (f e) s
      Right v -> Right v

instance Semigroup a => Semigroup (Parser a) where
  (<>) = liftA2 (<>)

alt :: Parser a -> Parser a -> Parser a
alt a b = Parser $ \s ->
  case unParser a s of
    Left _ -> unParser b s
    ps -> ps

(<|>) = alt

none :: Parser [a]
none = pure []

many :: Parser a -> Parser [a]
many p = ((singleton <$> p) <> many p) <|> none

many1 :: Parser a -> Parser [a]
many1 p = (singleton <$> p) <> many p

charMatch :: String -> (Char -> Bool) -> Parser Char
charMatch s f = Parser charMatch'
  where
    charMatch' (x : xs) | f x = pure (x, xs)
    charMatch' _ = throwError $ "[expected: '" <> s <> "']"

char :: Char -> Parser Char
char c = charMatch [c] (== c)

lower = charMatch "lower case character" isLower
upper = charMatch "upper case character" isUpper
alphaNum = charMatch "alphanumeric" isAlphaNum
digit = charMatch "alphanumeric" isDigit
idChar = charMatch "alpha num -/_'" isIdChar
  where
    isIdChar c = case c of
      '-' -> True; '/' -> True; '_' -> True; '\'' -> True;
      _ -> isAlphaNum c

nat :: Parser Int
nat = do
  ds <- many1 digit
  case (reads ds :: [(Int, String)]) of
    [(i,"")] -> pure i
    _ -> throwError "expected natural number"

sequence :: [Parser a] -> Parser [a]
sequence [] = none
sequence (p : ps) = do
  x <- p
  xs <- sequence ps
  pure (x : xs)

both :: Parser a -> Parser b -> Parser (a,b)
both = liftA2 (,)

string :: String -> Parser String
string = sequence . map char

sepBy :: Parser a -> Parser b -> Parser [b]
sepBy sep p = ((singleton <$> p) <> many (sep *> p)) <|> none

sepBy1 :: Parser a -> Parser b -> Parser [b]
sepBy1 sep p = (singleton <$> p) <> many (sep *> p)

optional :: Parser a -> Parser (Maybe a)
optional p = (Just <$> p) <|> pure Nothing

optional' :: a -> Parser a -> Parser a
optional' a p = fromMaybe a <$> (optional p)

sepByTrailing :: Parser a -> Parser b -> Parser [b]
sepByTrailing sep p = ((singleton <$> p) <> many (sep *> p) <* optional sep) <|> none

-- todo
isws ' ' = True
isws '\n' = True
isws '\t' = True
isws _ = False

ws = many $ charMatch "whitespace" isws
ws1 = many1 (charMatch "whitespace" isws)

commaSep = sepBy (char ',' *> ws)
commaSep1 = sepBy1 (char ',' *> ws)
commaSep' = sepByTrailing (char ',' *> ws)
commaSep1' x = let sep = (char ',' *> ws) in (sepBy1 sep x <* optional sep)
wsSep = sepBy ws1
sep2 sep p q = both p (ws *> sep *> ws *> q)
dotTerm p = many (ws *> p <* ws <* char '.') <* ws

brackets x = char '[' *> ws *> x <* ws <* char ']'
bbrackets x = string "[[" *> ws *> x <* ws <* string "]]"
braces x = char '{' *> ws *> x <* ws <* char '}'
parens x = char '(' *> ws *> x <* ws <* char ')'
pipes x = char '|' *> ws *> x <* ws <* char '|'

single :: Parser a -> Parser [a]
single = (singleton <$>)

-- Language Parsers
identifier = (singleton <$> idChar) <> many idChar
predicate = (singleton <$> (lower <|> char '#')) <> many idChar
--predicate = (singleton <$> lower) <> many idChar
variable =
  (single upper <> many idChar) <|>
  (single (char '_') <> many1 idChar)

stringLit = char '"' *> many (charMatch "string char" (/= '"')) <* char '"'

lexComments comment = unlines . map strip . lines
  where
    strip [] = []
    strip s@(c : cs) =
      if isPrefixOf comment s then [] else c : strip cs
