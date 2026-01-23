module Parser where

import Prelude hiding (pred)
import Data.Maybe

import ParserCombinator
import qualified Types as T

pred :: Parser T.Pred
pred = p
  where
    p = T.Pred <$> predicate

var :: Parser T.Var
var = b <|> v <|> cv
  where
    b = pure T.Blank <* char '_'
    v = T.Var <$> variable
    cv = T.CVar <$> (char '?' *> variable)

term :: Parser T.Term
term = v <|> p
  where
    v = (T.TermVar <$> var)
    p = (T.TermPred <$> pred)
    --af = T.TermAfter . T.TermPred <$> (char '>' *> pred)

pattern :: Parser T.Pattern
pattern = q <|> a <|> af
  where
    q = T.Pattern T.AtomDuring <$> (char '?' *> wsSep term)
    a = T.Pattern T.AtomPos <$> (char '!' *> wsSep term)
    af = T.Pattern T.AtomAfter <$> (char '>' *> wsSep term)

expr1 :: Parser T.E
expr1 = at <|> p
  where
    at = T.Atom <$> pattern
    p = parens $ expr2
expr2 :: Parser T.E
expr2 = ands <|> seqs <|> par <|> expr1
  where
    ands =
      (uncurry T.And <$> sep2 (char ',') expr1 expr2)
      <|> (uncurry T.And <$> sep2 (char ',') expr1 ands)
    seqs =
      (uncurry T.Seq <$> sep2 (char ';') expr1 expr2)
      <|> (uncurry T.Seq <$> sep2 (char ';') expr1 seqs)
    par = uncurry T.Par <$> sep2 (char '|') expr1 expr2
expr3 :: Parser T.E
expr3 = over <|> expr2
  where
    over = uncurry T.Over <$> sep2 (char '/') expr2 expr3

expr = expr3

program = many (ws *> expr <* ws <* char '.') <* ws
