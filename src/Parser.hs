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
term = fv <|> v <|> p <|> rand
  where
    v = (T.TermVar <$> var)
    p = (T.TermPred <$> pred)
    fv = T.TermFreshVar <$> (char '!' *> variable)
    rand = pure (T.TermExt "$") <* char '$'

pattern :: Parser T.Pattern
pattern = q <|> a
  where
    q = T.Pattern T.AtomDuring <$> (char '?' *> wsSep term)
    a = T.Pattern T.AtomPos <$> (char '!' *> wsSep term)
    --af = T.Pattern T.AtomAfter <$> (char '>' *> wsSep term)

expr1 :: Parser T.E
expr1 = at <|> p <|> af
  where
    at = T.Atom <$> pattern
    p = parens $ expr
    af = T.After <$> (char '>' *> ws *> expr1)
expr2 :: Parser T.E
expr2 = ands <|> seqs <|> pars <|> expr1
  where
    ands =
      (uncurry T.And <$> sep2 (char ',') expr1 expr2)
      <|> (uncurry T.And <$> sep2 (char ',') expr1 ands)
    seqs =
      (uncurry T.Seq <$> sep2 (char ';') expr1 expr2)
      <|> (uncurry T.Seq <$> sep2 (char ';') expr1 seqs)
    pars =
      (uncurry T.Par <$> sep2 (char '|') expr1 expr2)
      <|> (uncurry T.Par <$> sep2 (char '|') expr1 pars)
expr3 :: Parser T.E
expr3 = over <|> same <|> expr2
  where
    over = uncurry T.Over <$> sep2 (char '/') expr2 expr3
    same = uncurry T.Over <$> sep2 (char '~') expr2 expr3

expr = expr3

pragma = count
  where
    count = char '#' *> (pred)

program = many (ws *> (T.Pragma <$> pragma) <|> (T.Rule <$> expr) <* ws <* char '.') <* ws
