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
var = v
  where
    v = T.NegVar <$> variable
    --cv = T.CVar <$> (char '?' *> variable)

term :: Parser T.Term
term = cv <|> fv <|> v <|> p <|> rand <|> b
  where
    v = T.TermVar <$> var
    p = T.TermPred <$> pred
    fv = T.TermFreshVar <$> (char '!' *> var)
    cv = T.TermChoiceVar Nothing <$> (char '?' *> var)
    rand = pure (T.TermExt "$") <* char '$'
    b = pure T.TermBlank <* char '_'

pattern_ :: Parser T.Pattern
pattern_ = q <|> a
  where
    q = T.Pattern T.AtomNeg T.PVar0 <$> (char '?' *> wsSep term)
    a = T.Pattern T.AtomPos T.PVar0 <$> (char '!' *> wsSep term)

expr1 :: Parser T.E
expr1 = at <|> p <|> af <|> vr
  where
    at = T.Atom <$> pattern_
    p = parens $ expr
    af = T.After <$> (char '>' *> ws *> expr1)
    vr = T.EVar <$> term
expr2 :: Parser T.E
expr2 = and_ <|> seq_ <|> at <|> expr1
  where
    and_ = uncurry T.And <$> sep2 (char ',') expr1 expr2
    seq_ = uncurry T.Seq <$> sep2 (char ';') expr1 expr2
    at = uncurry T.At <$> sep2 (char '@') expr1 expr2
expr3 :: Parser T.E
expr3 = over <|> same <|> expr2
  where
    over = uncurry T.Over <$> sep2 (char '/') expr2 expr3
    same = (uncurry T.Same <$> sep2 (char '~') expr2 expr3)
expr4 :: Parser T.E
expr4 = par <|> expr3
  where
    par = uncurry T.Par <$> sep2 (char '|') expr3 expr4

expr = expr4

pragma = count
  where
    count = char '#' *> (pred)

program = dotTerm ((T.Pragma <$> pragma) <|> (T.Rule <$> expr))
