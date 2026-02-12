module Parser where

import Prelude hiding (pred, lex)
import Data.Maybe

import Basic
import ParserCombinator
import qualified Types as T

lex = lexComments "--" .> lines .> takeWhile (/= "exit") .> unlines
parse = lex .> assertParse program

pred :: Parser T.Pred
pred = p
  where
    p = T.Pred <$> predicate

var :: Parser T.Var
var = v
  where
    v = T.NegVar <$> variable

term :: Parser T.Term
term = cv <|> fv <|> v <|> p <|> rand <|> b <|> n
  where
    v = T.TermVar <$> var
    p = T.TermPred <$> pred
    fv = T.TermFreshVar <$> (char '!' *> var)
    cv = T.TermChoiceVar Nothing <$> (char '?' *> var)
    rand = pure (T.TermExt "$") <* char '$'
    b = pure T.TermBlank <* char '_'
    n = T.TermNum <$> nat

pattern_ :: Parser T.Pattern
pattern_ = q <|> a <|> k
  where
    q = T.Pattern T.AtomNeg T.PVar0 <$> (char '?' *> wsSep term)
    a = T.Pattern T.AtomPos T.PVar0 <$> (char '!' *> wsSep term)
    k = T.Pattern T.AtomAsk T.PVar0 <$> (char '∃' *> wsSep term)

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
expr3 = over <|> under <|> same <|> expr2
  where
    over = uncurry T.Over <$> sep2 (char '/') expr2 expr3
    under = uncurry T.Under <$> sep2 (char '\\') expr2 expr3
    same = (uncurry T.Same <$> sep2 (char '~') expr2 expr3)
expr4 :: Parser T.E
expr4 = par <|> expr3
  where
    par = uncurry T.Par <$> sep2 (char '|') expr3 expr4

expr = expr4

pragma = count
  where
    count = char '#' *> (pred)

program = dotTerm (pr <|> rl)
  where
    pr = T.Pragma <$> pragma
    rl = T.RuleStatement <$> optional (ws *> identifier <* char ':' <* ws) <*> expr
