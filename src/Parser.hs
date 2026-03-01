module Parser where

import Prelude hiding (pred, lex)
import Data.Maybe
import Data.List (isPrefixOf)

import Basic
import ParserCombinator
import qualified Types as T

lex = lexComments "--" .> lines .> takeWhile (not . isPrefixOf "exit") .> unlines
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
term = app <|> cv <|> fv <|> v <|> p <|> rand <|> b <|> n
  where
    v = T.TermVar <$> var
    p = T.TermPred <$> pred
    fv = T.TermFreshVar <$> (char '!' *> var)
    cv = T.TermChoiceVar Nothing <$> (char '?' *> var)
    rand = pure (T.TermExt "$") <* char '$'
    b = pure T.TermBlank <* char '_'
    n = T.TermNum <$> nat
    app = T.TermApp <$> predicate <*> parens (commaSep term)

mvar :: (T.Name -> T.Var) -> Parser T.PVar
mvar ty = do
  mv <- optional $ brackets $ ty <$> variable
  pure $ T.PVar mv Nothing

pattern_ :: Parser T.Pattern
pattern_ = q <|> a
  where
    q = char '?' *> ws *> (T.Pattern T.AtomNeg <$> mvar T.NegVar <*> (wsSep term))
    a = char '!' *> ws *> (T.Pattern T.AtomPos <$> mvar T.PosVar <*> (wsSep term))
    -- k = T.Pattern T.AtomAsk T.NoVars <$> (char '∃' *> wsSep term)

-- e2 -> e2 ~> e1
-- e2 -> e1
-- e1 -> atom | parens e5
-- e2 -> e1 e'
-- e' -> . | ~> e1 e'
expr1 :: Parser T.E
expr1 = at <|> p <|> af <|> vr
  where
    at = T.Atom <$> pattern_
    p = parens $ expr
    af = T.After <$> (char '#' *> ws *> expr1)
    vr = T.EVar <$> term
expr2 :: Parser T.E
expr2 = attr'
  where
    --attr = uncurry T.SameIsh <$> sep2 (string "->") expr2 expr1
    attr' = do
      e1 <- expr1
      ops <- many (ws *> string "~>" *> ws *> expr1)
      pure $ foldl T.SameIsh e1 ops
expr3 :: Parser T.E
expr3 = and_ <|> seq_ <|> at <|> expr2
  where
    and_ = uncurry T.And <$> sep2 (char ',') expr2 expr3
    seq_ = uncurry T.Seq <$> sep2 (char ';') expr2 expr3
    at = uncurry T.At <$> sep2 (char '@') expr2 expr3
expr4 :: Parser T.E
expr4 = over <|> under <|> same <|> expr3
  where
    over = uncurry T.Over <$> sep2 (char '/') expr3 expr4
    under = uncurry T.Under <$> sep2 (char '\\') expr3 expr4
    same = (uncurry T.Same <$> sep2 (char '~') expr3 expr4) -- TODO make binding higher (expr1?). maybe introduce second form for low precedence
expr5 :: Parser T.E
expr5 = par <|> expr4
  where
    par = uncurry T.Par <$> sep2 (char '|') expr4 expr5

expr = expr5

pragma = count
  where
    count = char '#' *> (pred)

program = dotTerm (pr <|> rl)
  where
    pr = T.Pragma <$> pragma
    rl = T.RuleStatement <$> optional (ws *> identifier <* char ':' <* ws) <*> expr
