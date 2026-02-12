module Derp.Parse where

import Prelude hiding (pred, lex)
import Data.Maybe

import Basic
import ParserCombinator
import qualified Derp.Core as T

lex = lexComments ";"
parse = lex .> assertParse prog

term :: Parser T.Term
term = app <|> v <|> p <|> b <|> n <|> str
  where
    v = T.TermVar <$> variable
    p = T.TermPred <$> predicate
    b = pure T.TermBlank <* char '_'
    n = T.TermNum <$> nat
    app = T.TermApp <$> predicate <*> parens (commaSep term)
    str = T.TermString <$> stringLit

tuple :: Parser T.Tuple
tuple = (wsSep term)

expr = T.simplify <$> T.joins' <$> commaSep leaf
  where
    leaf = neg <|> bind <|> tup
    tup = T.atom <$> wsSep term
    bind = T.Bind <$> term <*> ((ws *> char '=' *> ws) *> term)
    neg = T.NegAtom <$> (char '!' *> wsSep term)

rule = do
  body <- expr
  _ <- ws *> string "--" *> (many (char '-')) *> ws
  hs <- commaSep tuple
  pure $ T.Rule (T.Closure mempty body) hs

prog = dotTerm rule
