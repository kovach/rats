module ParseDerp where

import Prelude hiding (pred)
import Data.Maybe

import ParserCombinator
import qualified Derp as T

term :: Parser T.Term
term = app <|> v <|> p <|> b <|> n
  where
    v = T.TermVar <$> variable
    p = T.TermPred <$> predicate
    b = pure T.TermBlank <* char '_'
    n = T.TermNum <$> nat
    app = T.TermApp <$> predicate <*> parens (commaSep term)

tuple :: Parser T.Tuple
tuple = (wsSep term)

expr = T.joins' <$> commaSep leaf
  where
    leaf = bind <|> tup
    tup = T.leaf <$> wsSep term
    bind = T.Bind <$> variable <*> ((ws *> char '=' *> ws) *> term)

rule = do
  body <- expr
  _ <- ws *> string "--" *> (many (char '-')) *> ws
  hs <- commaSep tuple
  pure $ T.Rule (T.ce body) hs

prog = dotTerm rule
