module TestConcatParse where

import Control.Monad ( foldM )
import Compile
import ConcatParse

expected =
  [ Pair (Pair (Pair (Atom "a" 0 [] [Var (GenVar "X1")]) (Atom "a:b" 0 [Var (GenVar "X1")] [Var (GenVar "X2")])) (Atom "b:c" 0 [Var (GenVar "X2")] [Var (GenVar "X3")])) (Atom "c" 0 [Var (GenVar "X3")] [])
  , Pair (Atom "a" 0 [] [Var (GenVar "X2")]) (Pair (Atom "a:b" 0 [Var (GenVar "X2")] [Var (GenVar "X1")]) (Atom "b" 0 [Var (GenVar "X1")] []))
  , Pair (Pair (Atom "p" 0 [] [Var (IVar "I")]) (Atom "q" 0 [Var (IVar "I")] [])) (Atom "r" 0 [] [Var (IVar "I")])
  , Pair (Atom "cat" 0 [] [Var (IVar "X")]) (Atom "black" 0 [Var (IVar "X")] [])
  , Pair (Pair (Atom "cat" 0 [] [Var (IVar "X")]) (Atom "black" 0 [Var (IVar "X")] [])) (Atom "long" 0 [Var (IVar "X")] [])
  , Pair (Pair (Atom "a" 0 [Var (GenVar "X3")] []) (Atom "b" 0 [Var (GenVar "X3")] [])) (Atom "c" 0 [Var (GenVar "X3")] [])
  , Pair (Atom "a" 0 [] [Var (GenVar "X3")]) (Pair (Atom "b" 0 [] [Var (GenVar "X3")]) (Atom "c" 0 [Var (GenVar "X3")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X3")]) (Pair (Atom "b" 0 [Var (GenVar "X3")] []) (Atom "c" 0 [Var (GenVar "X3")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X3")]) (Pair (Atom ":b" 0 [] [Var (GenVar "X3"),Var (IVar "B")]) (Atom "c" 0 [Var (GenVar "X3")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X4")]) (Pair (Pair (Atom ":b" 0 [] [Var (GenVar "X4"),Var (IVar "B")]) (Atom ":c" 0 [Var (GenVar "X4")] [Var (GenVar "X3")])) (Atom "c" 0 [Var (GenVar "X3")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X4")]) (Pair (Pair (Atom ":b" 0 [] [Var (GenVar "X4"),Var (IVar "B")]) (Atom ":c" 0 [Var (GenVar "X4")] [Var (GenVar "X3")])) (Atom "c" 0 [Var (GenVar "X3")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X5")]) (Pair (Pair (Pair (Atom ":b" 0 [] [Var (GenVar "X5"),Var (GenVar "X1")]) (Atom "b" 0 [Var (GenVar "X1")] [])) (Atom ":c" 0 [Var (GenVar "X5")] [Var (GenVar "X4")])) (Atom "c" 0 [Var (GenVar "X4")] []))
  , Pair (Atom "a" 0 [] [Var (GenVar "X6")]) (Pair (Pair (Pair (Pair (Pair (Pair (Pair (Pair (Atom ":b" 0 [] [Var (GenVar "X6"),Var (IVar "B")]) (Atom ":c" 0 [Var (GenVar "X6")] [Var (GenVar "X3")])) (Atom "c" 0 [Var (GenVar "X3")] [])) (Term Over')) (Atom "d" 0 [] [Var (GenVar "X4")])) (Atom "d" 0 [Var (GenVar "X4")] [])) (Term Over')) (Atom "e" 0 [] [Var (GenVar "X5")])) (Atom "e" 0 [Var (GenVar "X5")] []))
  , Pair (Atom "q" 0 [] [Var (GenVar "X2")]) (Pair (Atom "p" 0 [] [Var (GenVar "X1")]) (Atom "p:q" 0 [Var (GenVar "X2"),Var (GenVar "X1")] []))
  , Pair (Atom "f" 0 [] [Var (GenVar "X1")]) (Atom "a:sum:b" 0 [Var (GenVar "X1"),Var (IVar "A")] [Var (IVar "B")])
  , Pair (Pair (Pair (Atom "the" 0 [] [Var (GenVar "X6"),Var (GenVar "X5")]) (Pair (Pair (Atom "long" 0 [] [Var (GenVar "X5")]) (Atom "black" 0 [Var (GenVar "X5")] [])) (Atom "cat" 0 [Var (GenVar "X5")] []))) (Atom "is" 0 [Var (GenVar "X6")] [Var (GenVar "X7")])) (Atom "at" 0 [Var (GenVar "X7")] [Var (IVar "X")])
  , Pair (Atom "p" 0 [Var (IVar "P")] []) (Atom "it:range" 0 [Var (IVar "It")] [Var (IVar "R")])
  , Atom "p:q" 0 [Var (IVar "Q"),Var (IVar "P")] []
  ]

testConcatParse = do
    i <- foldM check 0 (zip expected tests')
    putStrLn $ "passing: " <> show i
  where
    check :: Int -> (ConcatParse.Word Mark, String) -> IO Int
    check acc (a,b) =
      if alphaEquiv a (head (tfx' b))
         then pure $ acc+1
         else do
           putStrLn $ "bad parse: " <> b
           pure acc
