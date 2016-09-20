-- This example is inspired from Lindley and Morris, "embedding
-- session types in Haskell".

-- It demonstrates how to encode protocols using linear types, in the
-- flavour that we propose.

{-# LANGUAGE TypeOperators, GADTs #-}
module Calculator where
import Data.Monoid

-- Broken man's linear types.
type a ⊗ b = (a,b)
type a ⊸ b = a -> b

type Effect = IO () -- for simplicity
-- instance Monoid Effect

pr :: Double -> Effect -- "prints" a number
pr = print

type N a = a ⊸ Effect

data Client where
  Mul :: Double -> Double -> (N (Double ⊗ Server)) -> Client
         -- Client sends two 'Double' and
         -- expects a double and a new server
         -- session.
  Terminate :: Client
type Server = N Client


exampleClient :: N (N Client)
exampleClient server = server $ Mul 12 34 $ \(product,server') ->
  print product <> server' Terminate

exampleServer :: Server
exampleServer client = case client of
  Mul x y k -> k (x*y,exampleServer)
  Terminate -> return ()

