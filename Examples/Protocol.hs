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
infixr ⊸
type Effect = IO () -- for simplicity
-- instance Monoid Effect

-- A linear negation that represents the transfer of control from
-- server to client, and vice-versa.
type N a = a ⊸ Effect

-- | Protocol from the point of view of the client:
data Client where
  Mul :: Double -> Double -> -- ^ input for the request the request
         {-1-}(N (Double ⊗ Server)) -> -- ^ what the server does to respond: it returns a Double, and a new server state. 
         Client
         -- Client sends two 'Double' and
         -- expects a double and a new server
         -- session.
  Terminate :: Client
type Server = N Client


-- The linearity of client/server states ensures that:

-- 1. The protocol is respected. So, the effects that inevitably come
-- into play in a real implementation (database, ...) will never 'get
-- lost' or be duplicated.

-- 2. The implementation won't 'hold onto' stale server/client states
-- any longer than strictly necessary.

-- In sum, linearity comes at the expense of backtracking in the
-- protocol. Arguably this is exactly what one wants in many
-- applications.

exampleClient :: N (N Client)
exampleClient server = server $ Mul 12 34 $ \(product,server') -> do
  print product
  server' Terminate

exampleServer :: Server
exampleServer client = case client of
  Mul x y respond -> respond (x*y,exampleServer)
  Terminate -> return ()


-- See 'StorageServer.hs' for a more realistic server.

type a & b = N (Either (N a) (N b))

if_ :: Bool ⊸ (a & a) ⊸ (a ⊸ Effect) ⊸ Effect
if_ True  p k = p (Left  k)
if_ False p k = p (Right k)
