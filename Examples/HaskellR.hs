-- This module demonstrates how to interface with an external library,
-- such as R.

module HaskellR where


-- The R API is not re-entrant, so we will use an R-Context, which is unique:
type RContext
-- The above type is abstract and has no runtime representation in Haskell (it has one in R)


-- An R operation will need an instance of this context, do work (in
-- IO), and finally return release the context and return a result:
type R a = RContext ⊸ IO (RContext ⊗ a)

-- This type has a unit and a bind. (No need for linearity here, we
-- can reuse the standard Monad class)

instance Monad R where
  return x = \ctx -> return (ctx, x)
  k >>= f = \ctx -> do
    (ctx,x) <- k
    f x ctx


-- If we were too add a primitive allowing to run an arbitrary R
-- operation, then we may endup with several contexts (if we combine
-- it with forkIO)

-- withR :: R a ⊸ IO a -- wrong


-- so make sure that we call this operation once only:
withR ::1 R a ⊸ IO a

-- alternatively, we could provide a single context and a way to discard it:
rContext ::1 RContext
doneWithR :: RContext ⊸ () -- not necessarily unique


-- Note that the idea generalises to arbitrary 'single contexts' APIs:
type S ctx a = ctx ⊸ (ctx ⊗ a)

-- and we could even define
type IO = S #RealWorld
