-- This module shows how to use a specialised negation in order to run
-- some linearly-encoded protocol over the network

-- In polarized linear logic, the traditional computational
-- interpretation of the negation of a positive type A is a
-- computation which accepts an A.

type N a = a ⊸ Computation

-- This interpretation can be extended naturally with a location
-- information.  That is, we also say that it must execute remotely:

type N a = a ⊸ (Location ⊗ Computation)

-- Making this a little more concrete, in current Haskell, the
-- location might be a cloud haskell NodeId, and the computation should probably be a distributed closure:

type N a = a ⊸ (NodeId ⊗ Closure Computation)

-- In a real system this would be more complex. For example if we want
-- load-balancing we may want to have the Location to sometimes encode
-- a set of nodes, but sometimes a concrete node, for example when the
-- computation depends on data which is stored on a particular server.


-- Calling (entering) the continuation provokes a remote call. It does
-- not return any value though, so may be run asynchronously if so
-- desired.

-- One would be able to evaluate remote computations like so:
rpc :: RemoteComputation -> IO ()
rpc (location,c) = send node c

-- In this setting, the double negation of A represents the remote
-- computation of A:

type NN a = (a ⊸ (Location1 ⊗ Computation)) ⊸ (Location2 ⊗ Computation)

-- Location2 is the node which performs the RPC call, and Location1 is
-- the node with recieves the result.

-- In the simplest case, the A in question is simply data stored on
-- Location2. Thus one can represent a distributed data structure by
-- inserting double-negations at appropriate places.  For example, a
-- distributed binary tree may look like this:

data Tree a = Bin (NN (Tree a)) (NN (Tree a)) | Leaf a

