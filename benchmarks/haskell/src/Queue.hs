module Queue where

import Control.DeepSeq
import Data.IORef

import CQueue

data Queue = Queue {
    start :: IORef (Maybe Node),
    end   :: IORef (Maybe Node)
}

instance Show Queue where
    show _ = "queue"

instance NFData Queue where
    rnf Queue {} = ()

data Node = Node {
    index :: Int,
    next  :: IORef (Maybe Node)
}

instance NFData Node where
    rnf Node {} = ()

printNode :: Maybe Node -> IO()
printNode (Just node) = do print (index node)
printNode Nothing = do print "Empty node"

getList :: Queue -> IO [Int]
getList Queue {start = s} = go s []
    where go ref acc = do
            node <- readIORef ref
            case node of
                Nothing -> return $ reverse acc
                Just node' -> go (next node') (index node' : acc)

createQueue :: IO Queue
createQueue = do
    x <- newIORef Nothing
    y <- newIORef Nothing
    return Queue { start = x, end = y }

push :: Queue -> Int -> IO ()
push Queue { start = s, end = e} x = do
    startNode <- readIORef s
    terminationNode <- newIORef Nothing
    let node = x `seq` Just (Node { index = x, next = terminationNode })
    case startNode of
        Nothing -> do
            -- Empty queue
            writeIORef s node
            writeIORef e node
        Just _ -> do
            endNode <- readIORef e
            case endNode of
                Just (Node {next = n}) -> do
                    writeIORef n node
                    writeIORef e node
                Nothing -> return ()

pop :: Queue -> IO (Maybe Node)
pop Queue { start = s} = do
    n <- readIORef s
    case n of
        Nothing -> return Nothing
        Just (Node _ nextNodeRef) -> do
            nextNode <- readIORef nextNodeRef
            writeIORef s nextNode
            return n

-- | Rather verbose but there are a few edge cases to consider such as
-- |  * Index higher than the number of nodes.
-- |  * Last node empty
delete :: Queue -> Int -> IO (Maybe Node)
delete Queue { start = s } i = go s 0
    where go ref acc = do
            maybeNode <- readIORef ref
            case maybeNode of
                Nothing -> return Nothing
                Just node -> do
                     case acc == (i - 1) of
                         False -> go (next node) (acc + 1)
                         True -> do
                            maybeToDelete <- readIORef (next node)
                            case maybeToDelete of
                                Nothing -> return Nothing
                                Just toDelete -> do
                                    nextNode <- readIORef (next toDelete)
                                    writeIORef (next node) nextNode
                                    return maybeToDelete
