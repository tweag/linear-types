{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module SocketExample where

-- import Control.Exception ( bracket, catch )
-- import Control.Monad ( forever )

import Data.ByteString.Char8 ()
import Data.String (String, fromString)
import IO
import Linear.Std
import Prelude (fromInteger, (++), show)
import qualified Prelude as P
import Socket
import Socket.Generic (State(..))
import qualified System.Socket as S
import qualified System.Socket.Family.Inet6 as S
import qualified System.Socket.Type.Stream as S
import qualified System.Socket.Protocol.TCP as S

putStrLn :: String -> IO' 'Ω ()
putStrLn s = unsafeIOtoIOΩ (P.putStrLn s)

main :: IO' 'Ω (Socket 'Connected)
main = do
  s1 <- socket
  s2 <- bind s1 (S.SocketAddressInet6 S.inet6Any 8080 0 0)
  s3 <- listen s2
  putStrLn "Listening socket ready..."
  acceptAndHandle s3
  -- forever $ acceptAndHandle s `catch` \e-> print (e :: SocketException)

  --  bracket
  -- ( socket :: IO (Socket Inet6 Stream TCP) )
  -- ( \s-> do
  --   close s
  --   putStrLn "Listening socket closed."
  -- )
  -- ( \s-> do
  --   setSocketOption s (ReuseAddress True)
  --   setSocketOption s (V6Only False)
  --   bind s (SocketAddressInet6 inet6Any 8080 0 0)
  --   listen s 5
  --   putStrLn "Listening socket ready..."
  --   forever $ acceptAndHandle s `catch` \e-> print (e :: SocketException)
  -- )

acceptAndHandle :: Socket 'Listening -> IO' 'Ω (Socket 'Connected)
acceptAndHandle s = do
  (s, p1) <- accept s
  putStrLn $ "Accepted connection"
  (p2, Unrestricted _) <- send p1 "Hello world!"
  return p2

  --  bracket
  -- ( accept s )
  -- ( \(p, addr)-> do
  --   close p
  --   putStrLn $ "Closed connection to " ++ show addr
  -- )
  -- ( \(p, addr)-> do
  --   putStrLn $ "Accepted connection from " ++ show addr
  --   sendAll p "Hello world!" msgNoSignal
  -- )
