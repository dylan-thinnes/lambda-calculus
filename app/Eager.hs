module Eager where

import Data.Char
import Data.Maybe
import Data.Functor.Identity

import Control.Monad.State
import Control.Monad.Except

data Err = EOFError | ParseErr String
  deriving Show

type LL1T m stream = StateT [stream] (ExceptT Err m)
type LL1 stream = LL1T Identity stream

run :: LL1 stream a -> [stream] -> Either Err (a, [stream])
run action stream = runIdentity $ runT action stream

runT :: LL1T m stream a -> [stream] -> m (Either Err (a, [stream]))
runT action stream = runExceptT $ runStateT action stream

fullParse :: LL1 Char a -> String -> Either String a
fullParse parser stream =
  case run (skipSpaces >> parser >>= \a -> skipSpaces >> pure a) stream of
    Left EOFError -> Left "End of input reached unexpectedly."
    Left (ParseErr msg) -> Left $ "Parse error: " ++ msg
    Right (a, rest)
      | null rest -> Right a
      | otherwise -> Left $ "Input left over: " ++ rest

readsWith :: LL1 Char a -> ReadS a
readsWith parser stream =
  case run (skipSpaces >> parser >>= \a -> skipSpaces >> pure a) stream of
    Left EOFError -> error "End of input reached unexpectedly."
    Left (ParseErr msg) -> error $ "Parse error: " ++ msg
    Right (a, rest) -> [(a, rest)]

peek :: Monad m => LL1T m stream stream
peek = do
  stream <- get
  case stream of
    [] -> throwError EOFError
    (head:_) -> pure head

pop :: Monad m => LL1T m stream stream
pop = fmap fromJust $ popIf (const True)

popIf :: Monad m => (stream -> Bool) -> LL1T m stream (Maybe stream)
popIf pred = do
  head <- peek
  if pred head
    then modify (drop 1) >> pure (Just head)
    else pure Nothing

catchEOF :: Monad m => a -> LL1T m stream a -> LL1T m stream a
catchEOF def action = catchError action $ \err ->
  case err of
    EOFError -> pure def
    _ -> throwError err

err :: Monad m => String -> LL1T m stream a
err = throwError . ParseErr

toErr :: Monad m => String -> LL1T m stream (Maybe a) -> LL1T m stream a
toErr msg action = do
  a <- action
  case a of
    Nothing -> err msg
    Just x -> pure x

(!) :: Monad m => String -> LL1T m stream (Maybe a) -> LL1T m stream a
(!) = toErr

many :: Monad m => LL1T m stream (Maybe a) -> LL1T m stream [a]
many sub = do
  a <- catchEOF Nothing sub
  case a of
    Nothing -> pure []
    Just x -> (x:) <$> many sub

skipSpaces :: Monad m => LL1T m Char ()
skipSpaces = do
  many (popIf isSpace)
  pure ()
