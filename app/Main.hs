{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
module Main where

import "base" Control.Monad
import "base" Data.Bifunctor
import "base" Data.Char
import "base" Data.Foldable
import "base" Data.List (elemIndex)
import "base" Data.Monoid (Endo(..))
import "base" Data.Word
import "base" Prelude hiding (abs)
import "base" System.Environment
import "base" GHC.Generics
import "base" GHC.TypeLits
import "base" Data.Proxy

import "bytestring" Data.ByteString (ByteString (..), pack)

import "optparse-applicative" Options.Applicative hiding (many)
import "optparse-applicative" Options.Applicative.Help.Pretty (Doc(..), text, (<+>), vsep, align, bold)

import "recursion-schemes" Data.Functor.Foldable (cata)
import "recursion-schemes" Data.Functor.Foldable.TH (makeBaseFunctor)

import Eager

import Debug.Trace

class Pretty a where
  pretty' :: a -> String

newtype PP a = PP a
instance Pretty a => Show (PP a) where
  show (PP a) = pretty' a
pretty = PP

data LCG abs var = Abs abs (LCG abs var) | Var var | App (LCG abs var) (LCG abs var)
  deriving (Show, Eq, Ord)

makeBaseFunctor ''LCG

data IOMode = NamedIO | DeBruijnIO | BinaryIO
  deriving (Show, Enum, Bounded)

shortIOMode :: IOMode -> Char
shortIOMode = head . show

longIOMode :: IOMode -> String
longIOMode = reverse . drop 2 . reverse . show

helpMode :: IOMode -> String
helpMode NamedIO = "Lambda calculus with named variables (e.g. λx.x x)"
helpMode DeBruijnIO = "Lambda calculus with DeBruijn indices (e.g. λ 1 1)"
helpMode BinaryIO = "Binary lambda calculus written as a series of 1s and 0s, e.g. 00011010"

instance Read IOMode where
  readsPrec _ input = do
    (front, rest) <- lex input
    mode <- [minBound..maxBound]
    representation <- [show mode, [shortIOMode mode], longIOMode mode]
    guard $ map toLower front == map toLower representation
    pure (mode, rest)

data Options = Options
  { inputMode :: IOMode
  , outputMode :: IOMode
  }
  deriving Show

options :: Parser Options
options = Options <$> input <*> output
  where
    input = option auto $ fold
      [ long "input"
      , short 'i'
      , helpDoc $ Just $ vsep [text "Input mode, one of ", ioModeHelp]
      , value NamedIO
      , metavar $ map shortIOMode [minBound..maxBound]
      ]
    output = option auto $ fold
      [ long "output"
      , short 'o'
      , helpDoc $ Just $ vsep [text "Output mode, one of ", ioModeHelp]
      , value NamedIO
      , metavar $ map shortIOMode [minBound..maxBound]
      ]
    ioModeHelp = vsep $ map mkIOModeHelp [minBound..maxBound]
    mkIOModeHelp mode =
      text "- " <+>
        align (vsep [ bold (text [shortIOMode mode]) <+> text "or" <+> bold (text (longIOMode mode)) <+> text ": "
                    , text $ helpMode mode
                    ])

optionsPrefs = prefs mempty
optionsInfo = info (helper <*> options) $ fullDesc <> failureCode 1

main :: IO ()
main = do
  contents <- getContents
  options <- customExecParser optionsPrefs optionsInfo
  case inputMode options of
    DeBruijnIO -> do
      let body = read @DeBruijn contents
      print $ pretty body
      print $ pretty $ toBits body
      pure ()
    NamedIO -> do
      let body = read @Named contents
      print $ pretty body
      print $ pretty $ toDeBruijn body
      print $ pretty $ toBits $ toDeBruijn body
      pure ()
    mode -> do
      putStrLn $ unwords ["Input mode", show mode, "not yet supported."]
      pure ()

type Named = LCG String String
type DeBruijn = LCG () Int

data POS = FuncPOS | ArgPOS | BodyPOS

instance Pretty Named where
  pretty' = go BodyPOS
    where
      go pos (Abs name body) =
        case pos of
          BodyPOS -> inner
          _ -> "(" ++ inner ++ ")"
        where
          inner = "λ" ++ name ++ "." ++ go BodyPOS body
      go pos (App func arg) =
        case pos of
           ArgPOS -> "(" ++ inner ++ ")"
           _ -> inner
        where
          inner = go FuncPOS func ++ " " ++ go ArgPOS arg
      go _ (Var name) = name

instance Read Named where
  readsPrec _ = readsWith top
    where
    top :: LL1 Char Named
    top = do
      let name :: LL1 Char String
          name = many (popIf isAlpha)

      funcArgs <- many $ do
        skipSpaces
        head <- peek
        if | head `elem` "λ\\" -> Just <$> do
              pop
              skipSpaces
              var <- name
              skipSpaces
              "No '.' found after lambda's variable" ! popIf ('.' ==)
              body <- top
              pure $ Abs var body
           | isAlpha head -> Just . Var <$> name
           | head == '(' -> Just <$> do
              pop
              inner <- top
              "No matching closing bracket found." ! popIf (')' ==)
              pure inner
           | otherwise -> pure Nothing

      case funcArgs of
        [] -> err "No input for expression to parse."
        (func:args) -> pure $ foldl App func args

instance Pretty DeBruijn where
  pretty' = go False
    where
      go _ (Abs name body) = "λ " ++ go False body
      go isAppArg (App func arg) =
        let together = go False func ++ " " ++ go True arg
        in
        if isAppArg
           then "(" ++ together ++ ")"
           else together
      go _ (Var idx) = show idx

instance Read DeBruijn where
  readsPrec _ = readsWith top
    where
    top :: LL1 Char DeBruijn
    top = do
      let idx :: LL1 Char Int
          idx = read <$> many (popIf isDigit)

      funcArgs <- many $ do
        skipSpaces
        head <- peek
        if | head `elem` "λ\\" -> Just <$> do
              pop
              skipSpaces
              body <- top
              pure $ Abs () body
           | isDigit head -> Just . Var <$> idx
           | head == '(' -> Just <$> do
              pop
              inner <- top
              "No matching closing bracket found." ! popIf (')' ==)
              pure inner
           | otherwise -> pure Nothing

      case funcArgs of
        [] -> err "No input for expression to parse."
        (func:args) -> pure $ foldl App func args

toDeBruijn :: Named -> DeBruijn
toDeBruijn exp = cata alg exp []
  where
    alg :: LCGF String String ([String] -> LCG () Int) -> [String] -> LCG () Int
    alg (VarF name) stack =
      case elemIndex name stack of
        Nothing -> Var 0
        Just i -> Var $ i + 1
    alg (AppF func arg) stack = App (func stack) (arg stack)
    alg (AbsF arg body) stack = Abs () $ body $ arg : stack

toNamed :: DeBruijn -> Named
toNamed exp = cata alg exp 0
  where
    name :: Int -> String
    name i =
      let letters = ['x'..'z'] ++ ['a'..'w']
          (div, mod) = divMod i 26
          suffix = if div == 0 then "" else show div
      in
      letters !! mod : suffix

    alg :: LCGF () Int (Int -> LCG String String) -> Int -> LCG String String
    alg (VarF idx) depth
      | 0 < idx && idx <= depth
      = Var $ name (depth - idx)
      | otherwise
      = Var "_"
    alg (AppF func arg) depth = App (func depth) (arg depth)
    alg (AbsF arg body) depth = Abs (name depth) $ body $ depth + 1

newtype Bits = Bits { unbits :: [Bool] }

instance Pretty Bits where
  pretty' (Bits bools) = map (\b -> if b then '1' else '0') bools

toBits :: DeBruijn -> Bits
toBits = Bits . go
  where
    go (Abs () body) = False : False : go body
    go (App func arg) = False : True : go func ++ go arg
    go (Var idx) = replicate idx True ++ [False]

fromBits :: Bits -> Either String DeBruijn
fromBits (Bits bools) =
  case go bools of
    Right (x, []) -> Right x
    Right (x, leftover) -> Left $ "fromBits: Too much input, " ++ show (length leftover) ++ " bits left over."
    Left err -> Left err
  where
    go (False : False : rest) = fmap (first (Abs ())) $ go rest
    go (False : True : rest) = do
      (func, rest') <- go rest
      (arg, rest'') <- go rest'
      pure (App func arg, rest'')
    go (True : rest) =
      let size = length (takeWhile id rest) + 1
          rest' = drop 1 $ dropWhile id rest
      in
      pure (Var size, rest')

bitsToTerm :: Bits -> DeBruijn
bitsToTerm (Bits bools) = foldr cons nil $ map (\b -> if b then true else false) bools
  where
    true = toDeBruijn $ read "λx.λy.x"
    false = toDeBruijn $ read "λx.λy.y"
    cons x y = Abs () $ App (App (Var 1) x) y
    nil = false

class Encodable a where
  encode :: a -> DeBruijn

  default encode :: (Generic a, Encodable1 (Rep a)) => a -> DeBruijn
  encode = encode1 . from

instance Encodable Bool where
  encode True = toDeBruijn $ read "λx.λy.x"
  encode False = toDeBruijn $ read "λx.λy.y"

instance (Encodable a, Encodable b) => Encodable (a, b) where
  encode (a, b) = Abs () $ foldl App (Var 1) [encode a, encode b]

instance (Encodable a, Encodable b, Encodable c) => Encodable (a, b, c) where
  encode (a, b, c) = Abs () $ foldl App (Var 1) [encode a, encode b, encode c]

instance Encodable Int where
  encode i = Abs () $ Abs () $ foldr (.) id (replicate i (App (Var 2))) (Var 1)

class Encodable1 a where
  encode1 :: a x -> DeBruijn

-- Products, using a custom "handler" in case we're inside a sum
class UseHandler (f :: * -> *) where
  useHandler :: f x -> DeBruijn -> DeBruijn

instance (Encodable1 f, UseHandler (g :*: h)) => UseHandler (f :*: (g :*: h)) where
  useHandler (f :*: gh) handler = useHandler gh $ handler `App` encode1 f

instance (Encodable1 f, Encodable1 g) => UseHandler (f :*: M1 tag meta g) where
  useHandler (f :*: (M1 g)) handler = (handler `App` encode1 f) `App` encode1 g

instance UseHandler f => UseHandler (M1 tag meta f) where
  useHandler (M1 fx) handler = useHandler fx handler

instance Encodable a => UseHandler (Rec0 a) where
  useHandler (K1 fx) handler = handler `App` encode fx

instance UseHandler U1 where
  useHandler U1 handler = handler

-- If we need Encodable1 over products, with no sums, at top-level, this pairs with C1 to create an instance
instance UseHandler (f :*: g) => Encodable1 (f :*: g) where
  encode1 fgx = Abs () $ useHandler fgx (Var 1)

-- Base cases for UseHandler / General cases for non-UseHandler
instance Encodable1 f => Encodable1 (C1 meta f) where
  encode1 = encode1 . unM1

instance Encodable1 f => Encodable1 (S1 meta f) where
  encode1 = encode1 . unM1

instance Encodable a => Encodable1 (Rec0 a) where
  encode1 = encode . unK1

instance Encodable1 U1 where
  encode1 _ = Abs () $ Var 1

-- Sums, accounting for total sum depth, dispatches to UseHandler
class DepthToHandler (f :: * -> *) (n :: Nat) | f -> n where
  depthToHandler :: f x -> DeBruijn

instance (KnownNat n, UseHandler f, DepthToHandler g subDepth, n ~ (subDepth + 1))
  => DepthToHandler (f :+: g) n where
  depthToHandler (L1 fx) = useHandler fx $ Var $ fromIntegral $ natVal $ Proxy @n
  depthToHandler (R1 gx) = depthToHandler gx

instance UseHandler (M1 tag meta f) => DepthToHandler (M1 tag meta f) 1 where
  depthToHandler fx = useHandler fx (Var 1)

-- Use PassDepth to define Encodable1 for sums of products
instance (KnownNat n, DepthToHandler (f :+: g) n) => Encodable1 (f :+: g) where
  encode1 fx =
    let depth = fromIntegral $ natVal $ Proxy @n
        wrapAbs = foldr (.) id $ replicate depth (Abs ())
    in
    wrapAbs $ depthToHandler fx

-- Top-level recursion through D1
instance Encodable1 f => Encodable1 (D1 meta f) where
  encode1 = encode1 . unM1

-- Generic-deriving instances
instance Encodable ()

data A = X | Y Bool Bool Bool | Z Int deriving (Show, Generic)
instance Encodable A

data B = B Int Int deriving (Show, Generic)
instance Encodable B

data CC = CC1 Int | CC2 CC CC
  deriving (Show, Generic)
instance Encodable CC
