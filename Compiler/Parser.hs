module Compiler.Parser where

import Prelude hiding (abs, lookup)
import Text.Parsec
import Text.Parsec.String
import Text.ParserCombinators.Parsec.Number
import Data.Map (Map, lookup, insert, empty)
import Data.Maybe (maybe)
import Compiler.Types

addVar :: Map String Int -> String -> Map String Int
addVar m v = insert v 0 $ (+ 1) <$> m

keywords = [ "let", "in", "ifz" ]

varParser :: Parser String
varParser = do
  v0 <- letter
  v1 <- many (letter <|> digit)
  let v = v0:v1
  if v `elem` keywords
    then fail ("Unexpected keyword " <> v)
    else pure v

varParser' :: Map String Int -> Parser Int
varParser' m = do
  v <- varParser
  maybe (fail $ "Unknown variable " <> v) pure (lookup v m)

-- parsec's sepBy1 doesnt use try
mySepBy1 a b = (:) <$> a <*> helper where
  helper = try (b >> mySepBy1 a b) <|> pure []

appParser m = do
  l <- mySepBy1 (subExprParser m) (many1 space)
  pure $ f $ reverse l
  where
    f [a] = a
    f (a:r) = app (f r) a

absParser m = do
  char '\\'
  v <- varParser
  char '.'
  many1 space
  a <- exprParser' (addVar m v)
  pure $ abs' a

letParser m = do
  string "let"
  many1 space
  v <- varParser
  many1 space
  char '='
  many1 space
  a <- exprParser' m
  many1 space
  string "in"
  many1 space
  b <- exprParser' (addVar m v)
  pure $ let' a b

addParser m = do
  a <- try (subExprParser m) <|> try (appParser m)
  many1 space
  char '+'
  many1 space
  b <- exprParser' m
  pure $ primOp Plus [a,b]

ifzParser m = do
  string "ifz"
  many1 space
  a <- subExprParser m
  many1 space
  b <- subExprParser m
  many1 space
  c <- subExprParser m
  pure $ primOp IfZ [a,b,c]

tupAccessParser m = do
  char '.'
  n <- int
  char '.'
  mm <- int
  many1 space
  a <- subExprParser m
  pure $ tupAccess n mm a

tupParser m = primOp Tup <$> (char '(' >> spaces >> mySepBy1 (exprParser' m) (spaces >> char ',' >> spaces) <* char ')')

parenParser m = char '(' >> spaces >> exprParser' m <* spaces <* char ')'

subExprParser :: Map String Int -> Parser (Expr ())
subExprParser m =     try (evar <$> varParser' m)
                  <|> try (absParser m)
                  <|> try (primInt <$> int)
                  <|> try (letParser m)
                  <|> try (parenParser m)
                  <|> try (tupParser m)

exprParser' :: Map String Int -> Parser (Expr ())
exprParser' m = try (addParser m) <|> try (ifzParser m) <|> try (appParser m) <|> try (tupAccessParser m) <|> try (subExprParser m)

exprParser :: Parser (Expr ())
exprParser = exprParser' empty

exprFileParser :: Parser (Expr ())
exprFileParser = spaces >> exprParser <* spaces <* eof
