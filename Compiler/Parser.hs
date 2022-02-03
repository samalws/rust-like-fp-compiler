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

keywords = [ "let", "in" ]

varParser :: Parser String
varParser = do
  v <- many1 letter
  if (elem v keywords)
    then fail ("Unexpected keyword " <> v)
    else pure v

varParser' :: Map String Int -> Parser Int
varParser' m = do
  v <- varParser
  maybe (fail $ "Unknown variable " <> v) pure (lookup v m)

appParser m = do
  a <- subExprParser m
  b <- subExprParser m
  pure $ app a b

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
  b <- exprParser' (addVar m v)
  pure $ let' a b

primValParser = char '+' >> pure (primVal Plus)

parenParser m = char '(' >> spaces >> exprParser' m <* spaces <* char ')'

subExprParser :: Map String Int -> Parser (Expr ())
subExprParser m =     try (letParser m)
                  <|> try (evar <$> varParser' m)
                  <|> try (absParser m)
                  <|> try (primInt <$> int)
                  <|> try primValParser
                  <|> try (parenParser m)

exprParser' :: Map String Int -> Parser (Expr ())
exprParser' m = subExprParser m <|> try (appParser m)

exprParser :: Parser (Expr ())
exprParser = exprParser' empty
