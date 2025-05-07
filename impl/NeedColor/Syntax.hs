{-# LANGUAGE OverloadedStrings #-}
module Syntax where

import Control.Monad (forM_)
import Control.Applicative ((<|>))
import Data.Void
import Data.List (isPrefixOf)
import qualified Text.Megaparsec as MP
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Map.Strict as M

-- === AST definitions ===

data Typ
  = TInt
  | TVar String
  | TArr Typ Typ
  | TForall String Typ
  deriving (Eq, Show)

data Trm
  = Lit Int
  | Var String
  | Lam String Trm
  | App Trm Trm
  deriving (Eq, Show)

type TEnv = [(String, Typ)]
type SEnv = [(String, Bool)]

type Env = (TEnv, SEnv)

-- === Parser setup ===

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = MP.between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = MP.between (symbol "[") (symbol "]")

comma :: Parser String
comma = symbol ","

-- | Term variable identifiers: x, y, or z optionally followed by digits
termIdent :: Parser String
termIdent = lexeme ((:) <$> MP.oneOf ['x','y','z', 'f'] <*> MP.many C.digitChar)

-- | Type variable identifiers: a, b, c, or d optionally followed by digits
typeIdent :: Parser String
typeIdent = lexeme ((:) <$> MP.oneOf ['a','b','c','d'] <*> MP.many C.alphaNumChar)

-- === Typ parser ===

pTyp :: Parser Typ
pTyp = makeForall

-- Parse possibly multiple quantifiers: 'forall a b c. T'
makeForall :: Parser Typ
makeForall =
      MP.try (do
        MP.choice [symbol "forall", symbol "∀"]
        vs <- MP.some typeIdent
        symbol "."
        t <- pTyp
        pure (foldr TForall t vs))
  <|> pArr

pArr :: Parser Typ
pArr = do
  t1 <- pTypAtom
  rest <- MP.optional (symbol "->" *> pTyp)
  pure $ maybe t1 (TArr t1) rest

pTypAtom :: Parser Typ
pTypAtom =
      TInt <$ symbol "Int"
  <|> TVar <$> typeIdent
  <|> parens pTyp

parseTyp :: String -> Either (MP.ParseErrorBundle String Void) Typ
parseTyp = MP.parse (sc *> pTyp <* MP.eof) "<type>"

-- === Trm parser ===

pTrm :: Parser Trm
pTrm = makeApp

makeApp :: Parser Trm
makeApp = do
  f <- pTrmAtom
  go f
 where
  go f = MP.choice
    [ do arg <- pTrmAtom; go (App f arg)
    , pure f
    ]

pTrmAtom :: Parser Trm
pTrmAtom =
      Lit <$> lexeme L.decimal
  <|> Var <$> termIdent
  <|> parens pTrm
  <|> parseLam

parseLam :: Parser Trm
parseLam = do
  MP.choice [symbol "\\", symbol "λ"]
  v <- termIdent
  symbol "."
  e <- pTrm
  pure (Lam v e)

parseTrm :: String -> Either (MP.ParseErrorBundle String Void) Trm
parseTrm = MP.parse (sc *> pTrm <* MP.eof) "<term>"

-- === Env parser ===

-- | Generic lowercase identifiers for environment keys (e.g., id, f1, f2)
varIdent :: Parser String
varIdent = lexeme ((:) <$> C.lowerChar <*> MP.many C.alphaNumChar)

-- Bindings for type environment: allow any lowercase identifier for key
pTBinding :: Parser (String, Typ)
pTBinding = (,) <$> varIdent <* symbol ":" <*> pTyp

-- Top-level parser for TEnv
parseEnv :: String -> Either (MP.ParseErrorBundle String Void) TEnv
parseEnv = MP.parse (sc *> brackets (pTBinding `MP.sepBy` comma) <* MP.eof) "<tenv>"

-- === Bulk parsing utilities ===

-- | Parse a map of term-strings into a map of Trm
parseTermMap :: M.Map String String -> Either (MP.ParseErrorBundle String Void) (M.Map String Trm)
parseTermMap = M.traverseWithKey (const parseTrm)

-- | Parse a map of type-strings into a map of Typ
parseTypMap :: M.Map String String -> Either (MP.ParseErrorBundle String Void) (M.Map String Typ)
parseTypMap = M.traverseWithKey (const parseTyp)

-- | Parse a map of env-strings into a map of TEnv
parseEnvMap :: M.Map String String -> Either (MP.ParseErrorBundle String Void) (M.Map String TEnv)
parseEnvMap = M.traverseWithKey (const parseEnv)

-- === Pretty printer ===

ppTyp :: Typ -> String
ppTyp TInt = "Int"
ppTyp (TVar v) = v
ppTyp (TArr t1 t2) =
  let s1 = case t1 of TArr _ _ -> "("++ppTyp t1++")"; _ -> ppTyp t1 in
  s1 ++ " -> " ++ ppTyp t2
ppTyp (TForall v t) = "forall "++v++". "++ppTyp t

ppTrm :: Trm -> String
ppTrm (Lit n) = show n
ppTrm (Var v) = v
ppTrm (Lam v b) = "λ"++v++". "++ppTrm b
ppTrm (App f x) =
  let pf = if isLam f then "("++ppTrm f++")" else ppTrm f
      px = if isApp x || isLam x then "("++ppTrm x++")" else ppTrm x
  in pf++" "++px
  where isLam Lam{} = True; isLam _ = False
        isApp App{} = True; isApp _ = False

ppTEnv :: TEnv -> String
ppTEnv env = "[" ++ concat (zipWith (\(v,t) i -> (if i>0 then ", " else "")++v++": "++ppTyp t) env [0..]) ++ "]"

-- === Demo ===

termMapString :: M.Map String String
termMapString = M.fromList [("ex1", "f1 (\\x. x) 1")
                           ,("ex2", "f1 (\\x. x)")
                           ,("ex3", "f1")
                           ,("ex4", "f2")
                     ]

termMap :: M.Map String Trm
termMap = case parseTermMap termMapString of
  Left err -> error "term parse error"
  Right terms -> terms

bigEnvStr :: String
bigEnvStr = "[id : forall a. a -> a, f1 : forall a. (Int -> Int) -> a -> a, f2 : forall a. (a -> a) -> a -> a]"

bigEnv :: TEnv
bigEnv = case parseEnv bigEnvStr of
  Left err -> error "env parse error"
  Right env -> env
