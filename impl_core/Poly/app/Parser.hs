module Parser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void (Void)

{-
type t := int 
       | bool
       | t1 -> t2
       | forall a. t
       | a
       | {t1, ...} -> t
       | [t]
       | t1 * t2


term e := n                      natural number
        | true | false           boolean
        | λx. e                  lambda
        | λx : t. e              annotated lambda
        | λ{x, ...}. e           uncurried lambda
        | λ{x : t, ...}. e       uncurried annotated lambda
        | e1 e2                  application
        | e {e1 ...}             uncurried application
        | e : t                  annotated term
        | Λa. e                 type lambda
        | e @ t                  type application
        | nil                    list nil
        | cons                  list cons
        | <e1, e2>              pair
        | fst e
        | snd e

environments Γ := empty
              | Γ, x : t
              | Γ, a
              | Γ, ^a
              | Γ, ^a=t
              | Γ ; 
-}

data NamedTyp = TInt | TBool 
              | TVar String 
              | TArr NamedTyp NamedTyp 
              | TForall String NamedTyp 
              | TUncurry [NamedTyp] NamedTyp 
              | TList NamedTyp 
              | TProd NamedTyp NamedTyp 
              | TST NamedTyp NamedTyp 
              deriving (Eq, Show)

data NamedTerm = LitInt Int
              | LitBool Bool
              | Var String
              | Abs String NamedTerm
              | AbsAnn NamedTyp NamedTerm
              | AbsUncurry String NamedTerm
              | AbsUncurryAnn [NamedTyp] NamedTerm
              | App NamedTerm NamedTerm
              | AppUncurry NamedTerm [NamedTerm]
              | Ann NamedTerm NamedTyp
              | TAbs NamedTerm
              | TApp NamedTerm NamedTyp
              | Nil
              | Cons
              | Pair NamedTerm NamedTerm
              | Fst NamedTerm
              | Snd NamedTerm
              deriving (Eq, Show)

-- Base parser type specialized to String input
type Parser = Parsec Void String

-- Consumes inter-token whitespace and comments
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

-- Attaches whitespace consumption to a token-level parser
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- Parses a fixed symbol and consumes trailing space
symbol :: String -> Parser String
symbol = L.symbol sc

-- Parses something inside parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Parses something inside brackets
brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

-- Parses something inside braces
braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- Reserved keywords that cannot be used as identifiers
reservedWords :: [String]
reservedWords = ["int", "bool", "forall", "true", "false", "nil", "cons", "fst", "snd"]

-- Parses a reserved word, ensuring it is not a prefix of an identifier
rword :: String -> Parser String
rword w = lexeme (try (string w <* notFollowedBy (alphaNumChar <|> char '_' <|> char '\'')))

-- Parses a lower-case identifier that is not reserved
identifier :: Parser String
identifier = lexeme . try $ do
  c <- lowerChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c:cs
  if name `elem` reservedWords
    then fail ("reserved word: " ++ name)
    else pure name

-- Entry parser for a full type, requiring EOF
typeParser :: Parser NamedTyp
typeParser = sc *> pType <* eof

-- Convenience wrapper to run the type parser and get Either with errors
parseNamedTyp :: String -> Either (ParseErrorBundle String Void) NamedTyp
parseNamedTyp = parse typeParser "<type>"

-- Parses a type with top-level precedence (forall or lower)
pType :: Parser NamedTyp
pType = pForall <|> pArrow

-- Parses universal quantification: forall a b. t
pForall :: Parser NamedTyp
pForall = do
  _ <- rword "forall" <|> symbol "∀"
  vars <- some identifier
  _ <- symbol "."
  body <- pType
  pure (foldr TForall body vars)

-- Parses arrow types, including uncurried arrow on the left
pArrow :: Parser NamedTyp
pArrow = pUncurriedArrow <|> pArrChain

-- Parses uncurried function arrow: {t1, t2, ...} -> t
pUncurriedArrow :: Parser NamedTyp
pUncurriedArrow = do
  args <- braces (pType `sepBy1` symbol ",")
  _ <- arrSym
  res <- pArrow
  pure (TUncurry args res)

-- Parses a right-associative chain for -> with product on the left
pArrChain :: Parser NamedTyp
pArrChain = do
  left <- pProd
  (
    do _ <- arrSym
       right <- pArrow
       pure (TArr left right)
   ) <|> pure left

-- Parses left-associative products: t1 * t2 * t3
pProd :: Parser NamedTyp
pProd = do
  ts <- pAtom `sepBy1` symbol "*"
  pure (foldl1 TProd ts)

-- Parses atomic types: int, bool, variables, lists, or parenthesized types
pAtom :: Parser NamedTyp
pAtom = choice
  [ TInt  <$ rword "int"
  , TBool <$ rword "bool"
  , TList <$> brackets pType
  , TVar  <$> identifier
  , parens pType
  ]

-- Parses either ASCII or Unicode arrow (-> or →)
arrSym :: Parser String
arrSym = symbol "->" <|> symbol "→"


-- Entry parser for a full term, requiring EOF
termParser :: Parser NamedTerm
termParser = sc *> pTerm <* eof

-- Convenience wrapper to run the term parser and get Either with errors
parseNamedTerm :: String -> Either (ParseErrorBundle String Void) NamedTerm
parseNamedTerm = parse termParser "<term>"

-- Parses a term allowing outermost annotation: e : t
pTerm :: Parser NamedTerm
pTerm = do
  e <- pNonAnn
  (do _ <- symbol ":"
      t <- pType
      pure (Ann e t)
   ) <|> pure e

-- Parses applications, type applications, and uncurried applications (no outer :)
pNonAnn :: Parser NamedTerm
pNonAnn = do
  h <- pHead
  pSuffixes h

-- Parses lambda, type-lambda, or an atomic head
pHead :: Parser NamedTerm
pHead = pLam <|> pTAbs <|> pAtomTerm

-- Repeatedly parses suffixes after a head: @t, {args}, or value application
pSuffixes :: NamedTerm -> Parser NamedTerm
pSuffixes e =
  (
    -- type application: e @ t
    do _ <- symbol "@"
       t <- pType
       pSuffixes (TApp e t)
  ) <|> (
    -- uncurried application: e {e1, e2, ...}
    do args <- braces (pTerm `sepBy1` symbol ",")
       pSuffixes (AppUncurry e args)
  ) <|> (
    -- value application: e a (left-assoc)
    do a <- pAtomTerm
       pSuffixes (App e a)
  ) <|> pure e

-- Parses value lambdas and their variants
pLam :: Parser NamedTerm
pLam = do
  _ <- symbol "λ"
  pLamUncurriedAnn <|> pLamUncurried <|> pLamSimple

-- Parses simple lambda: \x. e or annotated: \x : t. e (maps to Abs or AbsAnn)
pLamSimple :: Parser NamedTerm
pLamSimple = do
  x <- identifier
  (do _ <- symbol ":"
      t <- pType
      _ <- symbol "."
      body <- pTerm
      pure (AbsAnn t body)
   ) <|> do
      _ <- symbol "."
      body <- pTerm
      pure (Abs x body)

-- Parses unannotated uncurried lambda: \{x1, x2, ...}. e (names joined into a single String)
pLamUncurried :: Parser NamedTerm
pLamUncurried = do
  names <- braces (identifier `sepBy1` symbol ",")
  _ <- symbol "."
  body <- pTerm
  pure (AbsUncurry (concat (zipWith (++) names (replicate (length names - 1) ",") ++ [""])) body)

-- Parses annotated uncurried lambda: \{x1 : t1, x2 : t2, ...}. e (stores only types)
pLamUncurriedAnn :: Parser NamedTerm
pLamUncurriedAnn = do
  anns <- braces (sepBy1 ((identifier >> symbol ":" >> pType)) (symbol ","))
  _ <- symbol "."
  body <- pTerm
  pure (AbsUncurryAnn anns body)

-- Parses type lambda: /\a b c. e (nests TAbs, discarding names)
pTAbs :: Parser NamedTerm
pTAbs = do
  _ <- try (symbol "Λ")
  _vars <- some identifier
  _ <- symbol "."
  body <- pTerm
  pure (foldr (const TAbs) body _vars)

-- Parses atomic terms: literals, variables, pairs, prefix fst/snd, parenthesized
pAtomTerm :: Parser NamedTerm
pAtomTerm = choice
  [ LitInt <$> lexeme L.decimal
  , LitBool True  <$ rword "true"
  , LitBool False <$ rword "false"
  , Nil <$ rword "nil"
  , Cons <$ rword "cons"
  , Fst <$> (rword "fst" *> pAtomTerm)
  , Snd <$> (rword "snd" *> pAtomTerm)
  , pPair
  , Var <$> identifier
  , parens pTerm
  ]

-- Parses a pair: <e1, e2>
pPair :: Parser NamedTerm
pPair = do
  _ <- symbol "<"
  e1 <- pTerm
  _ <- symbol ","
  e2 <- pTerm
  _ <- symbol ">"
  pure (Pair e1 e2)