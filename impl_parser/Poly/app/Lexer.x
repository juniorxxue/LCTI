{
module Lexer
  ( Token(..)
  , lexTokens
  ) where
}

%wrapper "basic"

$white    = [\ \t\r\n\f\v]
$alpha    = [A-Za-z]
$alnum    = [A-Za-z0-9]
$identchr = [$alnum _']

@ident = $alpha $identchr*

tokens :-
$white+                        ;
"--"[^\n]*                    ;

-- Symbols and punctuation
"."                            { \_ -> TDot }
"{"                            { \_ -> TLBrace }
"}"                            { \_ -> TRBrace }
"["                            { \_ -> TLBracket }
"]"                            { \_ -> TRBracket }
"("                            { \_ -> TLParen }
")"                            { \_ -> TRParen }
","                            { \_ -> TComma }
"*"                            { \_ -> TStar }
"->"                           { \_ -> TArrow }
"-"                            { \_ -> error "Unexpected '-' (did you mean '->'?)" }

-- Keywords and identifiers
@ident                          { \s -> kwOrIdent s }

{
-- Token type identical to the previous hand-written lexer

data Token
  = TForall
  | TDot
  | TArrow
  | TStar
  | TLBrace | TRBrace
  | TLBracket | TRBracket
  | TLParen | TRParen
  | TComma
  | TIntKw        -- "int"
  | TBoolKw       -- "bool"
  | TStKw         -- "ST"
  | TIdent String -- identifier
  | TEOF
  deriving (Eq, Show)

-- Public API expected by Parser.y
lexTokens :: String -> [Token]
lexTokens s = alexScanTokens s ++ [TEOF]

kwOrIdent :: String -> Token
kwOrIdent s = case s of
  "forall" -> TForall
  "int"    -> TIntKw
  "bool"   -> TBoolKw
  "ST"     -> TStKw
  _         -> TIdent s
}
