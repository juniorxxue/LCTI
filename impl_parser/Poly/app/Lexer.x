{
module Lexer
  ( Token(..)
  , lexTokens
  ) where
}

%wrapper "basic"

$white    = [\ \t\r\n\f\v]
$digit    = [0-9]
$alpha    = [A-Za-z]
$alnum    = [A-Za-z0-9]
$identchr = [$alnum _']

@ident = $alpha $identchr*
@nat   = $digit+

tokens :-
$white+                        ;
"--"[^\n]*                    ;

-- Symbols and punctuation (order matters - longer patterns first)
"->"                           { \_ -> TArrow }
"→"                            { \_ -> TArrow }
"λ"                            { \_ -> TLambda }
"Λ"                            { \_ -> TBigLambda }
"∀"                            { \_ -> TForall }
"."                            { \_ -> TDot }
"{"                            { \_ -> TLBrace }
"}"                            { \_ -> TRBrace }
"["                            { \_ -> TLBracket }
"]"                            { \_ -> TRBracket }
"("                            { \_ -> TLParen }
")"                            { \_ -> TRParen }
","                            { \_ -> TComma }
"*"                            { \_ -> TStar }
":"                            { \_ -> TColon }
"@"                            { \_ -> TAt }
"<"                            { \_ -> TLAngle }
">"                            { \_ -> TRAngle }
"-"                            { \_ -> error "Unexpected '-' (did you mean '->'?)" }

-- Keywords and identifiers
@nat                            { \s -> TNat (read s) }
@ident                          { \s -> kwOrIdent s }

{
-- Token type identical to the previous hand-written lexer

data Token
  = TForall
  | TDot
  | TArrow
  | TStar
  | TColon
  | TAt
  | TLAngle | TRAngle
  | TLBrace | TRBrace
  | TLBracket | TRBracket
  | TLParen | TRParen
  | TComma
  | TLambda
  | TBigLambda
  | TIntKw        -- "int"
  | TBoolKw       -- "bool"
  | TStKw         -- "ST"
  | TTrueKw       -- "true"
  | TFalseKw      -- "false"
  | TNilKw        -- "nil"
  | TConsKw       -- "cons"
  | TFstKw        -- "fst"
  | TSndKw        -- "snd"
  | TNat Int      -- natural number
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
  "true"   -> TTrueKw
  "false"  -> TFalseKw
  "nil"    -> TNilKw
  "cons"   -> TConsKw
  "fst"    -> TFstKw
  "snd"    -> TSndKw
  "lambda" -> TLambda
  "Lambda" -> TBigLambda
  _        -> TIdent s
}
