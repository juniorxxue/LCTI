{ 
-- ===========================================================
--  Haskell header
-- ===========================================================
module Parser (parseTyp, parseTypTokens) where

import qualified AST as AST
import Lexer
}

-- ===========================================================
--  Parser configuration
-- ===========================================================
%name parseTypTokens
%tokentype { Token }

%token
  FORALL   { TForall }         -- forall
  DOT      { TDot }            -- .
  ARROW    { TArrow }          -- ->
  STAR     { TStar }           -- *
  LBRACE   { TLBrace }         -- {
  RBRACE   { TRBrace }         -- }
  LBRACK   { TLBracket }       -- [
  RBRACK   { TRBracket }       -- ]
  LPAREN   { TLParen }         -- (
  RPAREN   { TRParen }         -- )
  COMMA    { TComma }          -- ,
  TINTKW   { TIntKw }          -- int
  TBOOLKW  { TBoolKw }         -- bool
  TSTKW    { TStKw }           -- ST
  IDENT    { TIdent $$ }       -- identifier (String)
  EOF      { TEOF }

%right ARROW
%left  STAR

%%

-- ===========================================================
--  Grammar: faithful to NamedTyp
-- ===========================================================

Input :: { AST.NamedTyp }
  : Type EOF { $1 }

-- one production rule: directly allow all forms of type
Type :: { AST.NamedTyp }
  : TINTKW                     { AST.TInt }                         -- int
  | TBOOLKW                    { AST.TBool }                        -- bool
  | IDENT                      { AST.TVar $1 }                      -- variable
  | FORALL IDENT DOT Type       { AST.TForall $2 $4 }               -- forall a. t
  | Type ARROW Type            { AST.TArr $1 $3 }                   -- t1 -> t2
  | Type STAR Type             { AST.TProd $1 $3 }                  -- t1 * t2
  | LBRACE TypeList RBRACE ARROW Type { AST.TUncurry $2 $5 }        -- {t1,...} -> t
  | LBRACK Type RBRACK         { AST.TList $2 }                     -- [t]
  | TSTKW Type Type            { AST.TST $2 $3 }                    -- ST t1 t2
  | LPAREN Type RPAREN         { $2 }                               -- (t)

TypeList :: { [AST.NamedTyp] }
  : Type COMMA TypeList { $1 : $3 }
  | Type                { [$1] }

{
-- ===========================================================
--  Footer: combine lexer + parser
-- ===========================================================
parseTyp :: String -> AST.NamedTyp
parseTyp s = parseTypTokens (lexTokens s)

happyError :: [Token] -> a
happyError _ = error "parse error"
}