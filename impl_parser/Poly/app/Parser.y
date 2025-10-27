{ 
-- ===========================================================
--  Haskell header
-- ===========================================================
module Parser (parseTyp, parseTypTokens, parseTerm, parseTermTokens) where

import qualified AST as AST
import Lexer
}

-- ===========================================================
--  Parser configuration
-- ===========================================================
%name parseTypTokens typ
%name parseTermTokens term
%tokentype { Token }

%token
  FORALL   { TForall }         -- forall
  DOT      { TDot }            -- .
  ARROW    { TArrow }          -- ->
  STAR     { TStar }           -- *
  COLON    { TColon }          -- :
  AT       { TAt }             -- @
  LANGLE   { TLAngle }         -- <
  RANGLE   { TRAngle }         -- >
  LBRACE   { TLBrace }         -- {
  RBRACE   { TRBrace }         -- }
  LBRACK   { TLBracket }       -- [
  RBRACK   { TRBracket }       -- ]
  LPAREN   { TLParen }         -- (
  RPAREN   { TRParen }         -- )
  COMMA    { TComma }          -- ,
  LAMBDA   { TLambda }         -- λ or \
  BIGLAM   { TBigLambda }      -- Λ or /\
  TINTKW   { TIntKw }          -- int
  TBOOLKW  { TBoolKw }         -- bool
  TSTKW    { TStKw }           -- ST
  TRUE     { TTrueKw }         -- true
  FALSE    { TFalseKw }        -- false
  NIL      { TNilKw }          -- nil
  CONS     { TConsKw }         -- cons
  FST      { TFstKw }          -- fst
  SND      { TSndKw }          -- snd
  NAT      { TNat $$ }         -- natural number (Int)
  IDENT    { TIdent $$ }       -- identifier (String)
  EOF      { TEOF }

%right ARROW
%left  STAR

%%

-- ===========================================================
--  Grammar: faithful to NamedTyp
-- ===========================================================

typ :: { AST.NamedTyp }
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

-- ===========================================================
--  Grammar: faithful to NamedTerm
-- ===========================================================

term :: { AST.NamedTerm }
  : Term EOF { $1 }

Term :: { AST.NamedTerm }
  : AppTerm                                                 { $1 }
  | LAMBDA IDENT DOT Term                                   { AST.Abs $2 $4 }                    -- λx. e
  | LAMBDA IDENT COLON Type DOT Term                        { AST.AbsAnn $2 $4 $6 }              -- λx : t. e
  | LAMBDA LBRACE IdentList RBRACE DOT Term                 { AST.AbsUncurry $3 $6 }             -- λ{x, ...}. e
  | LAMBDA LBRACE AnnotList RBRACE DOT Term                 { AST.AbsUncurryAnn $3 $6 }          -- λ{x : t, ...}. e
  | BIGLAM IDENT DOT Term                                   { AST.TAbs $2 $4 }                   -- Λa. e
  | Term COLON Type                                         { AST.Ann $1 $3 }                    -- e : t

AppTerm :: { AST.NamedTerm }
  : AppTerm AtomTerm                                        { AST.App $1 $2 }                    -- e1 e2
  | AppTerm AT Type                                         { AST.TApp $1 $3 }                   -- e @ t
  | AppTerm LBRACE TermList RBRACE                          { AST.AppUncurry $1 $3 }             -- e {e1, ...}
  | FST AtomTerm                                            { AST.Fst $2 }                       -- fst e
  | SND AtomTerm                                            { AST.Snd $2 }                       -- snd e
  | AtomTerm                                                { $1 }

AtomTerm :: { AST.NamedTerm }
  : NAT                                                     { AST.LitInt $1 }                    -- n
  | TRUE                                                    { AST.LitBool True }                 -- true
  | FALSE                                                   { AST.LitBool False }                -- false
  | IDENT                                                   { AST.Var $1 }                       -- x
  | NIL                                                     { AST.Nil }                          -- nil
  | CONS                                                    { AST.Cons }                         -- cons
  | LANGLE Term COMMA Term RANGLE                           { AST.Pair $2 $4 }                   -- <e1, e2>
  | LPAREN Term RPAREN                                      { $2 }                               -- (e)

TermList :: { [AST.NamedTerm] }
  : Term COMMA TermList { $1 : $3 }
  | Term                { [$1] }

IdentList :: { [String] }
  : IDENT COMMA IdentList { $1 : $3 }
  | IDENT                 { [$1] }

AnnotList :: { [(String, AST.NamedTyp)] }
  : IDENT COLON Type COMMA AnnotList { ($1, $3) : $5 }
  | IDENT COLON Type                 { [($1, $3)] }

{
-- ===========================================================
--  Footer: combine lexer + parser
-- ===========================================================
parseTyp :: String -> AST.NamedTyp
parseTyp s = parseTypTokens (lexTokens s)

parseTerm :: String -> AST.NamedTerm
parseTerm s = parseTermTokens (lexTokens s)

happyError :: [Token] -> a
happyError _ = error "parse error"
}