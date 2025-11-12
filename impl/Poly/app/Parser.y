{ 
-- ===========================================================
--  Haskell header
-- ===========================================================
module Parser (parseTyp, parseTypTokens, parseTerm, parseTermTokens) where

import qualified Syntax as S
import Lexer
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name (s2n)
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

typ :: { S.Ty }
  : Type EOF { $1 }

-- one production rule: directly allow all forms of type
Type :: { S.Ty }
  : TINTKW                     { S.TInt }                         -- int
  | TBOOLKW                    { S.TBool }                        -- bool
  | IDENT                      { S.TVar (s2n $1) }      -- variable
  | FORALL IDENT DOT Type       { S.TForall (bind (s2n $2) $4) }               -- forall a. t
  | Type ARROW Type            { S.TArr $1 $3 }                   -- t1 -> t2
  | Type STAR Type             { S.TProd $1 $3 }                  -- t1 * t2
  | LBRACE TypeList RBRACE ARROW Type { S.TUncurry $2 $5 }        -- {t1,...} -> t
  | LBRACK Type RBRACK         { S.TList $2 }                     -- [t]
  | TSTKW Type Type            { S.TST $2 $3 }                    -- ST t1 t2
  | LPAREN Type RPAREN         { $2 }                               -- (t)

TypeList :: { [S.Ty] }
  : Type COMMA TypeList { $1 : $3 }
  | Type                { [$1] }

-- ===========================================================
--  Grammar: faithful to NamedTerm
-- ===========================================================

term :: { S.Tm }
  : Term EOF { $1 }

Term :: { S.Tm }
  : AppTerm                                                 { $1 }
  | LAMBDA IDENT DOT Term                                   { S.Abs (bind (s2n $2) $4) }                    -- λx. e
  | LAMBDA IDENT COLON Type DOT Term                        { S.AbsAnn (bind ((s2n $2, Embed $4)) $6) }              -- λx : t. e
  | LAMBDA LPAREN IDENT COLON Type RPAREN DOT Term          { S.AbsAnn (bind ((s2n $3, Embed $5)) $8) }              -- λ(x : t). e
  | LAMBDA LBRACE IdentList RBRACE DOT Term                 { S.AbsUncurry (bind $3 $6) }                                -- λ{x, ...}. e
  | LAMBDA LBRACE AnnotList RBRACE DOT Term                 { S.AbsUncurryAnn (bind $3 $6) }          -- λ{x : t, ...}. e
  | BIGLAM IDENT DOT Term                                   { S.TAbs (bind (s2n $2) $4) }                   -- Λa. e
  | Term COLON Type                                         { S.Ann $1 $3 }                    -- e : t

AppTerm :: { S.Tm }
  : AppTerm AtomTerm                                        { S.App $1 $2 }                    -- e1 e2
  | AppTerm AT Type                                         { S.TApp $1 $3 }                   -- e @ t
  | AppTerm LBRACE TermList RBRACE                          { S.AppUncurry $1 $3 }             -- e {e1, ...}
  | FST AtomTerm                                            { S.Fst $2 }                       -- fst e
  | SND AtomTerm                                            { S.Snd $2 }                       -- snd e
  | AtomTerm                                                { $1 }

AtomTerm :: { S.Tm }
  : NAT                                                     { S.LitInt $1 }                    -- n
  | TRUE                                                    { S.LitBool True }                 -- true
  | FALSE                                                   { S.LitBool False }                -- false
  | IDENT                                                   { S.Var (s2n $1) }         -- x
  | NIL                                                     { S.Nil }                          -- nil
  | LANGLE Term COMMA Term RANGLE                           { S.Pair $2 $4 }                   -- <e1, e2>
  | LPAREN Term RPAREN                                      { $2 }                               -- (e)

TermList :: { [S.Tm] }
  : Term COMMA TermList { $1 : $3 }
  | Term                { [$1] }

IdentList :: { [S.TmName] }
  : IDENT COMMA IdentList { (s2n $1) : $3 }
  | IDENT                 { [s2n $1] }

AnnotList :: { [(S.TmName, Embed S.Ty)] }
  : IDENT COLON Type COMMA AnnotList { (s2n $1, Embed $3) : $5 }
  | IDENT COLON Type                 { [(s2n $1, Embed $3)] }

{
-- ===========================================================
--  Footer: combine lexer + parser
-- ===========================================================
parseTyp :: String -> S.Ty
parseTyp s = parseTypTokens (lexTokens s)

parseTerm :: String -> S.Tm
parseTerm s = parseTermTokens (lexTokens s)

happyError :: [Token] -> a
happyError _ = error "parse error"
}