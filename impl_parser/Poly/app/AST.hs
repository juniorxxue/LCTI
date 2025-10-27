module AST where

data NamedTyp = TInt | TBool 
              | TVar String 
              | TArr NamedTyp NamedTyp 
              | TForall String NamedTyp 
              | TUncurry [NamedTyp] NamedTyp 
              | TList NamedTyp 
              | TProd NamedTyp NamedTyp 
              | TST NamedTyp NamedTyp 
              deriving (Eq, Show)

data NamedTerm = LitInt Int                           -- natural number n
              | LitBool Bool                          -- true | false
              | Var String                            -- variable x
              | Abs String NamedTerm                  -- λx. e
              | AbsAnn String NamedTyp NamedTerm      -- λx : t. e
              | AbsUncurry [String] NamedTerm         -- λ{x, ...}. e
              | AbsUncurryAnn [(String, NamedTyp)] NamedTerm  -- λ{x : t, ...}. e
              | App NamedTerm NamedTerm               -- e1 e2
              | AppUncurry NamedTerm [NamedTerm]      -- e {e1, ...}
              | Ann NamedTerm NamedTyp                -- e : t
              | TAbs String NamedTerm                 -- Λa. e
              | TApp NamedTerm NamedTyp               -- e @ t
              | Nil                                   -- nil
              | Cons                                  -- cons
              | Pair NamedTerm NamedTerm              -- <e1, e2>
              | Fst NamedTerm                         -- fst e
              | Snd NamedTerm                         -- snd e
              deriving (Eq, Show)