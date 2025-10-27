module AST where

data NamedTyp = TInt | TBool 
              | TVar String 
              | TArr NamedTyp NamedTyp 
              | TForall String NamedTyp 
              | TUncurry [NamedTyp] NamedTyp 
              | TList NamedTyp 
              | TProd NamedTyp NamedTyp 
              | TST NamedTyp NamedTyp 
              deriving (Eq)

instance Show NamedTyp where
  show TInt = "int"
  show TBool = "bool"
  show (TVar name) = name
  show (TArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TForall name t) = "(forall " ++ name ++ ". " ++ show t ++ ")"
  show (TUncurry ts t) = "(" ++ show ts ++ " -> " ++ show t ++ ")"
  show (TList t) = "[" ++ show t ++ "]"
  show (TProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
  show (TST t1 t2) = "(ST " ++ show t1 ++ " " ++ show t2 ++ ")"  

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

-- named environments
data NamedEnv = EEmpty | ETrm String NamedTyp NamedEnv | EUvar String NamedEnv | EEvar String NamedEnv | ESvar String NamedTyp NamedEnv

instance Show NamedEnv where
  show EEmpty = "·"
  show (ETrm name ty env) = show env ++ ", \n" ++ name ++ " : " ++ show ty
  show (EUvar name env) = show env ++ ", " ++ "U" ++ name
  show (EEvar name env) = show env ++ ", " ++ "E" ++ name
  show (ESvar name ty env) = show env ++ ", " ++ "S" ++ name ++ " : " ++ show ty