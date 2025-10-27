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