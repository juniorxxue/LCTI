{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Derivation where

import Control.Applicative (Alternative(..))
import Control.Monad.Error.Class (MonadError(..))

-------------------------------------------------------------------------------
-- Core Data Structure
-------------------------------------------------------------------------------

-- | A derivation tree: each node has a rule name, conclusion, and premises
data Derivation = Derivation
  { dRule       :: String       -- ^ Rule name, e.g., "[S-Arr]"
  , dConclusion :: String       -- ^ Judgment as string
  , dPremises   :: [Derivation] -- ^ Sub-derivations (premises)
  } deriving (Eq)

-- | A result paired with its derivation
data Derived a = Derived
  { result :: a
  , deriv  :: Derivation
  } deriving (Eq, Functor)

-------------------------------------------------------------------------------
-- Smart Constructors
-------------------------------------------------------------------------------

-- | Axiom: a derivation with no premises
axiom :: String -> String -> a -> Derived a
axiom rule concl x = Derived x (Derivation rule concl [])

-- | Unary rule: one premise
unary :: String -> String -> Derived a -> b -> Derived b
unary rule concl (Derived _ d) x = Derived x (Derivation rule concl [d])

-- | Binary rule: two premises
binary :: String -> String -> Derived a -> Derived b -> c -> Derived c
binary rule concl (Derived _ d1) (Derived _ d2) x =
  Derived x (Derivation rule concl [d1, d2])

-- | Ternary rule: three premises
ternary :: String -> String -> Derived a -> Derived b -> Derived c -> d -> Derived d
ternary rule concl (Derived _ d1) (Derived _ d2) (Derived _ d3) x =
  Derived x (Derivation rule concl [d1, d2, d3])

-- | N-ary rule: arbitrary number of premises
rule :: String -> String -> [Derivation] -> a -> Derived a
rule ruleName concl premises x = Derived x (Derivation ruleName concl premises)

-------------------------------------------------------------------------------
-- Monadic Combinators
-------------------------------------------------------------------------------

-- | Lift a pure Derived into a monad
pureD :: Monad m => Derived a -> m (Derived a)
pureD = return

-- | Create an axiom in a monad
axiomM :: Monad m => String -> String -> a -> m (Derived a)
axiomM rule concl x = return $ axiom rule concl x

-- | Unary rule in monadic context
--   Usage: unaryM "[Rule]" conclusion premise $ \a -> return result
unaryM :: Monad m
       => String                        -- ^ Rule name
       -> m (Derived a)                 -- ^ Premise computation
       -> (a -> String)                 -- ^ Conclusion from result
       -> (a -> m b)                    -- ^ Body using premise result
       -> m (Derived b)
unaryM ruleName premise mkConcl body = do
  Derived a d <- premise
  b <- body a
  return $ Derived b (Derivation ruleName (mkConcl a) [d])

-- | Binary rule in monadic context (sequential: second may depend on first)
binaryM :: Monad m
        => String                       -- ^ Rule name
        -> m (Derived a)                -- ^ First premise
        -> (a -> m (Derived b))         -- ^ Second premise (may use first result)
        -> (a -> b -> String)           -- ^ Conclusion from results
        -> (a -> b -> m c)              -- ^ Body using both results
        -> m (Derived c)
binaryM ruleName prem1 prem2 mkConcl body = do
  Derived a d1 <- prem1
  Derived b d2 <- prem2 a
  c <- body a b
  return $ Derived c (Derivation ruleName (mkConcl a b) [d1, d2])

-- | Ternary rule in monadic context
ternaryM :: Monad m
         => String
         -> m (Derived a)
         -> (a -> m (Derived b))
         -> (a -> b -> m (Derived c))
         -> (a -> b -> c -> String)
         -> (a -> b -> c -> m d)
         -> m (Derived d)
ternaryM ruleName p1 p2 p3 mkConcl body = do
  Derived a d1 <- p1
  Derived b d2 <- p2 a
  Derived c d3 <- p3 a b
  d <- body a b c
  return $ Derived d (Derivation ruleName (mkConcl a b c) [d1, d2, d3])

-------------------------------------------------------------------------------
-- Alternative: Builder-style Derivation
--
-- For complex rules where you want to accumulate premises imperatively
-------------------------------------------------------------------------------

-- | A derivation builder that accumulates premises
data DerivBuilder a = DerivBuilder
  { dbResult   :: a
  , dbPremises :: [Derivation]  -- Accumulated in reverse order
  }

instance Functor DerivBuilder where
  fmap f (DerivBuilder a ps) = DerivBuilder (f a) ps

-- | Start building a derivation
startBuild :: a -> DerivBuilder a
startBuild a = DerivBuilder a []

-- | Add a premise to the builder
addPremise :: DerivBuilder a -> Derived b -> DerivBuilder a
addPremise (DerivBuilder a ps) (Derived _ d) = DerivBuilder a (d : ps)

-- | Finish building: create final Derived value
finishBuild :: String -> String -> DerivBuilder a -> Derived a
finishBuild ruleName concl (DerivBuilder a ps) =
  Derived a (Derivation ruleName concl (reverse ps))

-- | Update the result in the builder
withResult :: b -> DerivBuilder a -> DerivBuilder b
withResult b (DerivBuilder _ ps) = DerivBuilder b ps

-------------------------------------------------------------------------------
-- Convenience: Do-notation style with implicit premise tracking
-------------------------------------------------------------------------------

-- | Run a derivation-building computation
--   Usage pattern:
--     derive "[S-Arr]" $ do
--       senv1 <- premise $ ssub ...
--       senv2 <- premise $ ssub ...
--       conclude (showJudgment senv2)
--       return senv2

newtype DerivM m a = DerivM { unDerivM :: m (a, [Derivation]) }

instance Functor m => Functor (DerivM m) where
  fmap f (DerivM m) = DerivM $ fmap (\(a, ds) -> (f a, ds)) m

instance Monad m => Applicative (DerivM m) where
  pure a = DerivM $ return (a, [])
  DerivM mf <*> DerivM ma = DerivM $ do
    (f, ds1) <- mf
    (a, ds2) <- ma
    return (f a, ds1 ++ ds2)

instance Monad m => Monad (DerivM m) where
  DerivM ma >>= f = DerivM $ do
    (a, ds1) <- ma
    (b, ds2) <- unDerivM (f a)
    return (b, ds1 ++ ds2)

instance MonadFail m => MonadFail (DerivM m) where
  fail = DerivM . fail

instance (Monad m, Alternative m) => Alternative (DerivM m) where
  empty = DerivM empty
  DerivM ma <|> DerivM mb = DerivM (ma <|> mb)

instance MonadError e m => MonadError e (DerivM m) where
  throwError = DerivM . throwError
  catchError (DerivM m) h = DerivM $ catchError m (unDerivM . h)

-- | Run a sub-computation and record its derivation as a premise
premise :: Monad m => m (Derived a) -> DerivM m a
premise m = DerivM $ do
  Derived a d <- m
  return (a, [d])

-- | Lift a plain monadic computation (no derivation recorded)
liftD :: Monad m => m a -> DerivM m a
liftD m = DerivM $ do
  a <- m
  return (a, [])

-- | Complete a derivation with a rule name and conclusion
derive :: Monad m => String -> String -> DerivM m a -> m (Derived a)
derive ruleName concl (DerivM m) = do
  (a, premises) <- m
  return $ Derived a (Derivation ruleName concl premises)

-- | Like derive but conclusion is computed from the result
deriveWith :: Monad m => String -> (a -> String) -> DerivM m a -> m (Derived a)
deriveWith ruleName mkConcl (DerivM m) = do
  (a, premises) <- m
  return $ Derived a (Derivation ruleName (mkConcl a) premises)

-------------------------------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------------------------------

-- | Render derivation as indented text (like current Log output)
showDerivation :: Derivation -> String
showDerivation = unlines . go 0
  where
    go indent (Derivation r c ps) =
      (replicate indent ' ' ++ r ++ " " ++ c) : concatMap (go (indent + 2)) ps

-- | Render as inference rule (bottom-up style)
showDerivationTree :: Derivation -> String
showDerivationTree d = unlines $ renderTree d
  where
    renderTree (Derivation r c []) = [r ++ " " ++ c]
    renderTree (Derivation r c ps) =
      let premiseLines = concatMap renderTree ps
          width = maximum (map length premiseLines ++ [length c + length r + 1])
          line = replicate width '─'
      in premiseLines ++ [line, r ++ " " ++ c]

-- | Colorized output (reuse existing color functions)
showDerivationColor :: (String -> String)  -- grey
                    -> (String -> String)  -- bold
                    -> Derivation -> String
showDerivationColor grey bold = unlines . go 0
  where
    go indent (Derivation r c ps) =
      (replicate indent ' ' ++ grey r ++ " " ++ bold c) : concatMap (go (indent + 2)) ps

-------------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------------

-- | Extract just the result, discarding derivation
justResult :: Derived a -> a
justResult = result

-- | Extract just the derivation
justDeriv :: Derived a -> Derivation
justDeriv = deriv

-- | Map over the result while keeping derivation
mapResult :: (a -> b) -> Derived a -> Derived b
mapResult = fmap

-- | Combine multiple derivations under a single rule (for fold patterns)
combineDerivations :: String -> String -> [Derived a] -> [a] -> Derived [a]
combineDerivations ruleName concl deriveds results =
  Derived results (Derivation ruleName concl (map deriv deriveds))
