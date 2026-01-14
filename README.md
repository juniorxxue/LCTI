Paper: *Local Contextual Type Inference*. To appear at POPL 2026.

Also check our [online Agda proof*](https://types.hk/proof/lcti/), [preprint](papers/paper.pdf) and [extended version](papers/extended.pdf).
[Artifact Evaluation ver. (Resuable Badge)](https://github.com/juniorxxue/LCTI/tree/popl26ae) contains more details about how to approach the code.

## Abstract
> Type inference is essential for programming languages, yet complete
  and global inference quickly becomes undecidable in the presence of rich type
  systems like System F. Pierce and Turner proposed local type
  inference (LTI) as a scalable,
  partially annotated alternative by relying on information local to
  applications. While LTI has been widely adopted in practice, there
  are significant gaps between theory and practice, with its theory
  being underdeveloped and specifications for LTI being complex and restrictive.
> We propose *Local Contextual Type Inference*, a principled
  redesign of LTI grounded in contextual typing—a recent formalism
  which captures type information flow. We present *Contextual
    System F* (Fc), a variant of System F with implicit and
  first-class polymorphism.  We formalize Fc using a declarative system, prove soundness, completeness, and
  decidability, and introduce matching subtyping as a bridge between
  declarative and algorithmic inference. This work offers the first
  mechanized treatment of LTI, while at the same time removing
  important practical restrictions and also demonstrating the power of
  contextual typing in designing robust, extensible and simple to
  implement type inference algorithms.


## Overview

* `mech/agda`: Agda mechanization of LCTI, including three systems: declarative, intermediate, and algorithmic, along with their metatheories including soundness and completeness proofs.
* `mech/rocq`: Rocq mechanization of the decidability of the algorithmic system.
* `impl`: Haskell implementation of the type inference algorithm.
* `variants`: several variants discussed in related work.

## Try it out

The quickest way to give a taste of LCTI is to try out our Haskell implementation, located in `impl/Poly`.
Use `cabal run Poly` to start the REPL:

```shell
$ cabal run Poly
Welcome to the type inference REPL of Fc. Type :q to quit.
Available commands: :tree, :env, :examples, :tests, :define <name> : <type>
> :define myvar : int -> int
int -> int
> id
forall a. a -> a
> id 1
int
> :tree id 1
> :tree id 1
[Ty-App]  ⊢ ■ ⇒ id 1 ⇒ int
  [Ty-Sub]  ⊢ [1] ↝ ■ ⇒ id ⇒ int -> int
    [Ty-Var]  ⊢ ■ ⇒ id ⇒ forall a. a -> a
    [S-Forall-L] ; ∅ ⊢ forall a. a -> a <: [1] ↝ ■ ⊣ ∅ ⇝ int -> int
      [S-Term-Open] ; ∅, a^ ⊢ a -> a <: [1] ↝ ■ ⊣ ∅, a=int ⇝ int -> int
        [Ty-Int]  ⊢ ■ ⇒ 1 ⇒ int
        [S-MVar-R] ; ∅, a^ ⊢ a ≤- int ⊣ ∅, a=int
        [S-Empty] ; ∅, a=int ⊢ a <: ■ ⊣ ∅, a=int ⇝ int
```

### Available commands

* `:tree <term>`: show the derivation tree of the given term.
* `:env`: show the current environment (we preload some).
* `:examples`: show a list of examples.
* `:tests`: run all examples (failed cases accompanied with translation and errors).
* `:define <name> : <type>`: introduce a new binding.

### Language syntax

```
A, B ::= int                -- integer types
       | bool               -- boolean type
       | a, b, c, ...       -- type variables
       | forall a. A        -- universal quantification
       | A -> B             -- function type
       | A * B              -- product type
       | { A, B, C } -> B   -- uncurried function type
       | [ A ]              -- list type
       | ST A B             -- state type
       | ( A )              -- parentheses

e1, e2 ::= n | true | false       -- literals
         | x                      -- variables
         | e : A                  -- type annotation
         | lambda x. e            -- unannotated lambda abstraction
         | lambda (x : A). e      -- annotated lambda abstraction
         | lambda {x, ...}. e     -- uncurried unannotated lambda abstraction
         | lambda {x : A, ...}. e -- uncurried annotated lambda abstraction
         | Lambda a. e            -- polymorphic lambda abstraction
         | e1 e2                  -- application
         | e {e1, e2, ...}        -- uncurried application
         | e @ A                  -- type application
         | fst e                  -- pair projection
         | snd e                  -- pair projection
         | <e1, e2>               -- pair
         | nil                    -- nil literal
```
--------

*Notes: The Agda HTML template was originally created by [tsung-ju](https://github.com/tsung-ju) and has been adapted for this project.
