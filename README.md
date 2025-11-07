Paper: *Local Contextual Type Inference*. To appear at POPL 2026.

Also check our [online Agda proof](https://types.hk/proof/lcti/). Preprint and extended version will be available soon.
[Artifact Evaluation ver.](https://github.com/juniorxxue/LCTI/tree/popl26ae) contains more details about how to approach the code.

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