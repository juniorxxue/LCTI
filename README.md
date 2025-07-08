# Supplementary Materials for "Local Contextual Type Inference"

This repository contains mechanized proofs and implementations organized into three main directories:

## Core System

### Mechanized Proofs

* `proof_core/main_agda/`: Contains the main proof, written in Agda. This includes formalization of the declarative system, intermediate system (with matching subtyping), algorithmic system, and implicit system F, along with all lemmas and theorems presented in the paper, except for the decidability of the algorithm.

To compile the Agda files, run `make` in the `proof_core/main_agda/` directory. This requires `agda` and its standard library to be installed. We also provide a rendered HTML version of the main proof at `proof_core/main_agda/html/Implicit.README.html`, which is the recommended way to read the proof. In particular, `README.agda` or `README.html` states all the lemmas and theorem presented in the paper in order, and shows their corresponding code in Agda.

* `proof_core/decidability_coq/`: Contains the decidability proof of the algorithmic system, written in Rocq Prover. 

To compile the Rocq files, run `make` in the `proof_core/decidability_coq/Dec` directory. This requires `coq` and the `CoqHammer` library to be installed. We also include a rendered HTML version of the decidability proof at `proof_core/decidability_coq/html/toc.html` for convenient reading.

### Implementations

* `impl_core/`: Contains the Haskell implementation of the algorithmic system, including all examples shown in the paper and appendix table. Running `cabal run` will print all derivations for the examples.

## Right-to-Left Variant

The proof for the right-to-left variant is located in `proof_variant_right2left/`, containing all results equivalent to the main proof.

The implementation of the right-to-left variant is in `impl_variant_right2left/`.

## Systems with Top and Bottom Types

We also provide a proof that extends the declarative system and matching subtyping with top and bottom types, with all related properties proven, located in `proof_core_top_bot/`.