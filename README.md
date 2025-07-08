# Supplementary materials of the paper "Local Contextual Type Inference"

We include mechanized proofs and implementations in this repository. They are categorized into three main directories:

## Core System

### Mechanized Proofs

* `proof_core/main_agda/`: the main proof of the paper, written in Agda. It includes the formalization of the declarative system, the intermediate system (including matching subtyping), the algorithmic system and implicit system F, with all the lemmas and theorems shown in the paper, except for the decidability of the algorithm.

You can run `make` in the `proof_core/main_agda/` directory to compile the Agda files, which requires `agda` and its standard library installed. We also provide a nicely rendered html version of the main proof in `proof_core/main_agda/html/Implicit.Paper.html`, which is a recommended way to read the proof.

* `proof_core/decidability_coq`: the decidability proof of the algorithmic system, written in Rocq Prover, you can run `make` in the `proof_core/decidability_coq/Dec` directory to compile the Rocq files, which requires `coq` installed, and `CoqHammer` library. We also include the rendered html version of the decidability proof in `proof_core/decidability_coq/html/toc.html` for easy reading.

### Implementations

## Right-to-Left Variant

## Systems with Top and Bottom Types