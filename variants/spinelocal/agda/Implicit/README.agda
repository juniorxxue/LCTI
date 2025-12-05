module Implicit.README where

----------------------------------------------------------------------
--+                           Section 3                            +--
----------------------------------------------------------------------

-- Theorem 3.1 (Reflexivity of Subtyping)
import Implicit.Decl.Typing using (s-refl-∞)

-- Theorem 3.2 (Transitivity of subtyping)
import Implicit.Decl.Trans using (s-trans')

{- compared with IF is not considered in this extension

-- Theorem 3.3 (Soundness to Implicit System F)
import Implicit.Annotatability.Soundness using (sound)

-- Theorem 3.4 (Annotatability to F𝑖)
import Implicit.Annotatability.Corollaries using (annotatability-real)

-- Corollary 3.5 (Annotatability to F𝑖)
import Implicit.Annotatability.Corollaries using (annotatability-real')

-}

----------------------------------------------------------------------
--+                           Section 4                            +--
----------------------------------------------------------------------

-- Theorem 4.1 (Generalized Soundness of Subtyping)
import Implicit.Interm2Decl.Corollaries using (sound')

-- Theorem 4.2 (Generalized Completeness of Subtyping)
import Implicit.Decl2Interm.Corollaries using (complete+'; complete-')

-- Corollary 4.3 (Soundness)
import Implicit.Interm2Decl.Corollaries using (sound0')

-- Corollary 4.3 (Completeness)
import Implicit.Decl2Interm.Corollaries using (complete+0')

----------------------------------------------------------------------
--+                           Section 5                            +--
----------------------------------------------------------------------

-- Lemma 5.1 (Subtyping Inference Implies Environment Extension under types)
import Implicit.Algo.Properties.Regularity using (s-⊆/)

-- Lemma 5.2 2 (Subtyping Checking Implies Environment Extension under types)
import Implicit.Algo.Properties.Extension using (ss+-⊆/; ss--⊆/)

-- Theorem 5.3 & 5.4 (Decidilibty of Typing and Subtyping)
-- Proved in Rocq Prover, check the folder `decidability_coq/`

-- Lemma 5.5 (Soundness of Instantiation)
import Implicit.Algo2Interm.Find using (s-find)

-- Theorem 5.6 (Generalized Soundness of Subtyping)
import Implicit.Algo2Interm.Main using (sound-s)

-- Theorem 5.7 (Generalized Soundness of Typing)
import Implicit.Algo2Interm.Main using (sound)

-- Corollary 5.8 (Soundness of Typing)
import Implicit.Algo2Interm.Corollaries using (sound0; sound∞)

-- Lemma 5.9 (Typing implies Subtyping)
import Implicit.Algo.Properties.Typing2Sub using (⊢to≤)

-- Lemma 5.10 (Subsumption of Algo. Typing)
import Implicit.Algo.Properties.Subsumption using (subsumption0)

-- Theorem 5.11 (Generalized Completeness of Subtyping)
import Implicit.Interm2Algo.Main using (complete-s)

-- Theorem 5.12 (Generalized Completeness of Typing)
import Implicit.Interm2Algo.Corollaries using (complete)

-- Corollary 5.13 (Completeness of Typing)
import Implicit.Interm2Algo.Corollaries using (complete-0; complete-∞)
