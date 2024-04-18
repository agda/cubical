{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

Symmetric Monoidal Smash Products in Homotopy Type Theory,
Axel Ljungström, 2024

-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.Papers.SmashProducts where
-- Section 2
import Cubical.WildCat.Base                        as WCat1
import Cubical.WildCat.Instances.Pointed           as WCat2
import Cubical.WildCat.BraidedSymmetricMonoidal    as WCat3
import Cubical.HITs.SmashProduct.Base              as Smash

-- Section 3
import Cubical.Foundations.Pointed.Homogeneous     as Hom

-- Section 5
import Cubical.HITs.SmashProduct.SymmetricMonoidalCat as SM

-- Section 6
import Cubical.HITs.SmashProduct.Induction         as SmashInduction

---- 2 Background ----
--- 2.1 Symmetric monoidal wild categories

-- Definition 1 (Wild categories)
open WCat1 using (WildCat)

-- Proposition 2 (Pointed types form a wild cat)
open WCat2 using (PointedCat)

-- Definition 3 (Monoidal wild categories)
open WCat3 using (isMonoidalWildCat)

-- Definition 4 (Symmetric Monoidal wild categories)
open WCat3 using (SymmetricMonoidalPrecat)

--- 2.2 Smash Products
-- Definition 5 (Smash products -- note: defined as a coproduct in the
-- library. E.g. the ⟨ x , y ⟩ constructor here is simply
-- inr(x,y). Also note that pushₗ and pushᵣ are inverted with this
-- definition.)
open Smash using (_⋀_)

-- Definition 6 (Functorial action of ⋀)
open Smash using (_⋀→_)
-- Proposition 7 (Commutativity of ⋀)
-- Postponed -- stated as part of Theorem 21

---- 3 Associativity ----
-- Definition 8 (Double smash product)
open Smash using (⋀×2)

-- Equivalence between smash product and double smash
open Smash using (Iso-⋀-⋀×2)

-- Proposition 9 (Associativity of ⋀)
-- Postponed -- stated as part of Theorem 21

---- 4 The Heuristic ----
-- Lemma 10 (first induction principle for smash products)
open Smash using (⋀-fun≡)

-- Definition 10
open Smash using (⋀-fun≡)

-- Definition 11 (version using ≡ instead of ≃⋆ is used here)
open Hom using (isHomogeneous)

-- Lemma 12 (Evan's trick)
open Hom using (→∙Homogeneous≡)

-- Lemma 13 (Evan's trick for smash products)
open Smash using (⋀→∙Homogeneous≡)

-- Lemma 14 (Evan's trick smash products, v2)
open Smash using (⋀→Homogeneous≡)

-- Definition 15
open Smash.⋀-fun≡' renaming (Fₗ to L ; Fᵣ to R)

-- Lemma 16
open Smash.⋀-fun≡' using (main)

-- Lemmas 17/18
-- Omitted (used implicitly in formalisation)


---- 5 The symmetric monoidal structure ----
-- Proposition 19/20 (Hexagon and pentagon)
-- Postponed - stated as part of Theorem 21

-- Theorem 21 (Symmetric monoidal structure)
open SM using (⋀Symm)

--- 5.1 Back to Brunerie's thesis
-- This section is only meant to be an informal discussion and has not
-- been formalised, as stated in the paper.

-- 6. A formal statement of the heuristic
-- Definition 25 (FS)
open SmashInduction using (FS)

-- Definition 26 (⋀̃)
open SmashInduction using (⋀̃)

-- Theorem 27 (⋀̃→⋀ induction with coherences)
open SmashInduction using (⋀̃→⋀-ind ; ⋀̃→⋀-ind-coh)

-- Corollary 28 (⋀̃→⋀ induction without)
open SmashInduction using (⋀̃→⋀-ind)

-- Corollary 29 (⋀̃→⋀ induction for pointed maps)
open SmashInduction using (⋀̃→⋀-ind∙)
