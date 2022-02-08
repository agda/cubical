{-

This file contains a summary of what remains for π₄(S³) ≡ ℤ/2ℤ to be proved.

See the module π₄S³ at the end of this file.

The --experimental-lossy-unification flag is used to speed up type checking.
The file still type checks without it, but it's a lot slower (about 10 times).
-}

{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.Summary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Int renaming (ℤ to Int) hiding (_+_)

open import Cubical.HITs.Sn
open import Cubical.HITs.SetTruncation

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Brunerie
open import Cubical.Homotopy.Whitehead
open import Cubical.Homotopy.Group.Base hiding (π)
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
  renaming (Brunerie to β)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.ZAction

private
  variable
    ℓ : Level

-- TODO: ideally this would not be off by one in the definition of π'Gr
π : ℕ → Pointed ℓ → Group ℓ
π n X = π'Gr (predℕ n) X

-- Nicer notation for the spheres (as pointed types)
𝕊² 𝕊³ : Pointed₀
𝕊² = S₊∙ 2
𝕊³ = S₊∙ 3

-- Whitehead product
[_]× : {X : Pointed ℓ} {n m : ℕ}
     → π' (suc n) X × π' (suc m) X → π' (suc (n + m)) X
[_]× (f , g) = [ f ∣ g ]π'

-- Some type abbreviations (unproved results)
π₄S³≡ℤ/something : GroupEquiv (π 3 𝕊²) ℤ → Type₁
π₄S³≡ℤ/something eq =
  π 4 𝕊³ ≡ ℤ/ abs (eq .fst .fst [ ∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂ ]×)


-- The intended proof:
module π₄S³
  (π₃S²≃ℤ           : GroupEquiv (π 3 𝕊²) ℤ)
  (gen-by-HopfMap   : gen₁-by (π 3 𝕊²) ∣ HopfMap ∣₂)
  (π₄S³≡ℤ/whitehead : π₄S³≡ℤ/something π₃S²≃ℤ)
  (hopfWhitehead    : abs (HopfInvariant-π' 0 ([ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)) ≡ 2)
  where
  -- Package the Hopf invariant up into a group equivalence
  hopfInvariantEquiv' : GroupEquiv (π 3 𝕊²) ℤ
  fst (fst hopfInvariantEquiv') = HopfInvariant-π' 0
  snd (fst hopfInvariantEquiv') =
    GroupEquivℤ-isEquiv (invGroupEquiv π₃S²≃ℤ) ∣ HopfMap ∣₂
                        gen-by-HopfMap (GroupHom-HopfInvariant-π' 0)
                        (abs→⊎ _ _ HopfInvariant-HopfMap)
  snd hopfInvariantEquiv' = snd (GroupHom-HopfInvariant-π' 0)

  -- The two equivalences map [ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]× to
  -- the same number, modulo the sign
  remAbs : abs (groupEquivFun π₃S²≃ℤ [ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)
         ≡ abs (groupEquivFun hopfInvariantEquiv' [ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×)
  remAbs = absGroupEquivℤGroup (invGroupEquiv π₃S²≃ℤ) (invGroupEquiv hopfInvariantEquiv') _

  -- So the image of [ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]× under π₃S²≃ℤ
  -- is 2 (modulo the sign)
  remAbs₂ : abs (groupEquivFun π₃S²≃ℤ [ (∣ idfun∙ _ ∣₂ , ∣ idfun∙ _ ∣₂) ]×) ≡ 2
  remAbs₂ = remAbs ∙ hopfWhitehead

  -- The final result then follows
  π₄S³≡ℤ : π 4 𝕊³ ≡ ℤ/ 2
  π₄S³≡ℤ = π₄S³≡ℤ/whitehead ∙ cong (ℤ/_) remAbs₂

{- Lemma 1 -}
Lemma₁ : GroupEquiv (π'Gr 2 (S₊∙ 2)) ℤ
Lemma₁ = hopfInvariantEquiv

{- Lemma 2 -}
Lemma₂ : gen₁-by (π 3 𝕊²) ∣ HopfMap ∣₂
Lemma₂ = π₂S³-gen-by-HopfMap

{- Lemma 3 -}
Lemma₃ : π₄S³≡ℤ/something hopfInvariantEquiv
Lemma₃ = GroupPath _ _  .fst BrunerieIso

{- Lemma 4 -}
Lemma₄ : β ≡ 2
Lemma₄ = Brunerie≡2

{- And we are done -}
π₄S³≡ℤ/2 : π 4 𝕊³ ≡ (ℤ/ 2)
π₄S³≡ℤ/2 = π₄S³.π₄S³≡ℤ Lemma₁ Lemma₂ Lemma₃ Lemma₄

{- For completeness: π₄S³≡Bool -}
π₄S³≡Bool : π 4 𝕊³ ≡ Bool
π₄S³≡Bool =
    π₄S³≡ℤ/2
  ∙ GroupPath _ _ .fst
     (GroupIso→GroupEquiv ℤ/2≅Bool)
