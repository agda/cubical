{-

This file contains a summary of what remains for π₄(S³) ≡ ℤ/2ℤ to be proved.

See the module π₄S³ at the end of this file.

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

open import Cubical.Homotopy.Group.Base hiding (π)
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Whitehead
open import Cubical.Homotopy.Whitehead
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.Pi4S3.Tricky

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
[_]× : {X : Pointed ℓ} {n m : ℕ} → π' (suc n) X × π' (suc m) X → π' (suc (n + m)) X
[_]× (f , g) = [ f ∣ g ]π'

-- the Brunerie number
Brunerie : ℕ
Brunerie =
  abs (HopfInvariant-π' 0  [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π')

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

-- We will now instantiate the module.
-- The "actual" construction which pops out from the sequence
-- π₃S³→π₃S²→π₄S³→0
Brunerie' : ℕ
Brunerie' =
  abs (HopfInvariant-π' 0
       (fst (π'∘∙Hom 2 (fold∘W , refl))
         (Iso.inv (fst (πₙ'Sⁿ≅ℤ 2)) 1)))

-- Of course, they are equal
Brunerie'≡Brunerie : Brunerie' ≡ Brunerie
Brunerie'≡Brunerie = λ i → abs (HopfInvariant-π' 0 (h i))
  where
  h : fst (π'∘∙Hom 2 (fold∘W , refl))
         (Iso.inv (fst (πₙ'Sⁿ≅ℤ 2)) 1)
     ≡ [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π'
  h = cong (fst (π'∘∙Hom 2 (fold∘W , refl)))
           (cong (Iso.inv (fst (πₙ'Sⁿ≅ℤ 2))) (sym (πₙ'Sⁿ≅ℤ-idfun∙ 2))
           ∙ (Iso.leftInv (fst (πₙ'Sⁿ≅ℤ 2)) ∣ idfun∙ (S₊∙ 3) ∣₂))
    ∙ fold∘W≡Whitehead
    ∙ cong ∣_∣₂ (sym ([]≡[]₂ (idfun∙ (S₊∙ 2)) (idfun∙ (S₊∙ 2))))

-- And we get an iso π₄S³≅ℤ/nℤ for some n.
BrunerieIso : GroupEquiv (π 4 𝕊³) (ℤ/ Brunerie)
BrunerieIso =
  transport (λ i → GroupEquiv (GroupPath _ _ .fst π₄S³≅π₃coFib-fold∘W∙ (~ i))
            (ℤ/ Brunerie'≡Brunerie i))
            BrunerieIso₁
  where
  BrunerieIso₁ :
    GroupEquiv (π'Gr 2 coFib-fold∘W∙)
               (ℤ/ Brunerie')
  BrunerieIso₁ =
    (invGroupEquiv
      (GroupEquivℤ/abs-gen
        (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
          (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))
          (invGroupEquiv hopfInvariantEquiv)
          (π'∘∙Hom 2 (fold∘W , refl))
          _
          S³→S²→Pushout→Unit))

Brunerie≡2 : Brunerie ≡ 2
Brunerie≡2 = HopfInvariantWhitehead

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
Lemma₄ : Brunerie ≡ 2
Lemma₄ = Brunerie≡2

{- And we are done -}
π₄S³≡ℤ/2 : π 4 𝕊³ ≡ (ℤ/ 2)
π₄S³≡ℤ/2 = π₄S³.π₄S³≡ℤ Lemma₁ Lemma₂ Lemma₃ Lemma₄
