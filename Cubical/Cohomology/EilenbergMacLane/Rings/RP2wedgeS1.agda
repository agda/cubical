{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RP2wedgeS1 where

open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2wedgeS1
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.Groups.Wedge
open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle


open import Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.EilenbergMacLane1 hiding (elimProp ; elimSet)
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout as PO
open import Cubical.HITs.S1 renaming (rec to S¹Fun)
open import Cubical.HITs.Sn
open import Cubical.HITs.RPn
open import Cubical.HITs.Wedge

-- rUnitGroupIso

open AbGroupStr

RP²∙ : Pointed ℓ-zero
RP²∙ = RP² , point

RP²∨S¹ = RP²∙ ⋁ (S₊∙ 1)

gen-RP²₁-raw : RP² → EM ℤ/2 1
gen-RP²₁-raw =
  RP²Fun embase (emloop 1) (emloop-inv (ℤGroup/ 2) 1)

RP²∨S¹-elim' : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2))) → RP²∨S¹ → EM ℤ/2 2
RP²∨S¹-elim' p (inl x) = RP²Fun (0ₖ 2) refl p x
RP²∨S¹-elim' p (inr x) = 0ₖ 2
RP²∨S¹-elim' p (push a i) = 0ₖ 2

gen-RP²₂-raw : RP² → EM ℤ/2 2
gen-RP²₂-raw =
  RP²Fun (0ₖ 2) refl (Iso.inv Iso-Ω²K₂-ℤ/2 1)

α-raw : RP²∨S¹ → EM ℤ/2 1
α-raw (inl x) = gen-RP²₁-raw x
α-raw (inr x) = embase
α-raw (push a i) = embase

β-raw : RP²∨S¹ → EM ℤ/2 1
β-raw (inl x) = embase
β-raw (inr x) = S¹Fun embase (emloop 1) x
β-raw (push a i) = embase

α : coHom 1 ℤ/2 RP²∨S¹
α = ∣ α-raw ∣₂

β : coHom 1 ℤ/2 RP²∨S¹
β = ∣ β-raw ∣₂

α↦1' : fst (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) α ≡ (1 , 0)
α↦1' = refl

β↦1' : fst (fst H¹[RP²∨S¹,ℤ/2]≅ℤ/2×ℤ/2) β ≡ (0 , 1)
β↦1' = refl

genH²-raw : RP²∨S¹ → EM ℤ/2 2
genH²-raw = RP²∨S¹-elim' (Iso.inv Iso-Ω²K₂-ℤ/2 1)

genH²-raw⨂ : RP²∨S¹ → EM (ℤ/2 ⨂ ℤ/2) 2
genH²-raw⨂ (inl x) = RP²Fun (0ₖ 2) refl (ℤ/2→Ω²K₂⨂ 1) x
genH²-raw⨂ (inr x) = 0ₖ 2
genH²-raw⨂ (push a i) = 0ₖ 2

RP²Fun⨂ : RP²Fun (0ₖ 2) refl {!!} ≡ {!ℤ/2→Ω²K₂⨂ 1!}
RP²Fun⨂ = {!!}


TensorMult-genH²-raw⨂ : (x : _)
  → EMTensorMult {G'' = CommRing→Ring ℤ/2CommRing} 2 (genH²-raw⨂ x)
   ≡ genH²-raw x
TensorMult-genH²-raw⨂ (inl point) = refl
TensorMult-genH²-raw⨂ (inl (line i)) = refl
TensorMult-genH²-raw⨂ (inl (square i j)) = {!!}
  where
  l : {!genH²-raw (inl (square i j))!}
  l = {!!}
TensorMult-genH²-raw⨂ (inr x) = refl
TensorMult-genH²-raw⨂ (push a i) = refl

genH² : coHom 2 ℤ/2 RP²∨S¹
genH² = ∣ genH²-raw ∣₂

genH²↦1 : fst (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2) genH² ≡ 1
genH²↦1 = genH²↦1' _ refl
  where
  -- silly lemma for faster type checking
  genH²↦1' : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2)))
    → (p ≡ Iso.inv Iso-Ω²K₂-ℤ/2 1)
    → fst (fst H²[RP²∨S¹,ℤ/2]≅ℤ/2) (∣ RP²∨S¹-elim' p ∣₂) ≡ 1
  genH²↦1' p q =
      H²[RP²,ℤ/2]→ℤ/2-Id p
    ∙ cong (Iso.fun Iso-Ω²K₂-ℤ/2) q
    ∙ Iso.rightInv Iso-Ω²K₂-ℤ/2 1

private
  K[ℤ₂⊗ℤ₂,2] = EM (ℤ/2 ⨂ ℤ/2) 2
  K∙[ℤ₂⊗ℤ₂,2] = EM∙ (ℤ/2 ⨂ ℤ/2) 2

  cp : EM ℤ/2 1 → EM ℤ/2 1 → K[ℤ₂⊗ℤ₂,2]
  cp = _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}


β²-raw : (x : RP²∨S¹) → cp (β-raw x) (β-raw x) ≡ 0ₖ 2
β²-raw (inl x) = refl
β²-raw (inr base) = refl
β²-raw (inr (loop i)) j = cong₂-⌣ (emloop 1) j i
β²-raw (push a i) = refl

αβ-raw : (x : RP²∨S¹) → cp (α-raw x) (β-raw x) ≡ 0ₖ 2
αβ-raw (inl x) = ⌣ₖ-0ₖ⊗ 1 1 (gen-RP²₁-raw x)
αβ-raw (inr x) = 0ₖ-⌣ₖ⊗ 1 1 (S¹Fun embase (emloop (fsuc fzero)) x)
αβ-raw (push a i) = refl

βα-raw : (x : RP²∨S¹) → cp (β-raw x) (α-raw x) ≡ 0ₖ 2
βα-raw (inl x) = 0ₖ-⌣ₖ⊗ 1 1 (gen-RP²₁-raw x)
βα-raw (inr x) = ⌣ₖ-0ₖ⊗ 1 1 (S¹Fun embase (emloop (fsuc fzero)) x)
βα-raw (push a i) = refl

CC : Cube (λ j k → ∣ north ∣) (λ j k → ∣ north ∣)
          (λ i k → cong₂-⌣ (emloop 1) k (~ i)) (λ i k → cong₂-⌣ (emloop 1) k i)
          (λ i j → cp (emloop-inv (ℤGroup/ 2) 1 (~ j) i) (emloop-inv (ℤGroup/ 2) 1 (~ j) i))
          λ i j → ℤ/2→Ω²K₂⨂ 1 j i
CC i j k = ▣₇ i j k

Typ : (p : fst ((Ω^ 2) K∙[ℤ₂⊗ℤ₂,2])) → Type
Typ p =
  Cube (λ j k → cong₂-⌣ (emloop 1) k j)
       (λ j k → cong₂-⌣ (emloop (fsuc fzero)) k (~ j))
       (λ _ _ → ∣ north ∣) (λ _ _ → ∣ north ∣)
       ((λ i j → cp (emloop-inv (ℤGroup/ 2) 1 i j) (emloop-inv (ℤGroup/ 2) 1 i j)))
       p

CC' : Typ (ℤ/2→Ω²K₂⨂ (fsuc fzero))
CC' = subst Typ (sym (ℤ/2→Flip₁ 1 1)) λ i j k → ▣₇ j (~ i) k

α²-raw : (x : RP²∨S¹) → cp (α-raw x) (α-raw x) ≡ genH²-raw⨂ x
α²-raw (inl point) = refl
α²-raw (inl (line i)) j = cong₂-⌣ (emloop 1) j i
α²-raw (inl (square i j)) k = CC' i j k
α²-raw (inr x) = refl
α²-raw (push a i) = refl
