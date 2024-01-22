{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle where

open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Ring
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.Susp

open PlusBis
open Iso

private
  K[ℤ₂⊗ℤ₂,2] = EM (ℤ/2 ⨂ ℤ/2) 2
  K∙[ℤ₂⊗ℤ₂,2] = EM∙ (ℤ/2 ⨂ ℤ/2) 2

  cp : EM ℤ/2 1 → EM ℤ/2 1 → K[ℤ₂⊗ℤ₂,2]
  cp = _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}

-- generators of H¹(K²,ℤ/2)
module K²gen where
  α-raw : KleinBottle → EM ℤ/2 1
  α-raw = KleinFun embase (emloop 1) refl
           (flipSquare (sym (emloop-inv (ℤGroup/ 2) 1)))

  β-raw : KleinBottle → EM ℤ/2 1
  β-raw = KleinFun embase refl (emloop 1) (λ _ i → emloop 1 i)

  α : coHom 1 ℤ/2 KleinBottle
  α = ∣ α-raw ∣₂

  β : coHom 1 ℤ/2 KleinBottle
  β = ∣ β-raw ∣₂

----- an important homotopy for examining the squares α² and β² -----
cong₂-⌣ : (p : fst (Ω (EM∙ ℤ/2 1))) → cong₂ cp p p ≡ refl
cong₂-⌣ p = cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
          ∙∙ (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                    ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)
          ∙∙ sym (rUnit refl)

-- Goal: Relate cong sym (cong₂-⌣ (sym p)) to cong₂-⌣ p
-- We show that they are equal up to an instance of the
-- following family of paths
Res : ∀ {ℓ} {A B : Type ℓ} {x y : A} (f : A → A → B)
  → (p : x ≡ y)
  → sym (cong (λ x₁ → f x₁ y) (sym p) ∙ cong (f x) (sym p))
   ≡ cong (λ x₁ → f x₁ x) p ∙ cong (f y) p
Res {x = x} {y = y} f p i j =
  hcomp (λ k → λ {(i = i0) → compPath-filler (cong (λ x₁ → f x₁ y) (sym p))
                                (cong (f x) (sym p)) k (~ j)
                 ; (i = i1) → compPath-filler (cong (λ x₁ → f x₁ x) p)
                                (cong (f y) p) k j
                 ; (j = i0) → f x (p (~ k ∧ ~ i))
                 ; (j = i1) → f y (p (k ∨ ~ i))})
        (f (p j) (p (~ i)))

Res-refl : ∀ {ℓ} {A B : Type ℓ} {x : A} (f : A → A → B)
      → Res {x = x} f refl ≡ refl
Res-refl {x = x} f k i j =
  hcomp (λ r → λ {(i = i0) → compPath-filler (λ _ → f x x) refl r (~ j)
                 ; (i = i1) → compPath-filler (λ _ → f x x) refl r (~ j)
                 ; (j = i0) → f x x
                 ; (j = i1) → f x x
                 ; (k = i1) → compPath-filler (λ _ → f x x) refl r (~ j)})
        (f x x)

cong₂Funct-cong-sym : ∀ {ℓ} {A B : Type ℓ} {x y : A}
     (p : x ≡ y) (f : A → A → B)
  → cong₂Funct f p p ∙ sym (Res f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p))
cong₂Funct-cong-sym {A = A} {B = B} =
  J (λ y p → (f : A → A → B) → cong₂Funct f p p ∙ sym (Res f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p)))
        λ f → (λ i → cong₂Funct f refl refl ∙ sym (Res-refl f i))
              ∙ sym (rUnit _)

Res⌣ : (p : Path (EM ℤ/2 1) embase embase)
  → sym (cong (λ x₁ → cp x₁ embase) (sym p) ∙ cong (cp embase) (sym p))
   ≡ cong (λ x₁ → cp x₁ embase) p ∙ cong (cp embase) p
Res⌣ p = cong sym (sym (rUnit (cong (λ x₁ → cp x₁ embase) (sym p))))
     ∙∙ (λ i j → cp (p j) (p (~ i)))
     ∙∙ rUnit _

-- main result
sym-cong₂-⌣≡ : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong sym (cong₂-⌣ (sym p))
  ≡ (((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p))
  ∙∙ (sym (Res⌣ p) {- <-- New factor, everything else the same as cong₂-⌣ -}
    ∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)))
  ∙∙ sym (rUnit refl))
sym-cong₂-⌣≡ p =
    main
  ∙ lem (cong₂Funct cp p p) (sym (Res⌣ p)) (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
  ∙ (λ j → cp embase (p j))) (sym (rUnit refl))
  where
  lem : ∀ {ℓ} {A : Type ℓ} {x y z w t : A}
       (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ t)
    → ((p ∙ q) ∙∙ r ∙∙ s) ≡ (p ∙∙ (q ∙ r) ∙∙ s)
  lem p q r s i = compPath-filler p q (~ i) ∙∙ compPath-filler' q r i ∙∙ s

  main :
       cong sym (cong₂-⌣ (sym p))
    ≡ ((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
     ∙ sym (Res⌣ p))
    ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
    ∙∙ sym (rUnit refl))
  main i = (cong₂Funct-cong-sym p cp (~ i)
    ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
    ∙∙ sym (rUnit refl))

----- Some functions into Ω²K(G,2) with properties ------
ℤ/2×ℤ/2→Ω²K₂⨂ : (x y : fst ℤ/2) → fst ((Ω^ 2) (K∙[ℤ₂⊗ℤ₂,2]))
ℤ/2×ℤ/2→Ω²K₂⨂ x y =
  sym (EM→ΩEM+1-0ₖ 1)
  ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (x ⊗ y))
  ∙∙ EM→ΩEM+1-0ₖ 1

ℤ/2→Ω²K₂⨂ : fst ℤ/2 → fst ((Ω^ 2) (K∙[ℤ₂⊗ℤ₂,2]))
ℤ/2→Ω²K₂⨂ g = ℤ/2×ℤ/2→Ω²K₂⨂ g g

ℤ/2→Ω²K₂' : fst ℤ/2 → fst ((Ω^ 2) (EM∙ ℤ/2 2))
ℤ/2→Ω²K₂' g =
  sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 g) ∙∙ EM→ΩEM+1-0ₖ 1

ℤ/2→Flip₁ : (x y : fst ℤ/2)
  → (ℤ/2×ℤ/2→Ω²K₂⨂ x y) ≡ sym (ℤ/2×ℤ/2→Ω²K₂⨂ y x)
ℤ/2→Flip₁ x y i j =
  hcomp (λ k → λ {(j = i0) → EM→ΩEM+1-0ₖ 1 k
                 ; (j = i1) → EM→ΩEM+1-0ₖ 1 k})
         (main i j)
  where
  lem : (x y : _) → Path (ℤ/2 ⨂₁ ℤ/2) (x ⊗ y) (y ⊗ x)
  lem = ℤ/2-elim (ℤ/2-elim refl (⊗AnnihilL 1 ∙ sym (⊗AnnihilR 1)))
            (ℤ/2-elim (⊗AnnihilR 1 ∙ sym (⊗AnnihilL 1)) refl)

  lem₂ : (x y : _)
    → GroupStr.inv (snd (AbGroup→Group (ℤ/2 ⨂ ℤ/2))) (y ⊗ x) ≡ x ⊗ y
  lem₂ x y = cong (_⊗ x) (-Const-ℤ/2 y) ∙ lem y x

  main : cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (emloop (x ⊗ y))
       ≡ cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (sym (emloop (y ⊗ x)))
  main = cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1))
          (cong emloop (sym (lem₂ x y)))
       ∙ cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1))
          (emloop-inv (AbGroup→Group (ℤ/2 ⨂ ℤ/2)) (y ⊗ x))

ℤ/2→Flip₂ : ℤ/2→Ω²K₂⨂ 1 ≡ λ k i → ℤ/2→Ω²K₂⨂ 1 k (~ i)
ℤ/2→Flip₂ = ℤ/2→Flip₁ 1 1 ∙ sym≡cong-sym (ℤ/2→Ω²K₂⨂ 1)

ℤ/2→Flip₃ : ℤ/2→Ω²K₂⨂ 1 ≡ flipSquare (ℤ/2→Ω²K₂⨂ 1)
ℤ/2→Flip₃ = ℤ/2→Flip₂ ∙∙ sym (sym≡cong-sym (ℤ/2→Ω²K₂⨂ 1))
                        ∙∙ sym≡flipSquare (ℤ/2→Ω²K₂⨂ 1)

------ Characterising the cup product -------

-- Showing K²gen.β ⌣ K²gen.β = 0 is trivial by cong₂-⌣
KleinFun-β⊗ : (x : KleinBottle)
  → cp (K²gen.β-raw x) (K²gen.β-raw x) ≡ ∣ north ∣ₕ
KleinFun-β⊗ point = refl
KleinFun-β⊗ (line1 i) = refl
KleinFun-β⊗ (line2 i) j = cong₂-⌣ (emloop 1) j i
KleinFun-β⊗ (square i j) k = cong₂-⌣ (emloop 1) k j

-- Showing K²gen.α ⌣ K²gen.β = 1 is also straightforward
KleinFun-βα⊗ : (x : KleinBottle)
  → cp (K²gen.β-raw x) (K²gen.α-raw x)
   ≡ KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂⨂ 1) x
KleinFun-βα⊗ point = refl
KleinFun-βα⊗ (line1 i) k = ∣ north ∣
KleinFun-βα⊗ (line2 i) = ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 i)
KleinFun-βα⊗ (square i j) k =
  hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → cp (emloop 1 j) (K²gen.α-raw (square i (j ∧ r)))
                 ; (k = i1) → (ℤ/2→Ω²K₂⨂ 1) i j})
    (hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → doubleCompPath-filler
                                (sym (EM→ΩEM+1-0ₖ 1))
                                (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1)))
                                (EM→ΩEM+1-0ₖ 1) (~ r) (~ i) j
                 ; (k = i1) → (ℤ/2→Ω²K₂⨂ 1) i j})
        (ℤ/2→Flip₁ 1 1 (~ k) i j))

-- Showing that α ⌣ α = 1 is the hardest part. The fact that it's non-zero
-- comes from the fact that the term Res⌣ falls out at some point
-- (see sym-cong₂-⌣≡). Here's a bunch of cubes we'll need...
private
  ▣₁ : (i k r : I) → K[ℤ₂⊗ℤ₂,2]
  ▣₁ i k r =
    hcomp (λ j →
      λ {(i = i0) → ∣ north ∣
       ; (i = i1) → ∣ north ∣
       ; (k = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
       ; (k = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
       ; (r = i0) → ℤ/2→Ω²K₂⨂ 1 k i
       ; (r = i1) → doubleCompPath-filler
                      (sym (EM→ΩEM+1-0ₖ 1))
                      (λ i j → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) j)
                      (EM→ΩEM+1-0ₖ 1) (~ j) k (~ i) })
           (ℤ/2→Flip₂ r k i)

  ▣₂ : (i k r : I) → K[ℤ₂⊗ℤ₂,2]
  ▣₂ i k r =
    hcomp (λ j →
        λ {(i = i0) → ∣ north ∣
         ; (i = i1) → ∣ north ∣
         ; (k = i0) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)
         ; (k = i1) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)})
     (▣₁ i k r)

  ▣₃ : (i k r : I) → K[ℤ₂⊗ℤ₂,2]
  ▣₃ i k r =
    hcomp (λ j →
       λ {(i = i0) →  ∣ north ∣
        ; (i = i1) →  ∣ north ∣
        ; (k = i0) → ((λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r))
                     ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) (~ r)) (~ i)
        ; (k = i1) → ((λ k → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j))
                      ∙ λ k → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j)) (~ i)
        ; (r = i0) → (sym (rUnit refl)
                   ∙∙ ℤ/2→Ω²K₂⨂ 1
                   ∙∙ rUnit refl) k i
        ; (r = i1) → compPath-filler (sym (Res⌣ (emloop 1)))
                       (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i)
                       j k (~ i)})
    (▣₂ i k r)

  ▣₄ : (i k r : I) → K[ℤ₂⊗ℤ₂,2]
  ▣₄ i k r =
    hcomp (λ j →
     λ {(i = i0) → ∣ north ∣
      ; (i = i1) → ∣ north ∣
      ; (k = i1) → rUnit (λ _ → cp embase embase) (~ j) i
      ; (r = i0) → doubleCompPath-filler
                     (sym (rUnit (λ _ → cp embase embase)))
                     (ℤ/2→Ω²K₂⨂ 1)
                     (rUnit (λ _ → cp embase embase)) (~ j) k i
      ; (r = i1) → doubleCompPath-filler
                       (cong₂Funct cp (emloop 1) (emloop 1))
                       (sym (Res⌣ (emloop 1))
                       ∙ (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i))
                      (sym (rUnit refl)) j k (~ i)})
     (▣₃ i k r)

  ▣₅ : I → I → I → K[ℤ₂⊗ℤ₂,2]
  ▣₅ i j k =
    hcomp (λ r →
           λ {(i = i0) → ∣ north ∣
            ; (i = i1) → ∣ north ∣
            ; (j = i0) → cong₂-⌣ (emloop 1) (~ r ∨ k) (~ i)
            ; (j = i1) → ▣₄ i k r
            ; (k = i0) → cong₂-⌣ (emloop 1) (~ r) (~ i)
            ; (k = i1) → ℤ/2→Ω²K₂⨂ 1 j i})
            (ℤ/2→Ω²K₂⨂ 1 (j ∧ k) i)

  ▣₆ : I → I → I → K[ℤ₂⊗ℤ₂,2]
  ▣₆ i j k =
    hcomp (λ r →
           λ {(i = i0) → ∣ north ∣
            ; (i = i1) → ∣ north ∣
            ; (j = i0) → cong₂-⌣ (λ i₁ → K²gen.α-raw (line1 i₁)) k (~ i)
            ; (j = i1) → sym-cong₂-⌣≡ (emloop 1) (~ r) k (~ i)
            ; (k = i0) → cp (emloop 1 (~ i)) (emloop 1 (~ i))
            ; (k = i1) → ℤ/2→Ω²K₂⨂ 1 j i})
            (▣₅ i j k)

▣₇ : I → I → I → K[ℤ₂⊗ℤ₂,2]
▣₇ i j k =
  hcomp (λ r →
        λ {(i = i0) → ∣ north ∣
         ; (i = i1) → ∣ north ∣
         ; (j = i0) → cong₂-⌣ (λ i₁ → K²gen.α-raw (line1 i₁)) k (~ i)
         ; (j = i1) → cong₂-⌣ (λ i₁ → K²gen.α-raw (square i₁ r)) k i
         ; (k = i0) → cp (K²gen.α-raw (square i (j ∧ r)))
                          (K²gen.α-raw (square i (j ∧ r)))
         ; (k = i1) → ℤ/2→Ω²K₂⨂ 1 j i})
         (▣₆ i j k)

KleinFun-α⊗ : (x : KleinBottle)
  → cp (K²gen.α-raw x) (K²gen.α-raw x)
   ≡ KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂⨂ 1) x
KleinFun-α⊗ x =
  KleinFunα' x ∙ λ i → KleinFun (0ₖ 2) refl refl (ℤ/2→Flip₃ (~ i)) x
  where
  KleinFunα' : (x : KleinBottle)
    → cp (K²gen.α-raw x) (K²gen.α-raw x)
     ≡ KleinFun (0ₖ 2) refl refl (flipSquare (ℤ/2→Ω²K₂⨂ 1)) x
  KleinFunα' point = refl
  KleinFunα' (line1 i) k = cong₂-⌣ (cong K²gen.α-raw line1) k i
  KleinFunα' (line2 i) = refl
  KleinFunα' (square i j) k = ▣₇ i j k

-- Some lemmas for transferring our results over to H*(K²,ℤ/2)
KleinFun-ℤ/2→Ω²K₂⨂ : (x : KleinBottle)
  → (KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂⨂ 1) x)
   ≡ KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase)
      (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x
KleinFun-ℤ/2→Ω²K₂⨂ point = refl
KleinFun-ℤ/2→Ω²K₂⨂ (line1 i) = refl
KleinFun-ℤ/2→Ω²K₂⨂ (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
KleinFun-ℤ/2→Ω²K₂⨂ (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k)

KleinFun-ℤ/2→Ω²K₂' : (x : KleinBottle)
  → (KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂' 1) x)
   ≡ KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase)
     (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x
KleinFun-ℤ/2→Ω²K₂' point = refl
KleinFun-ℤ/2→Ω²K₂' (line1 i) = refl
KleinFun-ℤ/2→Ω²K₂' (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
KleinFun-ℤ/2→Ω²K₂' (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop 1 i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop 1 i) k)

KleinFun-EMTensorMult : (x : _)
  → EMTensorMult {G'' = ℤ/2Ring} 2
      (KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase)
       (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x)
   ≡ KleinFun (0ₖ 2) refl (EM→ΩEM+1 1 embase)
       (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x
KleinFun-EMTensorMult point = refl
KleinFun-EMTensorMult (line1 i) = refl
KleinFun-EMTensorMult (line2 i) k =
  ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2)
          (merid embase) (sym (merid embase)) k i ∣ₕ
KleinFun-EMTensorMult (square i j) k =
  ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2)
           (merid (emloop (1 ⊗ 1) i)) (sym (merid embase)) k j ∣ₕ

KleinFun-EMTensorMult-const : (x : _)
  → EMTensorMult {G'' = ℤ/2Ring} 2 ∣ north ∣
    ≡ (KleinFun (0ₖ 2) refl refl refl x)
KleinFun-EMTensorMult-const point = refl
KleinFun-EMTensorMult-const (line1 i) = refl
KleinFun-EMTensorMult-const (line2 i) = refl
KleinFun-EMTensorMult-const (square i j) = refl


ℤ/2→Ω²K₂'≡ : ℤ/2→Ω²K₂ 1 ≡ ℤ/2→Ω²K₂' 1
ℤ/2→Ω²K₂'≡ k i j =
  hcomp (λ r → λ {(i = i0) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                 ; (i = i1) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣ })
        (EM→ΩEM+1 1 (EM→ΩEM+1 0 1 i) j)

-- Commutativity of ⌣ in dimensions of interest
-- Todo: remove when graded commutativity for general ⌣ is done
module _ where
  private
    ⌣∙-comm : (x : EM ℤ/2 1)
      → cup∙ {G' = ℤ/2} {H' = ℤ/2} 1 1 x
      ≡ ((λ y → cp y x) , (0ₖ-⌣ₖ⊗ 1 1 x))
    ⌣∙-comm =
      EM-raw'-elim ℤ/2 1 (λ _ → isOfHLevel↑∙ 1 0 _ _)
        λ x → →∙Homogeneous≡ (isHomogeneousEM _)
          (funExt λ y → funExt⁻ (cong fst (flipped y)) x)
      where
      flipped : (y : EM ℤ/2 1)
        → Path (EM-raw'∙ ℤ/2 1 →∙ K∙[ℤ₂⊗ℤ₂,2])
                ((λ x → cp (EM-raw'→EM ℤ/2 1 x) y) , refl)
                ((λ x → cp y (EM-raw'→EM ℤ/2 1 x)) , ⌣ₖ-0ₖ⊗ 1 1 y)
      flipped = EM-raw'-elim _ 1 (λ _ → isOfHLevel↑∙' 1 1 _ _)
              λ x → →∙Homogeneous≡ (isHomogeneousEM 2)
               (funExt λ y → main y x)
        where
        main : (x y : EM₁-raw (ℤGroup/ 2))
          → cp (EM-raw'→EM ℤ/2 1 x) (EM-raw'→EM ℤ/2 1 y)
          ≡ cp (EM-raw'→EM ℤ/2 1 y) (EM-raw'→EM ℤ/2 1 x)
        main embase-raw embase-raw = refl
        main embase-raw (emloop-raw g i) = sym (⌣ₖ-0ₖ⊗ 1 1 (emloop g i))
        main (emloop-raw g i) embase-raw = ⌣ₖ-0ₖ⊗ 1 1 (emloop g i)
        main (emloop-raw g i) (emloop-raw h j) k =
          hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                         ; (i = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                         ; (j = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                         ; (j = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                         ; (k = i0) → doubleCompPath-filler
                                        (sym (EM→ΩEM+1-0ₖ 1))
                                        (λ j i → EM→ΩEM+1 1
                                                   (EM→ΩEM+1 0 (g ⊗ h) j) i)
                                        (EM→ΩEM+1-0ₖ 1) (~ r) j i
                         ; (k = i1) → doubleCompPath-filler
                                        (sym (EM→ΩEM+1-0ₖ 1))
                                        (λ j i → EM→ΩEM+1 1
                                                   (EM→ΩEM+1 0 (h ⊗ g) j) i)
                                        (EM→ΩEM+1-0ₖ 1) (~ r) i j})
                (help k i j)
          where
          help : flipSquare (ℤ/2×ℤ/2→Ω²K₂⨂ g h) ≡ ℤ/2×ℤ/2→Ω²K₂⨂ h g
          help = sym (sym≡flipSquare (ℤ/2×ℤ/2→Ω²K₂⨂ g h))
               ∙ cong sym (ℤ/2→Flip₁ g h)

  ⌣ₖ⊗-commℤ/2₁,₁ : (x y : EM ℤ/2 1) → cp x y ≡ cp y x
  ⌣ₖ⊗-commℤ/2₁,₁ x y i = ⌣∙-comm x i .fst y

  ⌣ₖ-commℤ/2₁,₁ : (x y : EM ℤ/2 1)
    → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} x y ≡ (y ⌣ₖ x)
  ⌣ₖ-commℤ/2₁,₁ x y = cong (EMTensorMult 2) (⌣ₖ⊗-commℤ/2₁,₁ x y)

  ⌣-commℤ/2₁,₁ : ∀ {ℓ} {A : Type ℓ} (x y : coHom 1 ℤ/2 A)
    → (_⌣_ {G'' = ℤ/2Ring} x y) ≡ (y ⌣ x)
  ⌣-commℤ/2₁,₁ =
    ST.elim2 (λ _ _ → isSetPathImplicit)
     λ f g → cong ∣_∣₂ (funExt λ x → ⌣ₖ-commℤ/2₁,₁ (f x) (g x))

  ⌣ₖ⊗-commℤ/2-base : (n : ℕ) (x : ℤ/2 .fst) (y : EM ℤ/2 n)
    → PathP (λ i → EM ℤ/2 (PlusBis.+'-comm 0 n i))
             (_⌣ₖ_ {G'' = ℤ/2Ring} {n = zero} {m = n} x y)
             (_⌣ₖ_ {G'' = ℤ/2Ring} {n = n} {m = zero} y x)
  ⌣ₖ⊗-commℤ/2-base n =
      ℤ/2-elim (λ y → 0ₖ-⌣ₖ 0 n y
             ◁ ((λ i → 0ₖ (PlusBis.+'-comm 0 n i))
             ▷ sym (⌣ₖ-0ₖ n 0 y)))
               (λ y → 1ₖ-⌣ₖ n y
               ◁ (λ i → transp (λ j →  EM ℤ/2 (PlusBis.+'-comm 0 n (i ∧ j)))
                                (~ i) y)
               ▷ sym (⌣ₖ-1ₖ n y))

⌣-comm-Klein : (n m : ℕ)
  (x : coHom n ℤ/2 KleinBottle) (y : coHom m ℤ/2 KleinBottle)
  → PathP (λ i → coHom (PlusBis.+'-comm n m i) ℤ/2 KleinBottle)
           (_⌣_ {G'' = ℤ/2Ring} x y)
           (_⌣_ {G'' = ℤ/2Ring} y x)
⌣-comm-Klein zero m =
  ST.elim2 (λ _ _ → isOfHLevelPathP 2 squash₂ _ _ )
    λ f g i → ∣ (λ x → ⌣ₖ⊗-commℤ/2-base m (f x) (g x) i) ∣₂
⌣-comm-Klein (suc n) zero x y =
  transport (λ j → PathP
      (λ i → coHom (isSetℕ _ _
        (sym (PlusBis.+'-comm zero (suc n)))
        (PlusBis.+'-comm (suc n) zero) j i) ℤ/2 KleinBottle)
      (_⌣_ {G'' = ℤ/2Ring} x y) (_⌣_ {G'' = ℤ/2Ring} y x))
      λ i → ⌣-comm-Klein zero (suc n) y x (~ i)
⌣-comm-Klein (suc zero) (suc zero) = ⌣-commℤ/2₁,₁
⌣-comm-Klein (suc zero) (suc (suc m)) x y =
  isProp→PathP
    (λ j → isContr→isProp
      (transport (λ i → isContr (coHom
        (PlusBis.+'-comm 1 (suc (suc m)) (j ∧ i)) ℤ/2 KleinBottle))
        (isContr-HⁿKleinBottle m ℤ/2))) _ _
⌣-comm-Klein (suc (suc n)) (suc m) x y =
  isProp→PathP
    (λ j → isContr→isProp
      (transport (λ i → isContr (coHom
        (PlusBis.+'-comm (suc (suc n)) (suc m) (i ∧ j)) ℤ/2 KleinBottle))
        (isContr-HⁿKleinBottle _ ℤ/2))) _ _

------ Main results ------
α↦1 : H¹K²→ℤ/2×ℤ/2 K²gen.α ≡ (1 , 0)
α↦1 = refl

β↦0,1 : H¹K²→ℤ/2×ℤ/2 K²gen.β ≡ (0 , 1)
β↦0,1 = refl

α²↦1 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.α K²gen.α) ≡ 1
α²↦1 = cong H²K²→ℤ/2 cupIdα ∙ ℤ/2→H²K²→ℤ/2 1
  where
  almostα : (x : KleinBottle)
    → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} (K²gen.α-raw x) (K²gen.α-raw x)
     ≡ KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂ 1) x
  almostα x = cong (EMTensorMult {G'' = ℤ/2Ring} 2)
               (KleinFun-α⊗ x ∙ KleinFun-ℤ/2→Ω²K₂⨂ x)
          ∙∙ KleinFun-EMTensorMult x
          ∙∙ sym (KleinFun-ℤ/2→Ω²K₂' x)
           ∙ λ i → KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂'≡ (~ i)) x

  cupIdα : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.α K²gen.α
         ≡ ℤ/2→H²K² 1
  cupIdα = cong ∣_∣₂ (funExt almostα)

β²↦0 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.β K²gen.β) ≡ 0
β²↦0 = cong H²K²→ℤ/2 cupIdΒ ∙ ℤ/2→H²K²→ℤ/2 0
  where
  ℤ/2→Ω²K₂-refl : ℤ/2→Ω²K₂ 0 ≡ refl
  ℤ/2→Ω²K₂-refl = Iso.leftInv Iso-Ω²K₂-ℤ/2 refl

  cupIdΒ : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.β K²gen.β
         ≡ ∣ KleinFun (0ₖ 2) refl refl (ℤ/2→Ω²K₂ 0) ∣₂
  cupIdΒ = cong ∣_∣₂ (funExt λ x →
      cong (EMTensorMult {G'' = ℤ/2Ring} 2) (KleinFun-β⊗ x)
    ∙ KleinFun-EMTensorMult-const x
    ∙ λ i → KleinFun ∣ north ∣ refl refl (ℤ/2→Ω²K₂-refl (~ i)) x)

βα↦1 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.β K²gen.α) ≡ 1
βα↦1 =
  cong H²K²→ℤ/2 (cong ∣_∣₂ (funExt
    (λ x → cong (EMTensorMult {G'' = ℤ/2Ring} 2)
             (KleinFun-βα⊗ x ∙ KleinFun-ℤ/2→Ω²K₂⨂ x)
        ∙∙ (KleinFun-EMTensorMult x  ∙ sym (KleinFun-ℤ/2→Ω²K₂' x))
        ∙∙ λ i → KleinFun ∣ north ∣ refl refl (ℤ/2→Ω²K₂'≡ (~ i)) x)))
      ∙ ℤ/2→H²K²→ℤ/2 1

αβ↦1 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.α K²gen.β) ≡ 1
αβ↦1 = cong H²K²→ℤ/2 (⌣-commℤ/2₁,₁ K²gen.α K²gen.β) ∙ βα↦1

--------- Part 2: Show H*(K²,ℤ/2) ≅ ℤ/2[X,Y]/<X³,Y²,XY+X²> ----------

-- some abbreviations
open RingStr renaming (_+_ to _+r_ ; _·_ to _·r_)
private
   ℤ/2[X,Y] : CommRing ℓ-zero
   ℤ/2[X,Y] = PolyCommRing ℤ/2CommRing 2

   ℤ/2[X,Y]R = CommRing→Ring ℤ/2[X,Y]

   -Z/2 = -_ (snd ℤ/2[X,Y]R)
   _·Z/2_ = _·r_ (snd ℤ/2[X,Y]R)

   _⌣'_ = _·r_ (snd (H*R ℤ/2Ring KleinBottle))

   α⌣α = _⌣_ {G'' = ℤ/2Ring} K²gen.α K²gen.α
   α⌣β = _⌣_ {G'' = ℤ/2Ring} K²gen.α K²gen.β

-- Some abstract stuff for faster type checking
abstract
  H²[K²,ℤ/2]≅ℤ/2* : AbGroupEquiv (coHomGr 2 ℤ/2 KleinBottle) ℤ/2
  H²[K²,ℤ/2]≅ℤ/2* = H²[K²,ℤ/2]≅ℤ/2

  H²[K²,ℤ/2]≅ℤ/2*≡ : H²[K²,ℤ/2]≅ℤ/2* ≡ H²[K²,ℤ/2]≅ℤ/2
  H²[K²,ℤ/2]≅ℤ/2*≡ = refl

  α²↦1' : fst (fst (H²[K²,ℤ/2]≅ℤ/2*)) α⌣α ≡ 1
  α²↦1' = α²↦1

  αβ↦1' : fst (fst (H²[K²,ℤ/2]≅ℤ/2*)) α⌣β ≡ 1
  αβ↦1' = αβ↦1



-- some lemmas
module _ where
  -≡id-ℤ/2[X,Y] : (x : fst ℤ/2[X,Y]) → -Z/2 x ≡ x
  -≡id-ℤ/2[X,Y] = DS-Ind-Prop.f _ _ _ _
    (λ _ → is-set (snd ℤ/2[X,Y]R) _ _)
    refl
    (λ r a → cong (base r) (-Const-ℤ/2  _))
    λ {x} {y} p q → GroupTheory.invDistr (Ring→Group ℤ/2[X,Y]R) x y
                  ∙ addComm _ _
                  ∙ cong₂ _add_ p q

  +Trivℤ/2[X,Y] : (x : fst ℤ/2[X,Y]) → x add x ≡ neutral
  +Trivℤ/2[X,Y] x = cong (x add_ ) (sym (-≡id-ℤ/2[X,Y] x))
                   ∙ +InvR (snd ℤ/2[X,Y]R) x

  -ConstH* : ∀ {ℓ} {A : Type ℓ} → (x : fst (H*R ℤ/2Ring A))
    → -_ (snd (H*R ℤ/2Ring A)) x ≡ x
  -ConstH* {A = A} = DS-Ind-Prop.f _ _ _ _
    (λ _ → trunc _ _)
    refl
    (λ r a → cong (base r) (-ₕConst-ℤ/2 r a))
    λ {x} {y} ind1 ind2 → RingTheory.-Dist (H*R ℤ/2Ring A) x y
                        ∙ cong₂ _add_ ind1 ind2

  +TrivH* : ∀ {ℓ} {A : Type ℓ}
    → (x : fst (H*R ℤ/2Ring A)) → x add x ≡ neutral
  +TrivH* {A = A} x = cong (x add_) (sym (-ConstH* x))
               ∙ +InvR (snd (H*R ℤ/2Ring A)) x

-- Construction of the equivalent polynomial ring
<X³,Y²,XY+X²> : FinVec (fst ℤ/2[X,Y]) 3
<X³,Y²,XY+X²> zero = base (3 ∷ (0 ∷ [])) 1
<X³,Y²,XY+X²> one = base (0 ∷ (2 ∷ [])) 1
<X³,Y²,XY+X²> two = base (1 ∷ (1 ∷ [])) 1 add base (2 ∷ (0 ∷ [])) 1

ℤ/2[X,Y]/<X³,Y²,XY+X²> : CommRing ℓ-zero
ℤ/2[X,Y]/<X³,Y²,XY+X²> = PolyCommRing-Quotient ℤ/2CommRing <X³,Y²,XY+X²>

private
  _·Z/_ = _·r_ (snd (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>))

  makeHomℤ[X,Y] : ∀ {ℓ'} {R : Ring ℓ'} (f : fst ℤ/2[X,Y] → fst R)
    → IsRingHom (snd (CommRing→Ring ℤ/2[X,Y])) f (snd R)
    → f (base (3 ∷ (0 ∷ [])) 1) ≡ 0r (snd R)
    → f (base (0 ∷ (2 ∷ [])) 1) ≡ 0r (snd R)
    → f ((base (1 ∷ (1 ∷ [])) 1) add (base (2 ∷ (0 ∷ [])) 1)) ≡ 0r (snd R)
    → RingHom (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>) R
  makeHomℤ[X,Y] {R = R} f ishom id1 id2 id3 = (λ x → fst k x)
    , makeIsRingHom (IsRingHom.pres1 (snd k))
                    (λ x y → IsRingHom.pres+ (snd k) x y)
                    λ x y → IsRingHom.pres· (snd k) x y
    where
    -- verbose definition (speeds up type checking a bit)
    k = Quotient-FGideal-CommRing-Ring.inducedHom
      ℤ/2[X,Y]
      R
      (f , ishom)
      <X³,Y²,XY+X²>
      λ { zero → id1 ; one → id2 ; two → id3}

-- Inclusion of basics

HⁿKlein→ℤ/2[X,Y]/I : (n : ℕ)
  → coHom n ℤ/2 KleinBottle → fst ℤ/2[X,Y]/<X³,Y²,XY+X²>
HⁿKlein→ℤ/2[X,Y]/I zero a =
  [ base (0 ∷ 0 ∷ []) (H⁰[K²,ℤ/2]≅ℤ/2 .fst .fst a) ]
HⁿKlein→ℤ/2[X,Y]/I one a =
    [ base (1 ∷ 0 ∷ [])  (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst .fst a .fst)
  add base (0 ∷ 1 ∷ [])  (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst .fst a .snd) ]
HⁿKlein→ℤ/2[X,Y]/I two a =
  [ base (2 ∷ 0 ∷ []) (H²[K²,ℤ/2]≅ℤ/2* .fst .fst a) ]
HⁿKlein→ℤ/2[X,Y]/I (suc (suc (suc n))) _ = [ neutral ]

-- xⁿ ↦ ... : Hⁿ(K²,ℤ/2)
incL : (x : ℕ) → coHom x ℤ/2 KleinBottle
incL zero = 1ₕ {G'' = ℤ/2Ring}
incL one = K²gen.α
incL two = α⌣α
incL (suc (suc (suc n))) = 0ₕ _

-- yⁿ ↦ ... : Hⁿ(K²,ℤ/2)
incR : (x : ℕ) → coHom x ℤ/2 KleinBottle
incR zero = 1ₕ {G'' = ℤ/2Ring}
incR one = K²gen.β
incR (suc (suc n)) = 0ₕ _

-- Map ℤ/2[X,Y] → H*(K²,ℤ/2)
ℤ/2[X,Y]→H*Klein-fun : fst ℤ/2[X,Y] → fst (H*R ℤ/2Ring KleinBottle)
ℤ/2[X,Y]→H*Klein-fun = DS-Rec-Set.f _ _ _ _
  trunc neutral
  (λ x y → mainFun y x)
  _add_ addAssoc addRid addComm
  (λ _ → refl)
  λ r a b → lem a b r
  where
  mainFun : Cubical.Data.Fin.Fin 2
     → (r : Vec ℕ 2)
     → fst (H*R ℤ/2Ring KleinBottle)
  mainFun =
    ℤ/2-rec (λ _ → neutral)
             λ {(x ∷ y ∷ []) → base (x +' y) (incL x ⌣ incR y)}

  lem : (a b : Cubical.Data.Fin.Fin 2) (r : Vec ℕ 2)
    → (mainFun a r add mainFun b r)
     ≡ mainFun ((snd (CommRing→Ring ℤ/2CommRing) +r a) b) r
  lem =
    ℤ/2-elim
     (ℤ/2-elim
     (λ r → addRid _)
      λ r → +IdL (snd (H*R ℤ/2Ring KleinBottle)) (mainFun 1 r))
     (ℤ/2-elim
     (λ r → +IdR (snd (H*R ℤ/2Ring KleinBottle)) (mainFun 1 r))
      λ r → +TrivH* (mainFun 1 r))

-- Homomorphism proof
isHomℤ/2[X,Y]→H*Klein :
  IsRingHom (snd ℤ/2[X,Y]R)
            ℤ/2[X,Y]→H*Klein-fun
            (snd (H*R ℤ/2Ring KleinBottle))
isHomℤ/2[X,Y]→H*Klein = makeIsRingHom refl (λ _ _ → refl)
  (DS-Ind-Prop.f _ _ _ _
    (λ _ → isPropΠ λ _ → trunc _ _)
    (λ y → cong ℤ/2[X,Y]→H*Klein-fun
             (RingTheory.0LeftAnnihilates ℤ/2[X,Y]R y)
           ∙ sym (RingTheory.0LeftAnnihilates (H*R ℤ/2Ring KleinBottle)
              (ℤ/2[X,Y]→H*Klein-fun y)))
    (λ r a
      → DS-Ind-Prop.f _ _ _ _
          (λ _ → trunc _ _)
          (cong ℤ/2[X,Y]→H*Klein-fun
            (RingTheory.0RightAnnihilates (ℤ/2[X,Y]R) (base r a))
          ∙ sym (RingTheory.0RightAnnihilates (H*R ℤ/2Ring KleinBottle) _))
       (λ r2 a2 → lem a a2 r r2)
         λ ind ind2
           → cong₂ (_+r_ (snd (H*R ℤ/2Ring KleinBottle))) ind ind2
                  ∙ sym (·DistR+ (snd (H*R ℤ/2Ring KleinBottle)) _ _ _))
    λ ind ind2 y
      → cong₂ (_+r_ (snd (H*R ℤ/2Ring KleinBottle))) (ind y) (ind2 y))
  where
  lem : (a b : fst ℤ/2) (r s : Vec ℕ 2)
    → ℤ/2[X,Y]→H*Klein-fun (base r a ·Z/2 base s b)
    ≡ (ℤ/2[X,Y]→H*Klein-fun (base r a) ⌣' ℤ/2[X,Y]→H*Klein-fun (base s b))
  lem =
    ℤ/2-elim
    (ℤ/2-elim
     (λ r s
       → cong ℤ/2[X,Y]→H*Klein-fun (base-neutral _)
        ∙ cong₂ _⌣'_
           (cong ℤ/2[X,Y]→H*Klein-fun (sym (base-neutral r)))
           (cong ℤ/2[X,Y]→H*Klein-fun (sym (base-neutral s))))
     λ r s
       → cong ℤ/2[X,Y]→H*Klein-fun
                (cong (_·Z/2 (base s 1)) (base-neutral _))
            ∙ cong (_⌣' ℤ/2[X,Y]→H*Klein-fun (base s 1))
              (cong ℤ/2[X,Y]→H*Klein-fun (sym (base-neutral r))))
    (ℤ/2-elim
     (λ r s → cong ℤ/2[X,Y]→H*Klein-fun
                (cong (base r 1 ·Z/2_) (base-neutral s))
             ∙ sym (RingTheory.0RightAnnihilates
                   (H*R ℤ/2Ring KleinBottle)
                   (ℤ/2[X,Y]→H*Klein-fun (base r 1)))
             ∙ cong (ℤ/2[X,Y]→H*Klein-fun (base r 1) ⌣'_)
                    (cong ℤ/2[X,Y]→H*Klein-fun (sym (base-neutral s))))
     1-1-case)
     where
     PathP-lem : (n m : ℕ) (p : n ≡ m)
       (x : coHom n ℤ/2 KleinBottle) (y : coHom m ℤ/2 KleinBottle)
       → PathP (λ i → coHom (p i) ℤ/2 KleinBottle) x y
       → Path (H*R ℤ/2Ring KleinBottle .fst) (base n x) (base m y)
     PathP-lem n = J> λ x → J> refl

     incR-pres⌣ : (n m : ℕ)
               → incR (n +' m) ≡ (_⌣_ {G'' = ℤ/2Ring} (incR n) (incR m))
     incR-pres⌣ zero m = sym (1ₕ-⌣ m (incR m))
     incR-pres⌣ one zero =
       sym (transportRefl (incR 1)) ∙ sym (⌣-1ₕ 1 (incR one))
     incR-pres⌣ one one =
          sym (IsGroupHom.pres1 (snd (invGroupEquiv H²[K²,ℤ/2]≅ℤ/2)))
       ∙∙ sym (cong (ℤ/2→H²K²) β²↦0)
       ∙∙ H²K²→ℤ/2→H²K² (_⌣_ {G'' = ℤ/2Ring} K²gen.β K²gen.β)
     incR-pres⌣ one (suc (suc m)) =
       isContr→isProp (isContr-HⁿKleinBottle m ℤ/2) _ _
     incR-pres⌣ (suc (suc n)) zero =
         sym (transportRefl (incR (2 + n)))
       ∙ sym (⌣-1ₕ (suc (suc n)) (incR (suc (suc n))))
     incR-pres⌣ (suc (suc n)) (suc m) =
       sym (0ₕ-⌣ (suc (suc n)) (suc m) (incR (suc m)))

     incL-pres⌣ : (n m : ℕ)
       → incL (n +' m) ≡ _⌣_ {G'' = ℤ/2Ring} (incL n) (incL m)
     incL-pres⌣ zero m = sym (1ₕ-⌣ m (incL m))
     incL-pres⌣ one zero =
       sym (transportRefl (incL 1)) ∙ sym (⌣-1ₕ 1 (incL one))
     incL-pres⌣ one one = refl
     incL-pres⌣ one (suc (suc m)) =
       isContr→isProp (isContr-HⁿKleinBottle m ℤ/2) _ _
     incL-pres⌣ two zero =
       sym (transportRefl (incL 2)) ∙ sym (⌣-1ₕ 2 (incL 2))
     incL-pres⌣ two (suc m) =
       isContr→isProp (isContr-HⁿKleinBottle m ℤ/2) _ _
     incL-pres⌣ (suc (suc (suc n))) m =
       isContr→isProp (subst (λ n → isContr (coHom n ℤ/2 KleinBottle))
          (sym (+'≡+ (3 + n) m))
          (isContr-HⁿKleinBottle (n + m) ℤ/2)) _ _

     1-1-case : (r s : Vec ℕ 2)
      → ℤ/2[X,Y]→H*Klein-fun (base r 1 ·Z/2 base s 1)
       ≡ (ℤ/2[X,Y]→H*Klein-fun (base r 1)
      ⌣'  ℤ/2[X,Y]→H*Klein-fun (base s 1))
     1-1-case (x ∷ y ∷ []) (x2 ∷ y2 ∷ []) =
        (λ i → base ((+'≡+ x x2 (~ i)) +' (+'≡+ y y2 (~ i)))
             (incL (+'≡+ x x2 (~ i)) ⌣ incR (+'≡+ y y2 (~ i))))
       ∙ cong (base ((x +' x2) +' (y +' y2)))
              (cong₂ _⌣_ (incL-pres⌣ x x2) (incR-pres⌣ y y2))
       ∙ PathP-lem _ _ (sym (+'-assoc x x2 (y +' y2))) _ _
           (assoc⌣Dep x x2 (y +' y2) (incL x) (incL x2) (incR y ⌣ incR y2))
       ∙ PathP-lem _ _ (cong (x +'_) (+'-assoc x2 y y2)) _ _
             (λ i → _⌣_ {G'' = ℤ/2Ring} (incL x)
              (assoc⌣Dep x2 y y2 (incL x2) (incR y) (incR y2) (~ i)))
       ∙ PathP-lem _ _ (λ i → x +' ((+'-comm x2 y i) +' y2)) _ _
          (λ i → _⌣_ {G'' = ℤ/2Ring} (incL x)
                 (_⌣_ {G'' = ℤ/2Ring}
                  (⌣-comm-Klein x2 y (incL x2) (incR y) i) (incR y2)))
       ∙ PathP-lem _ _ (cong (x +'_) (sym (+'-assoc y x2 y2))) _ _
          (λ i → _⌣_ {G'' = ℤ/2Ring} (incL x)
           (assoc⌣Dep y x2 y2 (incR y) (incL x2) (incR y2) i))
       ∙ PathP-lem _ _ (+'-assoc x y (x2 +' y2)) _ _
          (λ i → assoc⌣Dep x y (x2 +' y2) (incL x) (incR y)
            (_⌣_ {G'' = ℤ/2Ring} (incL x2) (incR y2)) (~ i))

-- Induced map ℤ/2[X,Y]/I → H*(K²,ℤ/2)
ℤ/2[X,Y]/I→H*Klein :
  RingHom (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)
          (H*R ℤ/2Ring KleinBottle)
ℤ/2[X,Y]/I→H*Klein =
  makeHomℤ[X,Y]
    ℤ/2[X,Y]→H*Klein-fun
    isHomℤ/2[X,Y]→H*Klein
    (base-neutral _) (base-neutral _)
    (IsRingHom.pres+ isHomℤ/2[X,Y]→H*Klein
      (base (1 ∷ (1 ∷ [])) 1) (base (2 ∷ (0 ∷ [])) 1)
    ∙ base-add 2 _ _
    ∙ cong (base 2)
       (cong₂ (_+ₕ_) αβ≡
             (⌣-1ₕ 2 (incL 2) ∙ transportRefl (incL 2))
       ∙ +ₕ≡id-ℤ/2 2 (_⌣_ {G'' = ℤ/2Ring} K²gen.α K²gen.α))
    ∙ base-neutral 2)
  where
  αβ≡ : α⌣β ≡ α⌣α
  αβ≡ = sym (H²K²→ℤ/2→H²K² (_⌣_ {G'' = ℤ/2Ring} K²gen.α K²gen.β))
     ∙∙ cong ℤ/2→H²K² (αβ↦1 ∙ sym α²↦1)
     ∙∙ H²K²→ℤ/2→H²K² (_⌣_ {G'' = ℤ/2Ring} K²gen.α K²gen.α)

-- Map H*(K²) → ℤ/2[X,Y]/I
H*Klein→ℤ/2[X,Y]/I :
    fst (H*R ℤ/2Ring KleinBottle)
 → fst (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)
H*Klein→ℤ/2[X,Y]/I =
  DS-Rec-Set.f _ _ _ _ squash/ [ neutral ]
    HⁿKlein→ℤ/2[X,Y]/I _
    (+Assoc (snd (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)))
    (+IdR (snd (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)))
    (+Comm (snd (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)))
    (λ { zero → cong [_] (base-neutral _)
      ; one → cong [_] (cong₂ _add_ (base-neutral _) (base-neutral _)
                      ∙ addRid neutral)
      ; two → cong [_] (cong (base (2 ∷ 0 ∷ []))
                        (IsGroupHom.pres1 (snd (H²[K²,ℤ/2]≅ℤ/2*)))
                      ∙ base-neutral _)
      ; (suc (suc (suc r))) → refl})
    λ { zero a b → cong [_] (base-add _ _ _ ∙ cong (base (0 ∷ 0 ∷ []))
                     (sym (IsGroupHom.pres· (snd (H⁰[K²,ℤ/2]≅ℤ/2)) a b)))
      ; one a b → cong [_] (move4 _ _ _ _ _add_ addAssoc addComm
      ∙ cong₂ _add_ (base-add _ _ _ ∙ cong (base (1 ∷ 0 ∷ []))
                    (cong fst (sym
                     (IsGroupHom.pres· (snd (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2)) a b))))
                    (base-add _ _ _ ∙ cong (base (0 ∷ 1 ∷ []))
                    (cong snd
                     (sym (IsGroupHom.pres· (snd (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2)) a b)))))
      ; two a b → cong [_] (base-add _ _ _ ∙ cong (base (2 ∷ 0 ∷ []))
                   (sym (IsGroupHom.pres· (snd (H²[K²,ℤ/2]≅ℤ/2*)) a b)))
      ; (suc (suc (suc n))) → λ a b → cong [_] (addRid neutral)}

-- The equivalence
ℤ/2[X,Y]/<X³,Y²,XY+X²>≅H*KleinBottle :
  RingEquiv (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)
            (H*R ℤ/2Ring KleinBottle)
fst ℤ/2[X,Y]/<X³,Y²,XY+X²>≅H*KleinBottle = isoToEquiv is
  where
  is : Iso  _ _
  fun is = ℤ/2[X,Y]/I→H*Klein .fst
  inv is = H*Klein→ℤ/2[X,Y]/I
  rightInv is = DS-Ind-Prop.f _ _ _ _
    (λ _ → trunc _ _)
    refl
    (λ { zero a → lem₀ a _ refl
       ; one a → lem₁ a _ _ refl
       ; two a → lem₂ a  _ refl
       ; (suc (suc (suc r))) a →
           sym (base-neutral _)
         ∙ cong (base (3 + r))
            (isContr→isProp (isContr-HⁿKleinBottle r ℤ/2)
             (0ₕ (3 + r)) a)})
    λ {x} {y} ind1 ind2
      → IsRingHom.pres+ (ℤ/2[X,Y]/I→H*Klein .snd)
          (H*Klein→ℤ/2[X,Y]/I x) (H*Klein→ℤ/2[X,Y]/I y)
         ∙ cong₂ _add_ ind1 ind2
    where
    lem₀ : (a : _) (x : _)
      → H⁰[K²,ℤ/2]≅ℤ/2 .fst .fst a ≡ x
      → ℤ/2[X,Y]/I→H*Klein .fst (H*Klein→ℤ/2[X,Y]/I (base zero a))
       ≡ base zero a
    lem₀ a =
      ℤ/2-elim
       (λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ H*Klein→ℤ/2[X,Y]/I) (help id)
              ∙ sym (help id))
      λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst)
               (cong [_] (cong (base (0 ∷ 0 ∷ [])) id))
            ∙ cong (base zero)
              (sym (cong (invEq (H⁰[K²,ℤ/2]≅ℤ/2 .fst)) id)
             ∙ retEq (fst H⁰[K²,ℤ/2]≅ℤ/2) a)
      where
      help : H⁰[K²,ℤ/2]≅ℤ/2 .fst .fst a ≡ 0
        → Path (fst (H*R ℤ/2Ring KleinBottle)) (base zero a) neutral
      help id' =
        sym (cong (base zero)
            (sym (cong (invEq (H⁰[K²,ℤ/2]≅ℤ/2 .fst)) id'
           ∙ IsGroupHom.pres1 (isGroupHomInv (H⁰[K²,ℤ/2]≅ℤ/2)))
           ∙ retEq (fst H⁰[K²,ℤ/2]≅ℤ/2) a))
        ∙ base-neutral zero

    lem₁ : (a : _) → (x y : _)
      → H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst .fst a ≡ (x , y)
      → ℤ/2[X,Y]/I→H*Klein .fst (H*Klein→ℤ/2[X,Y]/I (base one a))
       ≡ base one a
    lem₁ a =
      ℤ/2-elim
        (ℤ/2-elim
          (λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ [_])
            (cong₂ _add_ (cong (base (1 ∷ 0 ∷ []))
              (cong fst id))
              (cong (base (0 ∷ 1 ∷ []))
              (cong snd id)))
              ∙ addRid neutral
              ∙ sym (help a id))
          λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ [_])
                   (cong₂ _add_
                     (cong (base (1 ∷ 0 ∷ [])) (cong fst id)
                     ∙ base-neutral _)
                     (cong (base (0 ∷ 1 ∷ [])) (cong snd id))
                   ∙ addComm _ _ ∙ addRid _)
               ∙∙ cong (base 1) (1ₕ-⌣ 1 K²gen.β)
               ∙∙ cong (base 1) (sym (retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) K²gen.β)
                     ∙∙ cong (invEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst)) (sym id)
                     ∙∙ retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) a))
        (ℤ/2-elim
          (λ id → (cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ [_])
                   (cong₂ _add_
                     (cong (base (1 ∷ 0 ∷ [])) (cong fst id))
                     (cong (base (0 ∷ 1 ∷ [])) (cong snd id) ∙ base-neutral _)
                   ∙ addRid _)
                ∙ cong (base 1)
                   (    (⌣-1ₕ 1 K²gen.α ∙ transportRefl K²gen.α)
                      ∙ (sym (retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) K²gen.α)
                     ∙∙ cong (invEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst)) (α↦1 ∙ sym id)
                     ∙∙ retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) a))))
          λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ [_])
                   (cong₂ _add_
                     (cong (base (1 ∷ 0 ∷ [])) (cong fst id))
                     (cong (base (0 ∷ 1 ∷ [])) (cong snd id)))
                ∙ IsRingHom.pres+ (snd ℤ/2[X,Y]/I→H*Klein)
                   [ base (1 ∷ 0 ∷ []) 1 ] [ base (0 ∷ 1 ∷ []) 1 ]
                ∙ cong₂ _add_
                        (cong (base one) (⌣-1ₕ 1 (incL 1) ∙ transportRefl K²gen.α))
                        (cong (base one) (1ₕ-⌣ 1 (incR 1)))
                ∙ base-add 1 K²gen.α K²gen.β
                ∙ cong (base one)
                   (sym (retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) (K²gen.α +ₕ K²gen.β))
                 ∙∙ (cong (invEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst)) (sym id))
                 ∙∙ retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) a))
      where
      help : (a : _) → H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst .fst a ≡ (0 , 0)
        → Path (fst (H*R ℤ/2Ring KleinBottle)) (base one a) neutral
      help a p =
         (sym (cong (base one)
                  (sym (cong (invEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst)) p
                 ∙ IsGroupHom.pres1 (isGroupHomInv (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2)))
                 ∙ retEq (H¹[K²,ℤ/2]≅ℤ/2×ℤ/2 .fst) a)))
        ∙ base-neutral one

    lem₂ : (a : _) (x : _) → H²[K²,ℤ/2]≅ℤ/2* .fst .fst a ≡ x
      → ℤ/2[X,Y]/I→H*Klein .fst (H*Klein→ℤ/2[X,Y]/I (base two a))
       ≡ base two a
    lem₂ a =
      ℤ/2-elim
       (λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst ∘ H*Klein→ℤ/2[X,Y]/I)
                  (cong (base 2) (help1 id) ∙ base-neutral _)
              ∙∙ sym (base-neutral _)
              ∙∙ cong (base 2) (sym (help1 id)))
        λ id → cong (ℤ/2[X,Y]/I→H*Klein .fst)
                 (cong [_] (cong (base (2 ∷ 0 ∷ []))
                     (cong (H²[K²,ℤ/2]≅ℤ/2* .fst .fst) (help2 id)
                     ∙ α²↦1') ))
             ∙∙ cong (base 2) (⌣-1ₕ 2 (incL 2) ∙ transportRefl (incL 2))
             ∙∙ cong (base two) (sym (help2 id))
      where
      help1 : H²[K²,ℤ/2]≅ℤ/2* .fst .fst a ≡ 0 → a ≡ 0ₕ 2
      help1 p = sym (retEq (H²[K²,ℤ/2]≅ℤ/2* .fst) a)
           ∙ cong (invEq (H²[K²,ℤ/2]≅ℤ/2* .fst)) p
           ∙ IsGroupHom.pres1 (isGroupHomInv H²[K²,ℤ/2]≅ℤ/2*)

      help2 : H²[K²,ℤ/2]≅ℤ/2* .fst .fst a ≡ 1 → a ≡ α⌣α
      help2 p = sym (retEq (H²[K²,ℤ/2]≅ℤ/2* .fst) a)
          ∙∙ cong (invEq (H²[K²,ℤ/2]≅ℤ/2* .fst)) (p ∙ sym α²↦1')
          ∙∙ retEq (H²[K²,ℤ/2]≅ℤ/2* .fst) α⌣α

  leftInv is =
    SQ.elimProp
      (λ _ → squash/ _ _)
      (DS-Ind-Prop.f _ _ _ _
        (λ _ → squash/ _ _)
        refl
        (λ r a → main a r)
        λ {x} {y} ind1 ind2
          → cong₂ (_+r_ (snd (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)))
                   ind1 ind2)
    where
    clem : (x y : ℕ)
      → H*Klein→ℤ/2[X,Y]/I
          (ℤ/2[X,Y]/I→H*Klein .fst
            [ base (suc (suc (suc x)) ∷ y ∷ []) 1 ])
      ≡ [ neutral ]
    clem x zero = refl
    clem x (suc n) = refl

    help : (y : ℕ) →
      Path (fst (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>))
           [ base (one ∷ suc (suc y) ∷ []) 1 ]
           [ neutral ]
    help y = eq/ _ _
      ∣ (λ { zero → neutral
          ; one → base (1 ∷ y ∷ []) 1
          ; two → neutral})
      , (sym (addRid _)
       ∙ addComm (base (1 ∷ suc (suc y) ∷ []) 1 add neutral) neutral)
      ∙ (λ i → neutral add (base (1 ∷ (+-comm 2 y i) ∷ []) 1
                        add (addRid neutral (~ i)))) ∣₁

    help2 : (y : ℕ)
      → ℤ/2[X,Y]/I→H*Klein .fst [ base (zero ∷ suc (suc y) ∷ []) 1 ]
       ≡ neutral
    help2 zero = cong (base 2) (1ₕ-⌣ 2 (incR two))
            ∙ base-neutral _
    help2 (suc y) = base-neutral _

    help3 : (x y : ℕ)
      → ℤ/2[X,Y]/I→H*Klein .fst [ base (x ∷ suc (suc y) ∷ []) 1 ]
       ≡ neutral
    help3 zero y = help2 y
    help3 (suc x) y =
         (λ i → base (suc (suc (+-suc x y i)))
                 (transp (λ j → coHom (suc (suc (+-suc x y (i ∧ j))))
                   ℤ/2 KleinBottle) (~ i)
                  (_⌣_ {G'' = ℤ/2Ring} (incL (suc x)) (incR (suc (suc y))))))
       ∙ cong (base (suc (suc (suc (x + y)))))
          (isContr→isProp (isContr-HⁿKleinBottle (x + y) ℤ/2) _ _)
       ∙ base-neutral _

    main-1 : (r : _)
      → H*Klein→ℤ/2[X,Y]/I (ℤ/2[X,Y]/I→H*Klein .fst [ base r 1 ])
      ≡ [ base r 1 ]
    main-1 (zero ∷ zero ∷ []) = refl
    main-1 (zero ∷ one ∷ []) =
      cong (H*Klein→ℤ/2[X,Y]/I)
           (cong (base 1) (1ₕ-⌣ 1 (incR 1)))
        ∙ cong [_] (cong₂ _add_ (base-neutral _)
                   (λ _ → base (0 ∷ 1 ∷ []) 1)
                 ∙ addComm _ _ ∙ addRid _)
    main-1 (zero ∷ suc (suc y) ∷ []) =
      cong H*Klein→ℤ/2[X,Y]/I (help2 y)
     ∙ eq/ _ _
       ∣ (λ {zero → neutral
           ; one → base (0 ∷ (y ∷ [])) 1
           ; two → neutral})
      , cong (neutral add_)
         (((λ i → base (0 ∷ (+-comm 2 y i) ∷ []) 1)
        ∙ sym (addRid (base (0 ∷ (y + 2) ∷ []) 1)))
       ∙ cong (base (0 ∷ (y + 2) ∷ []) 1 add_) (sym (addRid _))) ∣₁
    main-1 (one ∷ zero ∷ []) =
      cong H*Klein→ℤ/2[X,Y]/I
        (cong (base 1) (⌣-1ₕ 1 (incL one) ∙ transportRefl _))
       ∙ cong [_] (cong₂ _add_ (cong (base (1 ∷ 0 ∷ []))
                                (cong fst α↦1))
                               (base-neutral _)
                 ∙ addRid _)
    main-1 (one ∷ one ∷ []) =
      cong [_] (cong (base (2 ∷ 0 ∷ [])) αβ↦1')
       ∙ eq/ _ _ ∣ (λ {zero → neutral
                     ; one → neutral
                     ; two → base (0 ∷ 0 ∷ []) 1})
               , ((addComm _ _
                ∙ sym (addRid _)
                ∙ addComm (base (1 ∷ 1 ∷ []) 1
                      add (base (2 ∷ 0 ∷ []) 1))
                      neutral
                ∙ sym (addRid _)
                ∙ addComm (neutral add (base (1 ∷ 1 ∷ []) 1
                      add (base (2 ∷ 0 ∷ []) 1))) neutral)
                ∙ λ i → neutral add
                  (neutral add (addRid
                   (base (1 ∷ 1 ∷ []) 1
                    add (base (2 ∷ 0 ∷ []) 1)) (~ i)))) ∣₁
    main-1 (one ∷ suc (suc y) ∷ []) =
      cong H*Klein→ℤ/2[X,Y]/I (help3 one y) ∙ sym (help y)
    main-1 (two ∷ zero ∷ []) =
      cong [_] (cong (base (2 ∷ 0 ∷ []))
        (cong (H²[K²,ℤ/2]≅ℤ/2* .fst .fst)
        (⌣-1ₕ 2 (incL 2) ∙ transportRefl _)
      ∙ α²↦1'))
    main-1 (two ∷ suc y ∷ []) =
      eq/ neutral _
       ∣ (λ {zero → base (0 ∷ y ∷ []) 1
           ; one → neutral
           ; two → base (1 ∷ y ∷ []) 1})
       , ((addComm _ _ ∙ addRid _
       ∙ ((((λ i → base (2 ∷ +-comm 1 y i ∷ []) 1)
         ∙ sym (addRid _))
         ∙ cong (base (2 ∷ y + 1 ∷ []) (fsuc fzero) add_)
            (sym (base-neutral _)
            ∙ sym (base-add (3 ∷ y + 0 ∷ []) 1 1)))
       ∙ addComm _ _)
       ∙ sym (addAssoc _ _ _))
       ∙∙ cong (base (3 ∷ y + 0 ∷ []) (fsuc fzero) add_)
          (addComm _ _
          ∙ sym (addComm _ _ ∙ addRid _))
       ∙∙ (λ i → base (3 ∷ (y + 0) ∷ []) 1
            add (neutral
            add addRid (base (2 ∷ (y + 1) ∷ []) 1
            add base (3 ∷ (y + 0) ∷ []) 1 ) (~ i)))) ∣₁
    main-1 (suc (suc (suc x)) ∷ y ∷ []) =
      clem x y
      ∙ eq/ neutral _
        ∣ (λ {zero → base (x ∷ y ∷ []) 1
           ; one → neutral
           ; two → neutral})
        , ((addComm neutral (base ((3 + x) ∷ y ∷ []) 1)
        ∙ cong (base ((3 + x) ∷ y ∷ []) 1 add_) (sym (addRid neutral)))
         ∙ λ i → base ((+-comm 3 x i) ∷ (+-comm 0 y i) ∷ []) 1
                  add (neutral add (addRid neutral (~ i)))) ∣₁

    main : (a : ℤ/2 .fst) (r : _)
      → H*Klein→ℤ/2[X,Y]/I (ℤ/2[X,Y]/I→H*Klein .fst [ base r a ]) ≡ [ base r a ]
    main = ℤ/2-elim (λ r → cong (H*Klein→ℤ/2[X,Y]/I ∘ ℤ/2[X,Y]/I→H*Klein .fst)
                             (cong [_] (base-neutral r))
                          ∙ cong [_] (sym (base-neutral r)))
                     main-1
snd ℤ/2[X,Y]/<X³,Y²,XY+X²>≅H*KleinBottle = ℤ/2[X,Y]/I→H*Klein .snd

H*KleinBottle≅ℤ/2[X,Y]/<X³,Y²,XY+X²> :
  RingEquiv (H*R ℤ/2Ring KleinBottle)
            (CommRing→Ring ℤ/2[X,Y]/<X³,Y²,XY+X²>)
H*KleinBottle≅ℤ/2[X,Y]/<X³,Y²,XY+X²> =
  RingEquivs.invRingEquiv ℤ/2[X,Y]/<X³,Y²,XY+X²>≅H*KleinBottle
