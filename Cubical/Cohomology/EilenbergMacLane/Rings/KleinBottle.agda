{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle where

open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Loopspace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.Ring

open import Cubical.HITs.KleinBottle renaming (rec to KleinFun)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp

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


lem2 : ℤ/2→Ω²K₂ 1 ≡ ℤ/2→Ω²K₂' 1
lem2 k i j =
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
           ∙ λ i → KleinFun (0ₖ 2) refl refl (lem2 (~ i)) x

  cupIdα : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.α K²gen.α
         ≡ ℤ/2→H²K² 1
  cupIdα = cong ∣_∣₂ (funExt almostα)

β²↦1 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.β K²gen.β) ≡ 0
β²↦1 = cong H²K²→ℤ/2 cupIdΒ ∙ ℤ/2→H²K²→ℤ/2 0
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
        ∙∙ λ i → KleinFun ∣ north ∣ refl refl (lem2 (~ i)) x)))
      ∙ ℤ/2→H²K²→ℤ/2 1

αβ↦1 : H²K²→ℤ/2 (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} K²gen.α K²gen.β) ≡ 1
αβ↦1 = cong H²K²→ℤ/2 (⌣-commℤ/2₁,₁ K²gen.α K²gen.β) ∙ βα↦1
