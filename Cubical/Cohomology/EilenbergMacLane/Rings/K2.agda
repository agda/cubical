{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.K2 where

open import Cubical.Cohomology.EilenbergMacLane.Groups.K2
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Connected

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Base as EM
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin

open import Cubical.HITs.EilenbergMacLane1 renaming (elimSet to elimSetEM ; elimProp to elimPropEM)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.Truncation as TR
  hiding (rec ; map ; elim ; elim2 ; elim3)
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.Susp 

private
  variable
    ℓ : Level

open import Cubical.HITs.Susp
open import Cubical.Homotopy.Loopspace

open IsAbGroup
open AbGroupStr

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Equiv.HalfAdjoint


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

α-raw : KleinBottle → EM ℤ/2 1
α-raw = Klein→-fun embase (emloop 1) refl (flipSquare (sym (emloop-inv (AbGroup→Group ℤ/2) 1)))

β-raw : KleinBottle → EM ℤ/2 1
β-raw = Klein→-fun embase refl (emloop 1) (λ _ i → emloop 1 i)

α : coHom 1 ℤ/2 KleinBottle
α = ∣ Klein→-fun embase (emloop 1) refl (flipSquare (sym (emloop-inv (AbGroup→Group ℤ/2) 1))) ∣₂

β : coHom 1 ℤ/2 KleinBottle
β = ∣ Klein→-fun embase refl (emloop 1) (λ _ i → emloop 1 i) ∣₂

open import Cubical.Algebra.Ring



open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)

emloop' : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong₂ (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
        ≡ refl
emloop' p = cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p
          ∙∙ (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                  ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)
          ∙∙ sym (rUnit refl)


FF = (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})

R : ∀ {ℓ} {A B : Type ℓ} {x y : A} (f : A → A → B)
  → (p : x ≡ y) → sym (cong (λ x₁ → f x₁ y) (sym p) ∙ cong (f x) (sym p)) ≡
      cong (λ x₁ → f x₁ x) p ∙ cong (f y) p
R {x = x} {y = y} f p i j =
  hcomp (λ k → λ {(i = i0) → compPath-filler (cong (λ x₁ → f x₁ y) (sym p)) (cong (f x) (sym p)) k (~ j)
                 ; (i = i1) → compPath-filler (cong (λ x₁ → f x₁ x) p) (cong (f y) p) k j
                 ; (j = i0) → f x (p (~ k ∧ ~ i))
                 ; (j = i1) → f y (p (k ∨ ~ i))})
        (f (p j) (p (~ i)))

myF : (p : Path (EM ℤ/2 1) embase embase)
  → sym
      (cong (λ x₁ → FF x₁ embase) (sym p) ∙ cong (FF embase) (sym p))
      ≡ cong (λ x₁ → FF x₁ embase) p ∙ cong (FF embase) p
myF = λ p → (cong sym (sym (rUnit (cong (λ x₁ → FF x₁ embase) (sym p)))) ∙∙ (λ i j → FF (p j) (p (~ i))) ∙∙ rUnit _)

R' : (p : Path (EM ℤ/2 1) embase embase)
  → R FF p ≡ myF p
R' p k i j =
  hcomp (λ r → λ {(i = i0) → compPath-filler (cong (λ x₁ → FF x₁ embase) (sym p)) (cong (FF embase) (sym p)) r (~ j)
                 ; (i = i1) → compPath-filler (cong (λ x₁ → FF x₁ embase) (sym p)) (cong (FF embase) (sym p)) r (~ j)
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣})
        (FF (p j) (p (~ i)))

R-refl : ∀ {ℓ} {A B : Type ℓ} {x : A} (f : A → A → B)
      → R {x = x} f refl ≡ refl
R-refl {x = x} f k i j = 
  hcomp (λ r → λ {(i = i0) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)
                 ; (i = i1) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)
                 ; (j = i0) → f x x
                 ; (j = i1) → f x x
                 ; (k = i1) → compPath-filler (λ _ → f x x) (λ _ → f x x) r (~ j)})
        (f x x)

cong₂Funct-cong-sym : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → A → B)
  → cong₂Funct f p p ∙ sym (R f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p))
cong₂Funct-cong-sym {A = A} {B = B} =
  J (λ y p → (f : A → A → B) → cong₂Funct f p p ∙ sym (R f p)
    ≡ cong sym (cong₂Funct f (sym p) (sym p)))
        λ f → (λ i → cong₂Funct f refl refl ∙ sym (R-refl f i))
              ∙ sym (rUnit _) -- λ f → rUnit _ ∙ λ i → cong sym (cong₂Funct f refl refl) ∙ R-refl f (~ i)

emloop''2 : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong sym (emloop' (sym p))
  ≡ (((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p) ∙ sym (myF p))
  ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
  ∙∙ sym (rUnit refl))
emloop''2 p i = (cong₂Funct-cong-sym p FF (~ i)
  ∙∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i))
  ∙∙ sym (rUnit refl))

gr : ∀ {ℓ} {A : Type ℓ} {x y z w t : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ t)
  → ((p ∙ q) ∙∙ r ∙∙ s) ≡ (p ∙∙ (q ∙ r) ∙∙ s)
gr p q r s i = compPath-filler p q (~ i) ∙∙ compPath-filler' q r i ∙∙ s

emloop''' : (p : fst (Ω (EM∙ ℤ/2 1)))
  → cong sym (emloop' (sym p))
  ≡ (((cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}) p p))
  ∙∙ (sym (myF p) ∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i)
                              ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (p j) i)))
  ∙∙ sym (rUnit refl))
emloop''' p = emloop''2 p ∙ gr (cong₂Funct FF p p) (sym (myF p)) (λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (p j) i) ∙ (λ j → embase ⌣ₖ⊗ p j)) (sym (rUnit refl))


Klein→-funβ : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (β-raw x) (β-raw x)) ≡ ∣ north ∣ₕ
Klein→-funβ point = refl
Klein→-funβ (line1 i) = refl
Klein→-funβ (line2 i) j = emloop' (emloop 1) j i
Klein→-funβ (square i j) k = emloop' (emloop 1) k j

ℤ/ℤ⨂→ : (x y : fst ℤ/2) → fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))
ℤ/ℤ⨂→ x y = sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (x ⊗ y)) ∙∙ EM→ΩEM+1-0ₖ 1

ℤ/2→ : fst ℤ/2 → fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))
ℤ/2→ g = ℤ/ℤ⨂→ g g

ℤ/2→' : fst ℤ/2 → fst ((Ω^ 2) (EM∙ ℤ/2 2))
ℤ/2→' g = (sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 g) ∙∙ EM→ΩEM+1-0ₖ 1)

ℤ/2→Flip''-gen : (x y : fst ℤ/2) → (ℤ/ℤ⨂→ x y) ≡ sym (ℤ/ℤ⨂→ y x)
ℤ/2→Flip''-gen x y i j =
  hcomp (λ k → λ {(j = i0) → EM→ΩEM+1-0ₖ 1 k
                 ; (j = i1) → EM→ΩEM+1-0ₖ 1 k})
         (braa i j)
  where
  lem3 : (x y : _) → Path (ℤ/2 ⨂₁ ℤ/2) (x ⊗ y) (y ⊗ x)
  lem3 = ℤ/2-elim (ℤ/2-elim refl (⊗AnnihilL 1 ∙ sym (⊗AnnihilR 1)))
            (ℤ/2-elim (⊗AnnihilR 1 ∙ sym (⊗AnnihilL 1)) refl)

  lem2 : (x y : _) → GroupStr.inv (snd (AbGroup→Group (ℤ/2 ⨂ ℤ/2))) (y ⊗ x) ≡ x ⊗ y
  lem2 x y = cong (_⊗ x) (-const y) ∙ lem3 y x

  braa : cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (emloop (x ⊗ y))
       ≡ cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1) (sym (emloop (y ⊗ x)))
  braa = cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1)) (cong emloop (sym (lem2 x y)))
       ∙ cong (cong (EM→ΩEM+1 {G = ℤ/2 ⨂ ℤ/2} 1))
          (emloop-inv (AbGroup→Group (ℤ/2 ⨂ ℤ/2)) (y ⊗ x))


ℤ/2→Flip'' : ℤ/2→ (fsuc fzero) ≡ sym (ℤ/2→ (fsuc fzero))
ℤ/2→Flip'' = ℤ/2→Flip''-gen 1 1

ℤ/2→Flip : ℤ/2→ (fsuc fzero) ≡ λ k i → ℤ/2→ (fsuc fzero) k (~ i)
ℤ/2→Flip = ℤ/2→Flip'' ∙ sym≡cong-sym (ℤ/2→ (fsuc fzero))

ℤ/2→Flip' : ℤ/2→ (fsuc fzero) ≡ flipSquare (ℤ/2→ (fsuc fzero))
ℤ/2→Flip' = ℤ/2→Flip ∙∙ sym (sym≡cong-sym (ℤ/2→ (fsuc fzero))) ∙∙ sym≡flipSquare (ℤ/2→ (fsuc fzero))


Cube1 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube1 i k r =
  hcomp (λ j →
    λ {(i = i0) → ∣ north ∣ 
     ; (i = i1) → ∣ north ∣
     ; (k = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
     ; (k = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 (~ i)) (~ r ∨ ~ j)
     ; (r = i0) → ℤ/2→ (fsuc fzero) k i
     ; (r = i1) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                         (λ i j → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) j)
                                         (EM→ΩEM+1-0ₖ 1) (~ j) k (~ i) })
         (ℤ/2→Flip r k i)

Cube2 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube2 i k r =
  hcomp (λ j →
      λ {(i = i0) → ∣ north ∣
       ; (i = i1) → ∣ north ∣
       ; (k = i0) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)
       ; (k = i1) → rUnit (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r)) j (~ i)})
   (Cube1 i k r)

Cube3 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube3 i k r =
  hcomp (λ j →
     λ {(i = i0) →  ∣ north ∣
      ; (i = i1) →  ∣ north ∣
      ; (k = i0) → ((λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (~ r))
                   ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) (~ r)) (~ i)
      ; (k = i1) → ((λ k → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j))
                    ∙ λ k → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 k) (~ r ∨ j)) (~ i)
      ; (r = i0) → (sym (rUnit refl) ∙∙ ℤ/2→ (fsuc fzero) ∙∙ rUnit refl) k i
      ; (r = i1) → compPath-filler (sym (myF (emloop 1)))
                     (((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                                                  ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i)))
                     j k (~ i)})
  (Cube2 i k r)

Cube4 : (i k r : I) → EM (ℤ/2 ⨂ ℤ/2) 2
Cube4 i k r =
  hcomp (λ j →
   λ {(i = i0) → ∣ north ∣
    ; (i = i1) → ∣ north ∣
    ; (k = i1) → rUnit (λ _ → FF embase embase) (~ j) i
    ; (r = i0) → doubleCompPath-filler (sym (rUnit (λ _ → FF embase embase))) (ℤ/2→ (fsuc fzero)) (rUnit (λ _ → FF embase embase)) (~ j) k i
    ; (r = i1) → doubleCompPath-filler (((cong₂Funct FF (emloop 1) (emloop 1))))
                     (sym (myF (emloop 1)) ∙ ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
                                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i)))
                    (sym (rUnit refl)) j k (~ i)})
   (Cube3 i k r)

Cube5 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube5 i j k = hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (emloop 1) (~ r ∨ k) (~ i)
                 ; (j = i1) → Cube4 i k r
                 ; (k = i0) → emloop' (emloop 1) (~ r) (~ i)
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
                 (ℤ/2→ (fsuc fzero) (j ∧ k) i)

Cube6 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube6 i j k =
  hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
                 ; (j = i1) → emloop''' (emloop 1) (~ r) k (~ i)
                 ; (k = i0) → FF (emloop 1 (~ i)) (emloop 1 (~ i))
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
                 (Cube5 i j k)

Cube7 : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube7 i j k = 
  hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣
                 ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
                 ; (j = i1) → emloop' (λ i₁ → α-raw (square i₁ r)) k i
                 ; (k = i0) → FF (α-raw (square i (j ∧ r))) (α-raw (square i (j ∧ r)))
                 ; (k = i1) → ℤ/2→ (fsuc fzero) j i})
           (Cube6 i j k)

Klein→-funβα : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (β-raw x) (α-raw x))
                                  ≡ Klein→-fun (0ₖ 2) refl refl (ℤ/2→ 1) x
Klein→-funβα point = refl
Klein→-funβα (line1 i) k = ∣ north ∣
Klein→-funβα (line2 i) = ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 i)
Klein→-funβα (square i j) k =
  hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) k
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → FF (emloop 1 j) (α-raw (square i (j ∧ r)))
                 ; (k = i1) → (ℤ/2→ (fsuc fzero)) i j})
    (hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                ; (i  = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) (k ∨ ~ r)
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1)) (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1) )) (EM→ΩEM+1-0ₖ 1) (~ r) (~ i) j
                 ; (k = i1) → (ℤ/2→ (fsuc fzero)) i j})
        (ℤ/2→Flip'' (~ k) i j))

Klein→-funα⊗ : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2} {n = 1} {m = 1} (α-raw x) (α-raw x))
                                    ≡ Klein→-fun (0ₖ 2) refl refl (ℤ/2→ 1) x
Klein→-funα⊗ x = Klein→-funα' x ∙ λ i → Klein→-fun (0ₖ 2) refl refl (ℤ/2→Flip' (~ i)) x
  where
  Klein→-funα' : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (α-raw x) (α-raw x))
                                    ≡ Klein→-fun (0ₖ 2) refl refl (flipSquare (ℤ/2→ 1)) x
  Klein→-funα' point = refl
  Klein→-funα' (line1 i) k = emloop' (cong α-raw line1) k i
  Klein→-funα' (line2 i) = refl
  Klein→-funα' (square i j) k = Cube7 i j k

Klein' : (x : KleinBottle)
  → (Klein→-fun (0ₖ 2) refl refl (ℤ/2→ 1) x)
   ≡ Klein→-fun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x
Klein' point = refl
Klein' (line1 i) = refl
Klein' (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
Klein' (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i) k)

Klein'' : (x : KleinBottle)
  → (Klein→-fun (0ₖ 2) refl refl (ℤ/2→' 1) x)
   ≡ Klein→-fun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x
Klein'' point = refl
Klein'' (line1 i) = refl
Klein'' (line2 i) j = EM→ΩEM+1-0ₖ 1 (~ j) i
Klein'' (square i k) j =
  hcomp (λ r → λ {(i = i0) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (i = i1) → EM→ΩEM+1-0ₖ 1 (~ j ∧ r) k
                 ; (j = i1) → EM→ΩEM+1 1 (emloop 1 i) k
                 ; (k = i0) → ∣ north ∣
                 ; (k = i1) → ∣ north ∣})
        (EM→ΩEM+1 1 (emloop 1 i) k)

Klein→-funα⊗'' : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 (Klein→-fun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop (1 ⊗ 1) i))) x)
                          ≡ (Klein→-fun (0ₖ 2) refl (EM→ΩEM+1 1 embase) (λ i → (EM→ΩEM+1 1 (emloop 1 i))) x)
Klein→-funα⊗'' point = refl
Klein→-funα⊗'' (line1 i) = refl
Klein→-funα⊗'' (line2 i) k = ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2) (merid embase) (sym (merid embase)) k i ∣ₕ
Klein→-funα⊗'' (square i j) k = ∣ cong-∙ (inducedFun-EM-raw TensorMultHom 2) (merid (emloop (1 ⊗ 1) i)) (sym (merid embase)) k j ∣ₕ

Klein→-funβ⊗'' : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 ∣ north ∣
                          ≡ (Klein→-fun (0ₖ 2) refl refl refl x) 
Klein→-funβ⊗'' point = refl
Klein→-funβ⊗'' (line1 i) = refl
Klein→-funβ⊗'' (line2 i) = refl
Klein→-funβ⊗'' (square i j) = refl


lem2 : G→Ω²K² 1 ≡ ℤ/2→' 1
lem2 k i j = hcomp (λ r → λ {(i = i0) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                            ; (i = i1) → transportRefl (EM→ΩEM+1-0ₖ 1) k r j
                            ; (j = i0) → ∣ north ∣
                            ; (j = i1) → ∣ north ∣ })
                   (EM→ΩEM+1 1 (EM→ΩEM+1 0 1 i) j)


open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
FF-comm : (x : EM ℤ/2 1)
  → cup∙ {G' = ℤ/2} {H' = ℤ/2} 1 1 x ≡ ((λ y → FF y x) , (0ₖ-⌣ₖ⊗ 1 1 x))
FF-comm =
  EM-raw'-elim ℤ/2 1 (λ _ → isOfHLevel↑∙ 1 0 _ _)
    λ x → →∙Homogeneous≡ (isHomogeneousEM _)
      (funExt λ y → funExt⁻ (cong fst (Rs' y)) x)
  where -- isOfHLevel↑∙'
  Rs' : (y : EM ℤ/2 1) → Path (EM-raw'∙ ℤ/2 1 →∙ EM∙ (ℤ/2 ⨂ ℤ/2) 2)
                               ((λ x → FF (EM-raw'→EM ℤ/2 1 x) y) , refl)
                               ((λ x → FF y (EM-raw'→EM ℤ/2 1 x)) , ⌣ₖ-0ₖ⊗ 1 1 y)
  Rs' = EM-raw'-elim _ 1 (λ _ → isOfHLevel↑∙' 1 1 _ _)
          λ x → →∙Homogeneous≡ (isHomogeneousEM _) (funExt λ y → L y x)
    where
    L : (x y : EM₁-raw (AbGroup→Group ℤ/2))
      → FF (EM-raw'→EM ℤ/2 1 x) (EM-raw'→EM ℤ/2 1 y)
      ≡ FF (EM-raw'→EM ℤ/2 1 y) (EM-raw'→EM ℤ/2 1 x)
    L embase-raw embase-raw = refl
    L embase-raw (emloop-raw g i) = sym (⌣ₖ-0ₖ⊗ 1 1 (emloop g i))
    L (emloop-raw g i) embase-raw = ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) 
    L (emloop-raw g i) (emloop-raw h j) k =
      hcomp (λ r → λ {(i = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                     ; (i = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop h j) (~ k ∨ ~ r)
                     ; (j = i0) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                     ; (j = i1) → ⌣ₖ-0ₖ⊗ 1 1 (emloop g i) (k ∨ ~ r)
                     ; (k = i0) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                    (λ j i → EM→ΩEM+1 1 (EM→ΩEM+1 0 (g ⊗ h) j) i) (EM→ΩEM+1-0ₖ 1) (~ r) j i
                     ; (k = i1) → doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1))
                                    (λ j i → EM→ΩEM+1 1 (EM→ΩEM+1 0 (h ⊗ g) j) i) (EM→ΩEM+1-0ₖ 1) (~ r) i j})
            (help k i j)
      where
      help : flipSquare (ℤ/ℤ⨂→ g h) ≡ ℤ/ℤ⨂→ h g
      help = sym (sym≡flipSquare (ℤ/ℤ⨂→ g h))
           ∙ cong sym (ℤ/2→Flip''-gen g h)

⌣ₖ⊗-commℤ/2₁,₁ : (x y : EM ℤ/2 1) → _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1} x y ≡ (y ⌣ₖ⊗ x)
⌣ₖ⊗-commℤ/2₁,₁ x y i = FF-comm x i .fst y

⌣ₖ-commℤ/2₁,₁ : (x y : EM ℤ/2 1) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} x y ≡ (y ⌣ₖ x)
⌣ₖ-commℤ/2₁,₁ x y = cong (EMTensorMult 2) (⌣ₖ⊗-commℤ/2₁,₁ x y)

⌣-commℤ/2₁,₁ : ∀ {ℓ} {A : Type ℓ} (x y : coHom 1 ℤ/2 A) → (_⌣_ {G'' = ℤ/2Ring} x y) ≡ (y ⌣ x)
⌣-commℤ/2₁,₁ = ST.elim2 (λ _ _ → isSetPathImplicit)
                λ f g → cong ∣_∣₂ (funExt λ x → ⌣ₖ-commℤ/2₁,₁ (f x) (g x))


almostα : (x : KleinBottle) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} (α-raw x) (α-raw x)
                           ≡ Klein→-fun (0ₖ 2) refl refl (G→Ω²K² 1) x
almostα x = cong (EMTensorMult {G'' = ℤ/2Ring} 2) (Klein→-funα⊗ x ∙ Klein' x)
        ∙∙ Klein→-funα⊗'' x
        ∙∙ sym (Klein'' x)
         ∙ λ i → Klein→-fun (0ₖ 2) refl refl (lem2 (~ i)) x

cupIdα : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α α
       ≡ G→H²K² 1
cupIdα = cong ∣_∣₂ (funExt almostα)

G→Ω²K²-refl : G→Ω²K² 0 ≡ refl
G→Ω²K²-refl = Iso.leftInv Iso-Ω²K²-G refl

cupIdΒ : _⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β β
       ≡ ∣ Klein→-fun (0ₖ 2) refl refl (G→Ω²K² 0) ∣₂
cupIdΒ = cong ∣_∣₂ (funExt λ x → cong (EMTensorMult {G'' = ℤ/2Ring} 2) (Klein→-funβ x)
                        ∙ Klein→-funβ⊗'' x
                        ∙ λ i → Klein→-fun ∣ north ∣ refl refl (G→Ω²K²-refl (~ i)) x)

βα↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β α) ≡ 1
βα↦1 = cong H²K²→G (cong ∣_∣₂ (funExt (λ x → cong (EMTensorMult {G'' = ℤ/2Ring} 2) (Klein→-funβα x ∙ Klein' x)
                   ∙∙ (Klein→-funα⊗'' x  ∙ sym (Klein'' x))
                   ∙∙ λ i → Klein→-fun ∣ north ∣ refl refl (lem2 (~ i)) x)))
      ∙ G→H²K²→G 1

β↦0,1 : H¹K²→G+G β ≡ (0 , 1)
β↦0,1 = refl

β²↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} β β) ≡ 0
β²↦1 = cong H²K²→G cupIdΒ ∙ G→H²K²→G 0


α↦1 : H¹K²→G+G α ≡ (1 , 0)
α↦1 = refl

α⌣α↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α α) ≡ 1
α⌣α↦1 = cong H²K²→G cupIdα ∙ G→H²K²→G 1

αβ↦1 : H²K²→G (_⌣_ {G'' = ℤ/2Ring} {n = 1} {m = 1} α β) ≡ 1
αβ↦1 = cong H²K²→G (⌣-commℤ/2₁,₁ α β) ∙ βα↦1
