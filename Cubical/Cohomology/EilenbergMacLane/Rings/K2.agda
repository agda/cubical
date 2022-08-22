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

Z/2r : Ring ℓ-zero
fst Z/2r = ℤ/2 .fst
RingStr.0r (snd Z/2r) = fzero
RingStr.1r (snd Z/2r) = 1
RingStr._+_ (snd Z/2r) = _+ₘ_
RingStr._·_ (snd Z/2r) = _·ₘ_
RingStr.- snd Z/2r = -ₘ_
IsRing.+IsAbGroup (RingStr.isRing (snd Z/2r)) = isAbGroup (snd ℤ/2)
IsSemigroup.is-set (IsMonoid.isSemigroup (IsRing.·IsMonoid (RingStr.isRing (snd Z/2r)))) =
  isSetFin
IsSemigroup.·Assoc (IsMonoid.isSemigroup (IsRing.·IsMonoid (RingStr.isRing (snd Z/2r)))) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsMonoid.·IdR (IsRing.·IsMonoid (RingStr.isRing (snd Z/2r))) = ℤ/2-elim refl refl
IsMonoid.·IdL (IsRing.·IsMonoid (RingStr.isRing (snd Z/2r))) = ℤ/2-elim refl refl
IsRing.·DistR+ (RingStr.isRing (snd Z/2r)) =
  ℤ/2-elim (λ y z → refl) (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsRing.·DistL+ (RingStr.isRing (snd Z/2r)) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))

open import Cubical.Algebra.AbGroup.TensorProduct
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

Klein→-funβ : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (β-raw x) (β-raw x)) ≡ ∣ north ∣ₕ
Klein→-funβ point = refl
Klein→-funβ (line1 i) = refl
Klein→-funβ (line2 i) j = emloop' (emloop 1) j i
Klein→-funβ (square i j) k = emloop' (emloop 1) k j

ℤ/2→ : fst ℤ/2 → fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))
ℤ/2→ g = (sym (EM→ΩEM+1-0ₖ 1) ∙∙ cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (g ⊗ g)) ∙∙ EM→ΩEM+1-0ₖ 1)

Cube₂ : Cube (λ j k → ∣ north ∣) (λ j k → ∣ north ∣)
             (λ i k → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i))
             (λ i k → emloop''2 (emloop 1) i1 k (~ i))
             (λ i j → FF (emloop 1 (~ i)) (emloop 1 (~ i)))
             (ℤ/2→ (fsuc fzero))
Cube₂ i j k = hcomp (λ r →
                λ {(i = i0) → ∣ north ∣ -- ∣ rCancel (merid ptEM-raw) r (j ∧ k) ∣
                 ; (i = i1) → ∣ north ∣ -- ∣ rCancel (merid ptEM-raw) r (j ∧ k) ∣
                 ; (j = i0) → emloop' (emloop 1) (~ r ∨ k) (~ i)
                 ; (j = i1) → {!doubleCompPath-filler (sym (EM→ΩEM+1-0ₖ 1)) (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1))) (EM→ΩEM+1-0ₖ 1) r i j!}
                 ; (k = i0) → emloop' (emloop 1) (~ r) (~ i)
                 ; (k = i1) → ℤ/2→ (fsuc fzero) i j})
                 {!!}
  where -- i k r
  c : Cube (λ k r → ∣ north ∣) (λ _ _ → ∣ north ∣)
           (λ i r → emloop' (emloop 1) (~ r) (~ i)) (λ _ _ → ∣ north ∣ )
           {!ℤ/2→ (fsuc fzero)!} λ i k → emloop''2 (emloop 1) i1 k (~ i)
  c = {!!}

Cube₁ : I → I → I → EM (ℤ/2 ⨂ ℤ/2) 2
Cube₁ i j k =
  hcomp (λ r →
                λ {(i = i0) → ∣ north ∣
                 ; (i = i1) → ∣ north ∣ -- ∣ north ∣
                 ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
                 ; (j = i1) → emloop''2 (emloop 1) (~ r) k (~ i)
                 ; (k = i0) → FF (emloop 1 (~ i)) (emloop 1 (~ i))
                 ; (k = i1) → ℤ/2→ (fsuc fzero) i j})
                 (Cube₂ i j k)



-- Klein→-funα : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (α-raw x) (α-raw x))
--                                   ≡ Klein→-fun (0ₖ 2) refl refl (ℤ/2→ 1) x
-- Klein→-funα point = refl
-- Klein→-funα (line1 i) k = emloop' (cong α-raw line1) k i
-- Klein→-funα (line2 i) = refl
-- Klein→-funα (square i j) k =
--     hcomp (λ r →
--                 λ {(i = i0) → ∣ north ∣
--                  ; (i = i1) → ∣ north ∣
--                  ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
--                  ; (j = i1) → emloop' (λ i₁ → α-raw (square i₁ r)) k i
--                  ; (k = i0) → α-raw (square i (j ∧ r)) ⌣ₖ⊗ α-raw (square i (j ∧ r))
--                  ; (k = i1) → ℤ/2→ (fsuc fzero) i j})
--            {!!}
-- {-

-- Klein→-funα : (x : KleinBottle) → (_⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (α-raw x) (α-raw x))
--                                   ≡ Klein→-fun (0ₖ 2) refl refl (ℤ/2→ 1) x
-- Klein→-funα point = refl
-- Klein→-funα (line1 i) k = emloop' (cong α-raw line1) k i
-- Klein→-funα (line2 i) = refl
-- Klein→-funα (square i j) k =
--   hcomp (λ r →
--                 λ {(i = i0) → ∣ north ∣
--                  ; (i = i1) → ∣ north ∣
--                  ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
--                  ; (j = i1) → emloop' (λ i₁ → α-raw (square i₁ r)) k i
--                  ; (k = i0) → α-raw (square i (j ∧ r)) ⌣ₖ⊗ α-raw (square i (j ∧ r))
--                  ; (k = i1) → ℤ/2→ (fsuc fzero) i j})
--         (hcomp (λ r →
--                 λ {(i = i0) → ∣ north ∣
--                  ; (i = i1) → ∣ north ∣ -- ∣ north ∣
--                  ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
--                  ; (j = i1) → emloop''2 (emloop 1) (~ r) k (~ i)
--                  ; (k = i0) → FF (emloop 1 (~ i)) (emloop 1 (~ i))
--                  ; (k = i1) → ℤ/2→ (fsuc fzero) i j})
--         {!!})
--         {- (hcomp (λ r →
--                 λ {(i = i0) → ∣ north ∣
--                  ; (i = i1) → ∣ north ∣
--                  ; (j = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) (k ∨ ~ r) (~ i)
--                  {- doubleCompPath-filler (cong₂Funct FF (emloop 1) (emloop 1))
--                               ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
--                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i))
--                              (sym (rUnit refl)) r k (~ i) -}
--                  ; (j = i1) → {!emloop' (λ i₁ → α-raw (line1 i₁)) (k ∧ r) (~ i)!}
--                  {- doubleCompPath-filler (cong₂Funct FF (emloop 1) (emloop 1) ∙ sym (myF (emloop 1)))
--                               ((λ i → (λ j → ⌣ₖ-0ₖ⊗ 1 1 (emloop 1 j) i)
--                                ∙ λ j → 0ₖ-⌣ₖ⊗ 1 1 (emloop 1 j) i))
--                              (sym (rUnit refl)) r k (~ i) -}
--                  ; (k = i0) → emloop' (λ i₁ → α-raw (line1 i₁)) (~ r) (~ i)
--                  ; (k = i1) → {!!}})
--                {!!})) -}
--   where -- r i j
--   h : Cube {!λ!} {!!}
--     (λ r j → {!!}) {!!}
--     {!!} {!!}
--   h = {!!}
-- -}
-- {-
-- i = i0 ⊢ α-raw (line2 j) ⌣ₖ⊗ α-raw (line2 j)
-- i = i1 ⊢ α-raw (line2 j) ⌣ₖ⊗ α-raw (line2 j)
-- j = i0 ⊢ emloop' (λ i₁ → α-raw (line1 i₁)) k (~ i)
-- j = i1 ⊢ emloop' (λ i₁ → α-raw (line1 i₁)) k i
-- k = i0 ⊢ α-raw (square i j) ⌣ₖ⊗ α-raw (square i j)
-- k = i1 ⊢ ℤ/2→ (fsuc fzero) i j
-- -}

-- -- -- α⌣α non-zero?
-- -- -- is non-zero
-- -- Klein→-fun'' : (x : KleinBottle) → F (α-raw x) (β-raw x) ≡ ∣ north ∣
-- -- Klein→-fun'' point = Fr embase
-- -- Klein→-fun'' (line1 i) k = Fr (emloop 1 i) k 
-- -- Klein→-fun'' (line2 i) k = (Fr≡Fl ◁ cong Fl (emloop 1) ▷ sym Fr≡Fl) i k
-- -- Klein→-fun'' (square i j) k =
-- --   hcomp (λ r →
-- --       λ {(i = i0) → (Fr≡Fl ◁ (λ i₁ → Fl (emloop (fsuc fzero) i₁)) ▷
-- --           (λ i₁ → Fr≡Fl (~ i₁)))
-- --          j k
-- --                  ; (i = i1) → (Fr≡Fl ◁ (λ i₁ → Fl (emloop (fsuc fzero) i₁)) ▷
-- --           (λ i₁ → Fr≡Fl (~ i₁)))
-- --          j k
-- --                  ; (j = i0) → Fr (emloop-inv (AbGroup→Group ℤ/2) 1 r i) k
-- --                  ; (j = i1) → Fr (emloop (fsuc fzero) i) k
-- --                  ; (k = i0) → F (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j ∧ r) i) (emloop 1 j)
-- --                  ; (k = i1) → ∣ north ∣})
-- --         (PP i j k)
-- -- {-
-- -- i = i0 ⊢ (Fr≡Fl ◁ (λ i₁ → Fl (emloop (fsuc fzero) i₁)) ▷
-- --           (λ i₁ → Fr≡Fl (~ i₁)))
-- --          j k
-- -- i = i1 ⊢ (Fr≡Fl ◁ (λ i₁ → Fl (emloop (fsuc fzero) i₁)) ▷
-- --           (λ i₁ → Fr≡Fl (~ i₁)))
-- --          j k
-- -- j = i0 ⊢ Fr (emloop (fsuc fzero) (~ i)) k
-- -- j = i1 ⊢ Fr (emloop (fsuc fzero) i) k
-- -- k = i0 ⊢ F (α-raw (square i j)) (β-raw (square i j))
-- -- k = i1 ⊢ ∣ north ∣
-- -- -}
-- -- {-
-- --   KleinElim
-- --     (λ _ → ∣ north ∣)
-- --     (λ k i → ∣ rCancel (merid ptEM-raw) i k ∣)
-- --     (λ _ _ → ∣ north ∣)
-- --     λ k i j → hcomp (λ r →
-- --       λ {(i = i0) → {!⌣ₖ-0ₖ⊗ {G' = ℤ/2} {H' = ℤ/2} 1 1 (emloop 1 k) (r ∧ ~ j)!}
-- --                  ; (i = i1) → {!!}
-- --                  ; (j = i0) → cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})
-- --                                 (λ j → (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j) k))
-- --                                 (emloop 1) (~ r) i
-- --                  ; (j = i1) → {!cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})
-- --                                 (λ j → (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j) k))
-- --                                 (emloop 1) (~ r) !}
-- --                  ; (k = i0) → {!!}
-- --                  ; (k = i1) → {!!}})
-- --                      {!!}
-- -- -}

-- -- -- Klein→-fun'' : (x : KleinBottle) → _⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (α-raw x) (β-raw x) ≡ 0ₖ 2
-- -- -- Klein→-fun'' point i = ∣ north ∣
-- -- -- Klein→-fun'' (line1 i) k = ∣ rCancel (merid ptEM-raw) k i ∣
-- -- -- Klein→-fun'' (line2 i) k = ∣ north ∣
-- -- -- Klein→-fun'' (square i j) k =
-- -- --   {!  hcomp (λ r → λ {(i = i0) → cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})
-- -- --                                 (λ j → embase)
-- -- --                                 (emloop 1) (~ r ∧ ~ k) j
-- -- --                  ; (i = i1) → cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})
-- -- --                                 (λ j → embase)
-- -- --                                 (emloop 1) (~ r ∧ ~ k) j
-- -- --                  ; (j = i0) → {!∣ rCancel (merid ptEM-raw) (k ∧ r) i ∣!}
-- -- --                  ; (j = i1) → ? -- ∣ rCancel (merid ptEM-raw) k i ∣
-- -- --                  ; (k = i0) → cong₂Funct (_⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1})
-- -- --                                 (λ j → (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j) i))
-- -- --                                 (emloop 1) (~ r) j
-- -- --                  ; (k = i1) → ∣ north ∣})
-- -- --         {!!}!}
-- -- -- {-

-- -- -- -}

-- -- -- -- {-
-- -- -- -- Klein→-fun'' point = refl -- λ i → _⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (emloop 1 i) (emloop 1 i) -- refl
-- -- -- -- Klein→-fun'' (line1 i) j = emloop' (emloop 1) j i -- emloop' (emloop 1) j i -- gl' (emloop 1) j i
-- -- -- -- Klein→-fun'' (line2 i) = refl -- refl
-- -- -- -- Klein→-fun'' (square i j) k =
-- -- -- --   hcomp (λ r → λ {(i = i0) → ∣ north ∣ -- ∣ north ∣
-- -- -- --                  ; (i = i1) → ∣ north ∣ -- ∣ north ∣
-- -- -- --                  ; (j = i0) → {!cool i k r!} -- 
-- -- -- --                  ; (j = i1) → emloop' (emloop 1) (~ r ∨ k) i
-- -- -- --                  ; (k = i0) → emloop' (cong α-raw (λ i → square i j)) (~ r) i
-- -- -- --                  ; (k = i1) → ∣ north ∣})
-- -- -- --         ∣ north ∣
-- -- -- --   where
-- -- -- --   grr : ∀ {ℓ} {A B : Type ℓ} (g : A → A → B) {x : A} (f : (p : x ≡ x) → cong₂ g p p ≡ refl)
-- -- -- --     (p : x ≡ x) → p ≡ sym p
-- -- -- --     → Cube {A = B}
-- -- -- --          (λ _ _ → g x x) (λ _ _ → g x x)
-- -- -- --          (λ i r → f p (~ r) i) (λ _ _ → g x x)
-- -- -- --          (λ _ _ → g x x) λ i k → f (sym p) k (~ i)
-- -- -- --   grr g {x = x} f p st i k r =
-- -- -- --     hcomp (λ j → λ {(i = i0) → g x x
-- -- -- --                  ; (i = i1) → g x x
-- -- -- --                  ; (k = i0) → {!g (st j (~ i)) (st j (~ i))!}
-- -- -- --                  ; (k = i1) → {!!}
-- -- -- --                  ; (r = i0) → {!!}
-- -- -- --                  ; (r = i1) → f (st j) k (~ i)})
-- -- -- --            {!!}
-- -- -- -- {-
-- -- -- -- i = i0 ⊢ g x x
-- -- -- -- i = i1 ⊢ g x x
-- -- -- -- k = i0 ⊢ f p (~ r) i
-- -- -- -- k = i1 ⊢ g x x
-- -- -- -- r = i0 ⊢ g x x
-- -- -- -- r = i1 ⊢ f (sym p) k (~ i)
-- -- -- -- -}
-- -- -- --   bztt : ∀ {ℓ} {A B : Type ℓ} (g : A → A → B) {x : A} (f : (p : x ≡ x) → cong₂ g p p ≡ refl)
-- -- -- --          (p : x ≡ x) → (q : p ≡ sym p)
-- -- -- --       → (λ i → cong₂ g (q (~ i)) (q (~ i))) ∙ (f p) ≡ f (sym p)
-- -- -- --   bztt g f p q =
-- -- -- --       (λ i → (λ j → cong₂ g (q (~ j ∨ i)) (q (~ j ∨ i))) ∙ f (q i))
-- -- -- --     ∙ sym (lUnit _)

-- -- -- --   bzzt2 : ∀ {ℓ} {A B : Type ℓ} (g : A → A → B) {x : A} (f : (p : x ≡ x) → cong₂ g p p ≡ refl)
-- -- -- --          (q p : x ≡ x) → (s : q ≡ p) → f refl ≡ refl
-- -- -- --       → (λ i → cong₂ g (s i) (s i)) ∙ f p
-- -- -- --        ≡ {!!}
-- -- -- --          ∙ cong sym (f p) -- (λ i → sym (cong₂ g (q i) (q i))) ∙ cong sym (f p)
-- -- -- --   bzzt2 g {x} f q p = {!!} -- J> λ r → sym (lUnit _) ∙∙ r ∙ cong (cong sym) (sym r) ∙∙ lUnit _

-- -- -- --   bztt3 : ∀ {ℓ} {A B : Type ℓ} (g : A → A → B) {x y : A} (f : (p : x ≡ x) → cong₂ g p p ≡ refl)
-- -- -- --          (p : x ≡ x) (q : p ≡ sym p)
-- -- -- --          → {!!}
-- -- -- --          → cong sym (f p) ≡ f (sym p)
-- -- -- --   bztt3 = {!!}
-- -- -- -- -}


-- -- -- -- --   asd : ∀ {ℓ} {A B : Type ℓ} {x : A} (p : x ≡ x) (q : refl ≡ p)
-- -- -- -- --       → PathP {!!} (cong sym q) (sym q)
-- -- -- -- --   asd = {!!}


-- -- -- -- --   bzt : cong sym (emloop' (sym (emloop 1))) ≡ emloop' (emloop 1)
-- -- -- -- --   bzt i j k =
-- -- -- -- --     hcomp (λ r → λ {(i = i0) → emloop' (emloop-inv (AbGroup→Group ℤ/2) 1 r) j (~ k)
-- -- -- -- --                    ; (i = i1) → {!emloop' (emloop 1)!}
-- -- -- -- --                    ; (j = i0) → {!emloop' (emloop-inv (AbGroup→Group ℤ/2) 1 r)!}
-- -- -- -- --                    ; (j = i1) → {!!}
-- -- -- -- --                    ; (k = i0) → {!!}
-- -- -- -- --                    ; (k = i1) → {!!}})
-- -- -- -- --           {!!}

-- -- -- -- --   cool : Cube (λ k r → ∣ north ∣) (λ k r → ∣ north ∣)
-- -- -- -- --               (λ i r → emloop' (sym (emloop 1)) (~ r) i) (λ i r → ∣ north ∣) 
-- -- -- -- --               (λ _ _ → ∣ north ∣) λ i k →  emloop' (emloop (fsuc fzero)) k (~ i) -- λ i k → emloop' (emloop (fsuc fzero)) k (~ i)
-- -- -- -- --   cool i k r = 
-- -- -- -- --     hcomp (λ j → λ {(i = i0) → emloop' (sym (emloop 1)) (~ r) (~ j)
-- -- -- -- --                  ; (i = i1) → {!!}
-- -- -- -- --                  ; (k = i0) → emloop' (sym (emloop 1)) (~ r) (i ∨ ~ j)
-- -- -- -- --                  ; (k = i1) → {!!}
-- -- -- -- --                  ; (r = i0) → {!!}
-- -- -- -- --                  ; (r = i1) → {!emloop' (emloop (fsuc fzero)) k (~ i ∧ j) !}})
-- -- -- -- --            {!!} 
-- -- -- -- --     where
-- -- -- -- --     sd : emloop' (sym (emloop (fsuc fzero)))
-- -- -- -- --       ≡ (λ i j → _⌣ₖ⊗_ {G' = ℤ/2}{n = 1} {m = 1} (emloop-sym (AbGroup→Group ℤ/2) 1 (~ i) j) (emloop-sym (AbGroup→Group ℤ/2) 1 (~ i) j))
-- -- -- -- --       ∙ emloop' (emloop 1) 
-- -- -- -- --     sd = {!!}
-- -- -- -- -- {- -- cong α-raw (λ i → square i j)
-- -- -- -- -- i = i0 ⊢ α-raw (line2 j) ⌣ₖ⊗ α-raw (line2 j)
-- -- -- -- -- i = i1 ⊢ α-raw (line2 j) ⌣ₖ⊗ α-raw (line2 j)
-- -- -- -- -- j = i0 ⊢ emloop' (emloop (fsuc fzero)) k (~ i)
-- -- -- -- -- j = i1 ⊢ emloop' (emloop (fsuc fzero)) k i
-- -- -- -- -- k = i0 ⊢ α-raw (square i j) ⌣ₖ⊗ α-raw (square i j)
-- -- -- -- -- k = i1 ⊢ ∣ north ∣
-- -- -- -- -- -}

-- -- -- -- -- -- Klein→-fun' : (λ x →  _⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} (α-raw x) (α-raw x))
-- -- -- -- -- --               ≡ Klein→-fun (0ₖ {G = ℤ/2} 2)
-- -- -- -- -- --                      (λ i → _⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} (emloop 1 i) (emloop 1 i))
-- -- -- -- -- --                      refl (flipSquare (sym (br ∣ north ∣ λ i → _⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} (emloop 1 i) (emloop 1 i))))
-- -- -- -- -- -- Klein→-fun' = funExt λ { point → refl
-- -- -- -- -- --                        ; (line1 i) → refl
-- -- -- -- -- --                        ; (line2 i) → refl
-- -- -- -- -- --                        ; (square i j) → {!!}}
-- -- -- -- -- --   where
-- -- -- -- -- --   bzt : (λ j i → _⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j) i) (emloop-inv (AbGroup→Group ℤ/2) 1 (~ j) i))
-- -- -- -- -- --       ≡ sym (br ∣ north ∣ λ i → _⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} (emloop 1 i) (emloop 1 i))
-- -- -- -- -- --   bzt = {!!}



-- -- -- -- -- -- ⌣₂ : (x : EM ℤ/2 1) → (_⌣ₖ_ {G'' = Z/2r}{n = 1} {m = 1} x x) ≡ 0ₖ 2
-- -- -- -- -- -- ⌣₂ = elimGroupoid _ (λ _ → hLevelEM _ 2 _ _)
-- -- -- -- -- --        refl
-- -- -- -- -- --        (λ g → flipSquare (sym (br ∣ north ∣ₕ {!br ∣ north ∣!}) ∙ {!!}))
-- -- -- -- -- --        {!!}

-- -- -- -- -- -- α⌣α : (x : _) → ((α-raw x) ⌣ₖ (α-raw x)) ≡ {!!} 
-- -- -- -- -- -- α⌣α = {!!}
