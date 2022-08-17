{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.CupProductProperties where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; -_ ; _+_ ; _·_ ; +Comm)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws

open PlusBis


module _
  {A : Type ℓ-zero}
  where

  open SubstLemma ℕ (λ n → coHom n A) (λ n → snd (coHomGroup n A)) public

  substG⌣ : (k : ℕ) → (a b : coHom k A) → (l : ℕ) → (x : k ≡ l)
            → substG (cong₂ _+'_ x x) (a ⌣ b) ≡ substG x a ⌣ substG x b
  substG⌣ k a b l x = J (λ l x → substG (cong₂ _+'_ x x) (a ⌣ b) ≡ substG x a ⌣ substG x b)
                        (transportRefl (a ⌣ b) ∙ sym (cong₂ _⌣_ (transportRefl a) (transportRefl b)))
                        x

  unitGroupEq : {n : ℕ} → (e : GroupIso (coHomGr n A) UnitGroup₀) →
                   (x y : coHom n A) → x ≡ y
  unitGroupEq {n} e x y = isOfHLevelRetractFromIso 1 (fst e) isPropUnit _ _

  unitGroupSEq : {n k : ℕ} → (r : suc k ≡ n) → (e : GroupIso (coHomGr (suc k) A) UnitGroup₀)
                    → (x y : coHom n A) → x ≡ y
  unitGroupSEq {n} {k} (r) e x y = x
                                          ≡⟨ sym (substSubst⁻ (λ X → coHom X A) r _) ⟩
                                      substG r (substG (sym r) x)
                                          ≡⟨ cong (substG r) (isOfHLevelRetractFromIso 1 (fst e) isPropUnit _ _) ⟩
                                      substG r (substG (sym r) y)
                                          ≡⟨ substSubst⁻ (λ X → coHom X A) r _ ⟩
                                      y ∎


module pres⌣
  {A : Type ℓ-zero}
  {n m : ℕ}
  (ϕₙ : ℤ → coHom n A)
  (ϕₙstr : IsGroupHom (ℤGroup .snd) ϕₙ (snd (coHomGr n A)))
  (ϕₘ : ℤ → coHom m A)
  (ϕₘstr : IsGroupHom (ℤGroup .snd) ϕₘ (snd (coHomGr m A)))
  (ϕₙ₊ₘ : ℤ → coHom (n +' m) A)
  (ϕₙ₊ₘstr : IsGroupHom (ℤGroup .snd) ϕₙ₊ₘ (snd (coHomGr (n +' m) A)))
  (mp-gen : ϕₙ (pos 1) ⌣ ϕₘ (pos 1) ≡ ϕₙ₊ₘ (pos 1))
  where

  open IsGroupHom

  mp-1-1 : ϕₙ (pos 1) ⌣ ϕₘ (- (pos 1)) ≡ ϕₙ₊ₘ (- (pos 1))
  mp-1-1 = ϕₙ (pos 1) ⌣ ϕₘ (- pos 1)          ≡⟨ cong (λ X → ϕₙ (pos 1) ⌣ X) (presinv ϕₘstr _) ⟩
           ϕₙ (pos 1) ⌣ (-ₕ (ϕₘ (pos 1)))     ≡⟨ sym (-ₕDistᵣ n m _ _) ⟩
           -ₕ (ϕₙ (pos 1) ⌣ ϕₘ (pos 1))       ≡⟨ cong (λ X → -ₕ X) mp-gen ⟩
           -ₕ (ϕₙ₊ₘ (pos 1))                   ≡⟨ sym (presinv ϕₙ₊ₘstr _) ⟩
            ϕₙ₊ₘ (- (pos 1)) ∎

  eq+-1 : (n : ℕ) → negsuc (suc n) ≡ (- (pos 1)) + negsuc n
  eq+-1 n = sym (+Comm (- pos 1) (negsuc n))

  ϕₙ-⌣ : (b : ℤ) → ϕₙ (pos 1) ⌣ ϕₘ b ≡ ϕₙ₊ₘ b
  ϕₙ-⌣ (pos zero) =
        ϕₙ (pos 1) ⌣ ϕₘ (pos zero)                                    ≡⟨ cong (λ X → ϕₙ (pos 1) ⌣ X) (pres1 ϕₘstr) ⟩
        ϕₙ (pos 1) ⌣ 0ₕ m                                              ≡⟨ ⌣-0ₕ n m _ ⟩
        0ₕ (n +' m)                                                    ≡⟨ sym (pres1 ϕₙ₊ₘstr) ⟩
        ϕₙ₊ₘ (pos zero) ∎
  ϕₙ-⌣ (pos (suc k)) =
        ϕₙ (pos 1) ⌣ ϕₘ (pos (suc k))                                  ≡⟨ refl ⟩
        ϕₙ (pos 1) ⌣ ϕₘ (pos k + pos 1)                                ≡⟨ cong (λ X → ϕₙ (pos 1) ⌣ X) (pres· ϕₘstr _ _) ⟩
        ϕₙ (pos 1) ⌣ (ϕₘ (pos k) +ₕ ϕₘ (pos 1))                        ≡⟨ leftDistr-⌣ n m _ _ _ ⟩
       (ϕₙ (pos 1) ⌣ ϕₘ (pos k)) +ₕ (ϕₙ (pos 1) ⌣ (ϕₘ (pos 1)))        ≡⟨ cong₂ _+ₕ_ (ϕₙ-⌣ (pos k)) mp-gen ⟩
        ϕₙ₊ₘ (pos k) +ₕ ϕₙ₊ₘ (pos 1)                                     ≡⟨ sym (pres· ϕₙ₊ₘstr _ _) ⟩
        ϕₙ₊ₘ (pos k + pos 1)                                             ≡⟨ refl ⟩
        ϕₙ₊ₘ (pos (suc k)) ∎
  ϕₙ-⌣ (negsuc zero) = mp-1-1
  ϕₙ-⌣ (negsuc (suc k)) =
        ϕₙ (pos 1) ⌣ ϕₘ (negsuc (suc k))                                 ≡⟨ cong (λ X → ϕₙ (pos 1) ⌣ ϕₘ X) (eq+-1 k) ⟩
        ϕₙ (pos 1) ⌣ ϕₘ ((- (pos 1)) + negsuc k)                         ≡⟨ cong (λ X → ϕₙ (pos 1) ⌣ X) (pres· ϕₘstr _ _) ⟩
        ϕₙ (pos 1) ⌣ (ϕₘ (- (pos 1)) +ₕ ϕₘ ( negsuc k))                   ≡⟨ leftDistr-⌣ n m _ _ _ ⟩
        (ϕₙ (pos 1) ⌣ ϕₘ (- (pos 1))) +ₕ (ϕₙ (pos 1) ⌣ ϕₘ ( negsuc k))    ≡⟨ cong₂ _+ₕ_ mp-1-1 (ϕₙ-⌣ (negsuc k)) ⟩
        (ϕₙ₊ₘ (- pos 1)) +ₕ (ϕₙ₊ₘ (negsuc k))                              ≡⟨ sym (pres· ϕₙ₊ₘstr _ _) ⟩
        ϕₙ₊ₘ ((- pos 1) + (negsuc k))                                      ≡⟨ cong ϕₙ₊ₘ (sym (eq+-1 k)) ⟩
        ϕₙ₊ₘ (negsuc (suc k)) ∎

  ϕₙ⌣ϕₘ : (a b : ℤ) → ϕₙ₊ₘ (a · b) ≡  ϕₙ a ⌣ ϕₘ b
  ϕₙ⌣ϕₘ (pos zero) b =
        ϕₙ₊ₘ (pos zero · b)                                   ≡⟨ refl ⟩
        ϕₙ₊ₘ (pos zero)                                       ≡⟨ pres1 ϕₙ₊ₘstr ⟩
        0ₕ (n +' m)                                           ≡⟨ sym (0ₕ-⌣ n m _) ⟩
        0ₕ n ⌣ ϕₘ b                                          ≡⟨ sym (cong (λ X → X ⌣ ϕₘ b) (pres1 ϕₙstr)) ⟩
        ϕₙ (pos zero) ⌣ ϕₘ b ∎
  ϕₙ⌣ϕₘ (pos (suc k)) b =
        ϕₙ₊ₘ (pos (suc k) · b)                                ≡⟨ refl ⟩
        ϕₙ₊ₘ (b + (pos k · b))                                ≡⟨ pres· ϕₙ₊ₘstr _ _ ⟩
        (ϕₙ₊ₘ b) +ₕ (ϕₙ₊ₘ (pos k · b))                        ≡⟨ cong₂ _+ₕ_ (sym (ϕₙ-⌣ b)) (ϕₙ⌣ϕₘ (pos k) b) ⟩
        (ϕₙ (pos 1) ⌣ ϕₘ b) +ₕ (ϕₙ (pos k) ⌣ ϕₘ b)           ≡⟨ sym (rightDistr-⌣ n m _ _ _) ⟩
        (ϕₙ (pos 1) +ₕ ϕₙ (pos k)) ⌣ ϕₘ b                     ≡⟨ sym (cong (λ X → X ⌣ ϕₘ b) (pres· ϕₙstr _ _)) ⟩
        ϕₙ (pos 1 + pos k) ⌣ ϕₘ b                             ≡⟨ cong (λ X → ϕₙ X ⌣ ϕₘ b) (+Comm (pos 1) (pos k)) ⟩
        ϕₙ (pos (suc k)) ⌣ ϕₘ b ∎
  ϕₙ⌣ϕₘ (negsuc zero) b =
        ϕₙ₊ₘ ((- (pos 1)) · b)                                 ≡⟨ refl ⟩
        (ϕₙ₊ₘ (- (pos 1 · b)))                                 ≡⟨ presinv ϕₙ₊ₘstr _ ⟩
        (-ₕ (ϕₙ₊ₘ (pos 1 · b)))                                 ≡⟨ cong -ₕ_ (sym (ϕₙ-⌣ _)) ⟩
        (-ₕ (ϕₙ (pos 1) ⌣ ϕₘ b))                               ≡⟨ -ₕDistₗ n m _ _ ⟩
        (-ₕ (ϕₙ (pos 1))) ⌣ (ϕₘ b)                             ≡⟨ cong (λ X → X ⌣ ϕₘ b) (sym (presinv ϕₙstr _)) ⟩
        ϕₙ (- (pos 1)) ⌣ ϕₘ b ∎
  ϕₙ⌣ϕₘ (negsuc (suc k)) b =
       ϕₙ₊ₘ (negsuc (suc k) · b)                                ≡⟨ refl ⟩
       ϕₙ₊ₘ ((- b) + negsuc k · b)                              ≡⟨ pres· ϕₙ₊ₘstr _ _ ⟩
       ϕₙ₊ₘ (- b) +ₕ ϕₙ₊ₘ (negsuc k · b)                        ≡⟨ cong (λ X → X +ₕ ϕₙ₊ₘ (negsuc k · b)) (presinv ϕₙ₊ₘstr _) ⟩
       (-ₕ (ϕₙ₊ₘ b)) +ₕ ϕₙ₊ₘ (negsuc k · b)                     ≡⟨ cong₂ _+ₕ_ (cong -ₕ_ (sym (ϕₙ-⌣ _))) (ϕₙ⌣ϕₘ _ _) ⟩
       (-ₕ (ϕₙ (pos 1) ⌣ ϕₘ b)) +ₕ (ϕₙ (negsuc k) ⌣ ϕₘ b)      ≡⟨ cong (λ X → X +ₕ (ϕₙ (negsuc k) ⌣ ϕₘ b)) (-ₕDistₗ n m _ _) ⟩
       ((-ₕ (ϕₙ (pos 1))) ⌣ ϕₘ b) +ₕ (ϕₙ (negsuc k) ⌣ ϕₘ b)    ≡⟨ cong (λ X → (X ⌣ ϕₘ b) +ₕ (ϕₙ (negsuc k) ⌣ ϕₘ b))
                                                                        (sym (presinv ϕₙstr _)) ⟩
       (ϕₙ (- (pos 1)) ⌣ ϕₘ b) +ₕ (ϕₙ (negsuc k) ⌣ ϕₘ b)       ≡⟨ sym (rightDistr-⌣ n m _ _ _) ⟩
       (ϕₙ (- (pos 1)) +ₕ ϕₙ (negsuc k)) ⌣ ϕₘ b                 ≡⟨ cong (λ X → X ⌣ ϕₘ b) (sym (pres· ϕₙstr _ _)) ⟩
       ϕₙ (- (pos 1) + negsuc k) ⌣ ϕₘ b                         ≡⟨ cong (λ X → X ⌣ ϕₘ b) (cong ϕₙ (sym (eq+-1 k))) ⟩
       ϕₙ (negsuc (suc k)) ⌣ ϕₘ b ∎
