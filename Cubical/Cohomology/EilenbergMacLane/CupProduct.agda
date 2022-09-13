{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.CupProduct where

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Data.Nat

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open RingStr

open PlusBis

private
  variable
    ℓ ℓ' : Level



module _ {G'' : Ring ℓ} {A : Type ℓ'} where
  private
    G' = Ring→AbGroup G''
    G = fst G'
    _+G_ = _+Gr_ (snd G')

    cup : (n m : ℕ) → EM G' n → EM G' m → EM G' (n +' m)
    cup n m x y = x ⌣ₖ y

  1ₕ : coHom zero G' A
  1ₕ = ∣ (λ _ → 1r (snd G'')) ∣₂

  _⌣_ : {n m : ℕ}
    → coHom n G' A → coHom m G' A → coHom (n +' m) G' A
  _⌣_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

  ⌣-0ₕ : (n m : ℕ) (x : coHom n G' A) → (x ⌣ 0ₕ m) ≡ 0ₕ (n +' m)
  ⌣-0ₕ n m =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (funExt λ x → ⌣ₖ-0ₖ n m (f x))

  0ₕ-⌣ : (n m : ℕ) (x : coHom m G' A) → (0ₕ n ⌣ x) ≡ 0ₕ (n +' m)
  0ₕ-⌣ n m =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (funExt λ x → 0ₖ-⌣ₖ n m (f x))

  ⌣-1ₕ : (n : ℕ) (x : coHom n G' A)
    → (x ⌣ 1ₕ) ≡ subst (λ n → coHom n G' A) (+'-comm zero n) x
  ⌣-1ₕ n =
    ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂
            (funExt λ x → ⌣ₖ-1ₖ n (f x)
           ∙ cong (transport (λ i → EM G' (+'-comm zero n i)))
                  (cong f (sym (transportRefl x))))

  1ₕ-⌣ : (n : ℕ) (x : coHom n G' A) → (1ₕ ⌣ x) ≡ x
  1ₕ-⌣ n = ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂
            (funExt λ x → 1ₖ-⌣ₖ n (f x))

  distrR⌣ : (n m : ℕ) (x y : coHom n G' A) (z : coHom m G' A)
          → ((x +ₕ y) ⌣ z) ≡ (x ⌣ z) +ₕ (y ⌣ z)
  distrR⌣ n m =
    ST.elim2 (λ _ _ → isSetΠ (λ _ → isSetPathImplicit))
      λ f g → ST.elim (λ _ → isSetPathImplicit)
        λ h → cong ∣_∣₂ (funExt (λ x → distrR⌣ₖ n m (f x) (g x) (h x)))

  distrL⌣ : (n m : ℕ) (x : coHom n G' A) (y z : coHom m G' A)
          → (x ⌣ (y +ₕ z)) ≡ (x ⌣ y) +ₕ (x ⌣ z)
  distrL⌣ n m =
    ST.elim (λ _ → isSetΠ2 (λ _ _ → isSetPathImplicit))
      λ f → ST.elim2 (λ _ _ → isSetPathImplicit)
        λ g h → cong ∣_∣₂ (funExt (λ x → distrL⌣ₖ n m (f x) (g x) (h x)))

  assoc⌣ : (n m l : ℕ)
       (x : coHom n G' A) (y : coHom m G' A) (z : coHom l G' A)
    → ((x ⌣ y) ⌣ z) ≡ subst (λ n → coHom n G' A) (+'-assoc n m l) (x ⌣ (y ⌣ z))
  assoc⌣ n m l =
    ST.elim (λ _ → isSetΠ2 (λ _ _ → isSetPathImplicit))
      λ f → ST.elim (λ _ → isSetΠ (λ _ → isSetPathImplicit))
        λ g → ST.elim (λ _ → isSetPathImplicit)
          λ h → cong ∣_∣₂ (funExt λ x → assoc⌣ₖ n m l (f x) (g x) (h x)
            ∙ cong (transport (λ i → EM G' (+'-assoc n m l i)))
               (cong (λ x → (f x ⌣ₖ (g x ⌣ₖ h x))) (sym (transportRefl x))))

-- dependent versions
module _ {G'' : Ring ℓ} {A : Type ℓ'} where
  private
    G' = Ring→AbGroup G''

  ⌣-1ₕDep : (n : ℕ) (x : coHom n G' A)
    → PathP (λ i → coHom (+'-comm zero n (~ i)) G' A) (x ⌣ 1ₕ) x
  ⌣-1ₕDep n x = toPathP {A = λ i → coHom (+'-comm zero n (~ i)) G' A}
                        (flipTransport (⌣-1ₕ n x))

  assoc⌣Dep : (n m l : ℕ)
       (x : coHom n G' A) (y : coHom m G' A) (z : coHom l G' A)
    → PathP (λ i → coHom (+'-assoc n m l (~ i)) G' A) ((x ⌣ y) ⌣ z) (x ⌣ (y ⌣ z))
  assoc⌣Dep n m l x y z = toPathP {A = λ i → coHom (+'-assoc n m l (~ i)) G' A}
                                  (flipTransport (assoc⌣ n m l x y z))
