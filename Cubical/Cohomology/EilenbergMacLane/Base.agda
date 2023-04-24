{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Base where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)

private
  variable
    ℓ ℓ' : Level

open IsAbGroup
open IsGroup
open IsSemigroup

open IsMonoid
open AbGroupStr

-- cohomology groups
coHom : (n : ℕ) (G : AbGroup ℓ) (A : Type ℓ') → Type _
coHom n G A = ∥ (A → EM G n) ∥₂

module _ {n : ℕ} {G : AbGroup ℓ} {A : Type ℓ'} where
  _+ₕ_ : coHom n G A → coHom n G A → coHom n G A
  _+ₕ_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x +ₖ g x) ∣₂

  -ₕ_ : coHom n G A → coHom n G A
  -ₕ_ = ST.map λ f x → -ₖ f x

  _-ₕ_ : coHom n G A → coHom n G A → coHom n G A
  _-ₕ_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x -ₖ g x) ∣₂

module _ (n : ℕ) {G : AbGroup ℓ} {A : Type ℓ'} where
  +ₕ-syntax : coHom n G A → coHom n G A → coHom n G A
  +ₕ-syntax = _+ₕ_

  -ₕ-syntax : coHom n G A → coHom n G A
  -ₕ-syntax = -ₕ_

  -'ₕ-syntax : coHom n G A → coHom n G A → coHom n G A
  -'ₕ-syntax = _-ₕ_

  syntax +ₕ-syntax n x y = x +[ n ]ₕ y
  syntax -ₕ-syntax n x = -[ n ]ₕ x
  syntax -'ₕ-syntax n x y = x -[ n ]ₕ y

module _ (n : ℕ) {G : AbGroup ℓ} {A : Type ℓ'} where
  0ₕ : coHom n G A
  0ₕ = ∣ (λ _ → 0ₖ n) ∣₂

  rUnitₕ : (x : coHom n G A) → x +ₕ 0ₕ ≡ x
  rUnitₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → rUnitₖ n (f x))

  lUnitₕ : (x : coHom n G A) → 0ₕ +[ n ]ₕ x ≡ x
  lUnitₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → lUnitₖ n (f x))

  commₕ : (x y : coHom n G A) → x +ₕ y ≡ y +ₕ x
  commₕ = ST.elim2 (λ _ _ → isSetPathImplicit)
           λ f g → cong ∣_∣₂ (funExt λ x → commₖ n (f x) (g x))

  assocₕ : (x y z : coHom n G A) → x +ₕ (y +ₕ z) ≡ (x +ₕ y) +ₕ z
  assocₕ = ST.elim3 (λ _ _ _ → isSetPathImplicit)
           λ f g h → cong ∣_∣₂ (funExt λ x → assocₖ n (f x) (g x) (h x))

  rCancelₕ : (x : coHom n G A) → x +ₕ (-ₕ x) ≡ 0ₕ
  rCancelₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → rCancelₖ n (f x))

  lCancelₕ : (x : coHom n G A) → (-ₕ x) +ₕ x ≡ 0ₕ
  lCancelₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → lCancelₖ n (f x))

coHomGr : (n : ℕ) (G : AbGroup ℓ) (A : Type ℓ') → AbGroup (ℓ-max ℓ ℓ')
fst (coHomGr n G A) = coHom n G A
0g (snd (coHomGr n G A)) = 0ₕ n
AbGroupStr._+_ (snd (coHomGr n G A)) = _+ₕ_
- snd (coHomGr n G A) = -ₕ_
is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A)))))) = squash₂
·Assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A)))))) = assocₕ n
·IdR (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A))))) = rUnitₕ n
·IdL (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A))))) = lUnitₕ n
·InvR (isGroup (isAbGroup (snd (coHomGr n G A)))) = rCancelₕ n
·InvL (isGroup (isAbGroup (snd (coHomGr n G A)))) = lCancelₕ n
+Comm (isAbGroup (snd (coHomGr n G A))) = commₕ n


-- ℤ/2 lemmas
+ₕ≡id-ℤ/2 : ∀ {ℓ}  {A : Type ℓ} (n : ℕ) (x : coHom n ℤ/2 A) → x +ₕ x ≡ 0ₕ n
+ₕ≡id-ℤ/2 n =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → +ₖ≡id-ℤ/2 n (f x))

-ₕConst-ℤ/2 : ∀{ℓ} (n : ℕ) {A : Type ℓ} (x : coHom n ℤ/2 A) → -ₕ x ≡ x
-ₕConst-ℤ/2 zero =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -Const-ℤ/2 (f x))
-ₕConst-ℤ/2 (suc n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -ₖConst-ℤ/2 n (f x))
