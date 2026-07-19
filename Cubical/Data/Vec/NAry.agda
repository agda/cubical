module Cubical.Data.Vec.NAry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

nAryLevel : Level → Level → ℕ → Level
nAryLevel ℓ₁ ℓ₂ zero    = ℓ₂
nAryLevel ℓ₁ ℓ₂ (suc n) = ℓ-max ℓ₁ (nAryLevel ℓ₁ ℓ₂ n)

nAryOp : (n : ℕ) → Type ℓ → Type ℓ' → Type (nAryLevel ℓ ℓ' n)
nAryOp zero A B    = B
nAryOp (suc n) A B = A → nAryOp n A B


_$ⁿ_ : ∀ {n} → nAryOp n A B → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

curryⁿ : ∀ {n} → (Vec A n → B) → nAryOp n A B
curryⁿ {n = zero}  f   = f []
curryⁿ {n = suc n} f x = curryⁿ (λ xs → f (x ∷ xs))

$ⁿ-curryⁿ : ∀ {n} (f : Vec A n → B) → _$ⁿ_ (curryⁿ f) ≡ f
$ⁿ-curryⁿ {n = zero} f  = funExt λ { [] → refl }
$ⁿ-curryⁿ {n = suc n} f = funExt λ { (x ∷ xs) i → $ⁿ-curryⁿ {n = n} (λ ys → f (x ∷ ys)) i xs}

curryⁿ-$ⁿ : ∀ {n} (f : nAryOp {ℓ = ℓ} {ℓ' = ℓ'} n A B) → curryⁿ {A = A} {B = B} (_$ⁿ_ f) ≡ f
curryⁿ-$ⁿ {n = zero} f  = refl
curryⁿ-$ⁿ {n = suc n} f = funExt λ x → curryⁿ-$ⁿ {n = n} (f x)

nAryOp≃VecFun : ∀ {n} → nAryOp n A B ≃ (Vec A n → B)
nAryOp≃VecFun {n = n} = isoToEquiv f
  where
  f : Iso (nAryOp n A B) (Vec A n → B)
  Iso.fun f      = _$ⁿ_
  Iso.inv f      = curryⁿ
  Iso.rightInv f = $ⁿ-curryⁿ
  Iso.leftInv f  = curryⁿ-$ⁿ {n = n}

-- In order to apply ua to nAryOp≃VecFun we probably need to change
-- the base-case of nAryLevel to "ℓ-max ℓ₁ ℓ₂". This will make it
-- necessary to add lots of Lifts in zero cases so it's not done yet,
-- but if the Path is ever needed then it might be worth to do.
