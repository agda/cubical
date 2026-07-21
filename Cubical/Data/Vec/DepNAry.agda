{-# OPTIONS --safe #-}
module Cubical.Data.Vec.DepNAry where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Vec.NAry using (nAryLevel)

private variable
  ℓ ℓ' : Level
  n : ℕ
  A : Type ℓ
  B : Vec A n → Type ℓ'

nAryOp : (n : ℕ) → (A : Type ℓ) → (Vec A n → Type ℓ') → Type (nAryLevel ℓ ℓ' n)
nAryOp zero A B = B []
nAryOp (suc n) A B = (a : A) → nAryOp n A (B ∘ (a ∷_))

_$ⁿ_ : nAryOp n A B → (xs : Vec A n) → B xs
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

curryⁿ : ((xs : Vec A n) → B xs) → nAryOp n A B
curryⁿ {n = zero}  f   = f []
curryⁿ {n = suc n} f x = curryⁿ (λ xs → f (x ∷ xs))

$ⁿ-curryⁿ : {B : Vec A n → Type ℓ'} (f : (xs : Vec A n) → B xs) → _$ⁿ_ (curryⁿ f) ≡ f
$ⁿ-curryⁿ {n = zero} f  = funExt λ { [] → refl }
$ⁿ-curryⁿ {n = suc n} f = funExt λ { (x ∷ xs) i → $ⁿ-curryⁿ {n = n} (λ ys → f (x ∷ ys)) i xs}

curryⁿ-$ⁿ : (f : nAryOp {ℓ = ℓ} {ℓ' = ℓ'} n A B) → curryⁿ {A = A} {B = B} (_$ⁿ_ f) ≡ f
curryⁿ-$ⁿ {n = zero} f  = refl
curryⁿ-$ⁿ {n = suc n} f = funExt λ x → curryⁿ-$ⁿ {n = n} (f x)

nAryOp≃VecFun : nAryOp n A B ≃ ((xs : Vec A n) → B xs)
nAryOp≃VecFun {n = n} = isoToEquiv f
  where
  f : Iso (nAryOp n A B) ((xs : Vec A n) → B xs)
  Iso.fun f      = _$ⁿ_
  Iso.inv f      = curryⁿ
  Iso.rightInv f = $ⁿ-curryⁿ
  Iso.leftInv f  = curryⁿ-$ⁿ {n = n}
