{-# OPTIONS --safe #-}
module Cubical.Data.Prod.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Prod.Base
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_) hiding (prodIso ; toProdIso ; curryIso)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

-- Swapping is an equivalence

×≡ : {a b : A × B} → proj₁ a ≡ proj₁ b → proj₂ a ≡ proj₂ b → a ≡ b
×≡ {a = (a1 , b1)} {b = (a2 , b2)} id1 id2 i = (id1 i) , (id2 i)

swap : A × B → B × A
swap (x , y) = (y , x)

swap-invol : (xy : A × B) → swap (swap xy) ≡ xy
swap-invol (_ , _) = refl

isEquivSwap : (A : Type ℓ) (B : Type ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv (iso swap swap swap-invol swap-invol)

swapEquiv : (A : Type ℓ) (B : Type ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Type ℓ) (B : Type ℓ') → A × B ≡ B × A
swapEq A B = ua (swapEquiv A B)

private
  open import Cubical.Data.Nat

  -- As × is defined as a datatype this computes as expected
  -- (i.e. "C-c C-n test1" reduces to (2 , 1)). If × is implemented
  -- using Sigma this would be "transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)"
  test : ℕ × ℕ
  test = transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)

  testrefl : test ≡ (2 , 1)
  testrefl = refl

-- equivalence between the sigma-based definition and the inductive one
A×B≃A×ΣB : A × B ≃ A ×Σ B
A×B≃A×ΣB = isoToEquiv (iso (λ { (a , b) → (a , b)})
                          (λ { (a , b) → (a , b)})
                          (λ _ → refl)
                          (λ { (a , b) → refl }))

A×B≡A×ΣB : A × B ≡ A ×Σ B
A×B≡A×ΣB = ua A×B≃A×ΣB

-- truncation for products
isOfHLevelProd : (n : HLevel) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A × B)
isOfHLevelProd {A = A} {B = B} n h1 h2 =
  let h : isOfHLevel n (A ×Σ B)
      h = isOfHLevelΣ n h1 (λ _ → h2)
  in transport (λ i → isOfHLevel n (A×B≡A×ΣB {A = A} {B = B} (~ i))) h


×-≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
    → A ≃ C → B ≃ D → A × B ≃ C × D
×-≃ {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
   where
    φ : A × B → C × D
    φ (a , b) = equivFun f a , equivFun g b

    ψ : C × D → A × B
    ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

    η : section φ ψ
    η (c , d) i = secEq f c i , secEq g d i

    ε : retract φ ψ
    ε (a , b) i = retEq f a i , retEq g b i


{- Some simple ismorphisms -}

prodIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
       → Iso A C
       → Iso B D
       → Iso (A × B) (C × D)
Iso.fun (prodIso iAC iBD) (a , b) = (Iso.fun iAC a) , Iso.fun iBD b
Iso.inv (prodIso iAC iBD) (c , d) = (Iso.inv iAC c) , Iso.inv iBD d
Iso.rightInv (prodIso iAC iBD) (c , d) = ×≡ (Iso.rightInv iAC c) (Iso.rightInv iBD d)
Iso.leftInv (prodIso iAC iBD) (a , b) = ×≡ (Iso.leftInv iAC a) (Iso.leftInv iBD b)

toProdIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → Iso (A → B × C) ((A → B) × (A → C))
Iso.fun toProdIso = λ f → (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
Iso.inv toProdIso (f , g) = λ a → (f a) , (g a)
Iso.rightInv toProdIso (f , g) = refl
Iso.leftInv toProdIso b = funExt λ a → sym (×-η _)

curryIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → Iso (A × B → C) (A → B → C)
Iso.fun curryIso f a b = f (a , b)
Iso.inv curryIso f (a , b) = f a b
Iso.rightInv curryIso a = refl
Iso.leftInv curryIso f = funExt λ {(a , b) → refl}
