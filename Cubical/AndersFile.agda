{-# OPTIONS --cubical --safe #-}
module Cubical.AndersFile where



open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat
open import Cubical.Data.HomotopyGroup

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


FunLR : (n : ℕ) {f : A → B} →
        ((typ ((Ω^ (suc n)) ((A → B) , f))) →
        (((x : A) → (typ ((Ω^ (suc n)) (B , f x))))))
LR-id : (n : ℕ) {f : A → B} → FunLR n {f} refl ≡ (λ x → refl)
FunLR n {f} = {!!}
LR-id n {f} = {!!}


FunRL : (n : ℕ) {f : A → B} →
        ((x : A) → (typ ((Ω^ (suc n)) (B , f x)))) →
        ((typ ((Ω^ (suc n)) ((A → B) , f))))
RL-id : (n : ℕ) {f : A → B} →
        FunRL n (λ x → pt (((Ω^ (suc n)) (B , f x)))) ≡ pt  ((Ω^ (suc n)) ((A → B) , f))
FunRL n {f} = {!!}
RL-id n {f} = {!!}


wantToShow : (n : ℕ) (f : A → B) →
             ((x : A) → (typ ((Ω^ n) (B , f x)))) ≡ (typ ((Ω^ n) ((A → B) , f)))
wantToShow n f = {!!}


