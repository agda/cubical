{-

This file contains:
  -- The inductive family 𝕁 can be constructed by iteratively applying pushouts.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.PushoutFormula where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.James.Inductive.Base
  renaming (𝕁ames to 𝕁amesContruction)

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  private
    𝕁ames = 𝕁amesContruction (X , x₀)

  Push𝕁ames : (n : ℕ) → Type ℓ
  Push𝕁ames n = Pushout {A = 𝕁ames n} {B = X × 𝕁ames n} (λ xs → x₀ , xs) incl

  X→𝕁ames1 : X → 𝕁ames 1
  X→𝕁ames1 x = x ∷ []

  𝕁ames1→X : 𝕁ames 1 → X
  𝕁ames1→X (x ∷ []) = x
  𝕁ames1→X (incl []) = x₀
  𝕁ames1→X (unit [] i) = x₀

  X→𝕁ames1→X : (x : X) → 𝕁ames1→X (X→𝕁ames1 x) ≡ x
  X→𝕁ames1→X x = refl

  𝕁ames1→X→𝕁ames1 : (xs : 𝕁ames 1) → X→𝕁ames1 (𝕁ames1→X xs) ≡ xs
  𝕁ames1→X→𝕁ames1 (x ∷ []) = refl
  𝕁ames1→X→𝕁ames1 (incl []) i = unit [] (~ i)
  𝕁ames1→X→𝕁ames1 (unit [] i) j = unit [] (i ∨ ~ j)

  leftMap  : {n : ℕ} → Push𝕁ames n → X × 𝕁ames (1 + n)
  leftMap  (inl (x , xs)) = x , incl xs
  leftMap  (inr ys) = x₀ , ys
  leftMap  (push xs i) = x₀ , incl xs

  rightMap : {n : ℕ} → Push𝕁ames n → 𝕁ames (1 + n)
  rightMap (inl (x , xs)) = x ∷ xs
  rightMap (inr ys) = ys
  rightMap (push xs i) = unit xs (~ i)

  PushMap : {n : ℕ} → Pushout {A = Push𝕁ames n} leftMap rightMap → 𝕁ames (2 + n)
  PushMap (inl (x , xs)) = x ∷ xs
  PushMap (inr ys) = incl ys
  PushMap (push (inl (x , xs)) i) = incl∷ x xs (~ i)
  PushMap (push (inr ys) i) = unit ys (~ i)
  PushMap (push (push xs i) j) = coh xs (~ i) (~ j)

  PushInv : {n : ℕ} → 𝕁ames (2 + n) → Pushout {A = Push𝕁ames n} leftMap rightMap
  PushInv (x ∷ xs) = inl (x , xs)
  PushInv (incl xs) = inr xs
  PushInv (incl∷ x xs i) = push (inl (x , xs)) (~ i)
  PushInv (unit xs i) = push (inr xs) (~ i)
  PushInv (coh xs i j) = push (push xs (~ i)) (~ j)

  PushInvMapInv : {n : ℕ}(xs : 𝕁ames (2 + n)) → PushMap (PushInv xs) ≡ xs
  PushInvMapInv (x ∷ xs) = refl
  PushInvMapInv (incl xs) = refl
  PushInvMapInv (incl∷ x xs i) = refl
  PushInvMapInv (unit xs i) = refl
  PushInvMapInv (coh xs i j) = refl

  PushMapInvMap : {n : ℕ}(xs : Pushout {A = Push𝕁ames n} leftMap rightMap) → PushInv (PushMap xs) ≡ xs
  PushMapInvMap (inl (x , xs)) = refl
  PushMapInvMap (inr ys) = refl
  PushMapInvMap (push (inl (x , xs)) i) = refl
  PushMapInvMap (push (inr ys) i) = refl
  PushMapInvMap (push (push xs i) j) = refl

  -- The type family 𝕁ames can be constructed by iteratively using pushouts

  𝕁ames0≃ : 𝕁ames 0 ≃ Unit
  𝕁ames0≃ = isoToEquiv (iso (λ { [] → tt }) (λ { tt → [] }) (λ { tt → refl }) (λ { [] → refl }))

  𝕁ames1≃ : 𝕁ames 1 ≃ X
  𝕁ames1≃ = isoToEquiv (iso 𝕁ames1→X X→𝕁ames1 X→𝕁ames1→X 𝕁ames1→X→𝕁ames1)

  𝕁ames2+n≃ : (n : ℕ) → 𝕁ames (2 + n) ≃ Pushout leftMap rightMap
  𝕁ames2+n≃ n = isoToEquiv (iso PushInv PushMap PushMapInvMap PushInvMapInv)
