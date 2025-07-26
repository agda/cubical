{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.WhiteheadProducts.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Int using (ℤ ; pos)

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim2)
open import Cubical.HITs.Truncation as TR hiding (elim2)
open import Cubical.HITs.S1

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Join
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Base

open Iso

-- Whitehead product (main definition)
[_∣_]-pre : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → join∙ (S₊∙ n) (S₊∙ m) →∙ X
[_∣_]-pre {X = X} {n = n} {m = m} f g =
  joinPinch∙ (S₊∙ n) (S₊∙ m) X
    (λ a b → (Ω→ g .fst (σS b) ∙ Ω→ f .fst (σS a)))

[_∣_] : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_] {n = n} {m = m} f g =
  [ f ∣ g ]-pre ∘∙ (sphere→Join n m , IsoSphereJoin⁻Pres∙ n m)

-- Homotopy group versions
[_∣_]π' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → π' (suc n) X → π' (suc m) X
       → π' (suc (n + m)) X
[_∣_]π' = elim2 (λ _ _ → squash₂) λ f g → ∣ [ f ∣ g ] ∣₂

-- Join version
[_∣_]π* : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → π' (suc n) X → π' (suc m) X
       → π* n m X
[_∣_]π* = elim2 (λ _ _ → squash₂) λ f g → ∣ [ f ∣ g ]-pre ∣₂

-- The two versions agree
whπ*≡whπ' : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (f : π' (suc n) X) (g : π' (suc m) X)
       → [ f ∣ g ]π' ≡ Iso.fun (Iso-π*-π' n m ) [ f ∣ g ]π*
whπ*≡whπ' {n = n} {m} = elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
  λ f g → TR.rec (squash₂ _ _)
          (λ p → cong ∣_∣₂ (ΣPathP (refl , (sym (rUnit _)
                ∙ cong (cong (fst [ f ∣ g ]-pre)) p
                ∙ rUnit _))))
          (help n m)
  where
  help : (n m : ℕ)
    → hLevelTrunc 1 (IsoSphereJoin⁻Pres∙ n m
                   ≡ snd (≃∙map (invEquiv∙ (joinSphereEquiv∙ n m))))
  help zero zero = ∣ invEq (congEquiv F) (λ _ → pos 0) ∣ₕ
    where
    F : (Path (join (S₊ 0) (S₊ 0)) (inr true) (inl true)) ≃ ℤ
    F = compEquiv ( (compPathlEquiv (push true true)))
                (compEquiv ((Ω≃∙ (isoToEquiv (IsoSphereJoin 0 0) , refl) .fst))
                (isoToEquiv ΩS¹Isoℤ))
  help zero (suc m) =
    isConnectedPath 1
      (isConnectedPath 2
        (isOfHLevelRetractFromIso 0
          (mapCompIso (IsoSphereJoin zero (suc m)))
            (isConnectedSubtr 3 m
              (subst (λ p → isConnected p (S₊ (2 + m)))
                (+-comm 3 m)
                (sphereConnected (2 + m))))) _ _) _ _ .fst
  help (suc n) m =
    isConnectedPath 1
      (isConnectedPath 2
        (isOfHLevelRetractFromIso 0
          (mapCompIso (IsoSphereJoin (suc n) m))
            (isConnectedSubtr 3 (n + m)
              (subst (λ p → isConnected p (S₊ (2 + (n + m))))
                (+-comm 3 (n + m)) (sphereConnected (2 + (n + m)))))) _ _) _ _ .fst

whπ'≡whπ* : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (f : π' (suc n) X) (g : π' (suc m) X)
       → Iso.inv (Iso-π*-π' n m) [ f ∣ g ]π' ≡ [ f ∣ g ]π*
whπ'≡whπ* {n = n} {m} f g =
  cong (inv (Iso-π*-π' n m)) (whπ*≡whπ' f g)
  ∙ Iso.leftInv (Iso-π*-π' n m) _

-- Whitehead product (as a composition)
joinTo⋁ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
 → join (typ A) (typ B)
 → (Susp (typ A) , north) ⋁ (Susp (typ B) , north)
joinTo⋁ (inl x) = inr north
joinTo⋁ (inr x) = inl north
joinTo⋁ {A = A} {B = B} (push a b i) =
     ((λ i → inr (σ B b i))
  ∙∙ sym (push tt)
  ∙∙ λ i → inl (σ A a i)) i

[_∣_]comp : ∀ {ℓ} {X : Pointed ℓ} {n m : ℕ}
       → (S₊∙ (suc n) →∙ X)
       → (S₊∙ (suc m) →∙ X)
       → S₊∙ (suc (n + m)) →∙ X
[_∣_]comp {n = n} {m = m} f g =
    (((f ∘∙ (inv (IsoSucSphereSusp n) , IsoSucSphereSusp∙ n))
  ∨→ (g ∘∙ (inv (IsoSucSphereSusp m) , IsoSucSphereSusp∙ m))
    , cong (fst f) (IsoSucSphereSusp∙ n) ∙ snd f)
  ∘∙ ((joinTo⋁ {A = S₊∙ n} {B = S₊∙ m} , sym (push tt))))
  ∘∙ (inv (IsoSphereJoin n m) , IsoSphereJoin⁻Pres∙ n m)
