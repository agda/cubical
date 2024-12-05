{-# OPTIONS --safe --lossy-unification #-}

{-
  The finitary Hilton–Milnor splitting
    Ω(X ⋁ Y) ≃ ΩX × ΩY × ΩΣ(ΩY ⋀ ΩX)
  for pointed types X and Y.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToPath; isoToEquiv)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Homotopy.Loopspace

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge

module Cubical.Homotopy.HiltonMilnor {ℓ} (X∙@(X , x₀) Y∙@(Y , y₀) : Pointed ℓ) where

fun : X∙ ⋁ Y∙ → typ X∙ × typ Y∙
fun = ⋁↪ {A = X∙} {B = Y∙}

-- The required section, given by concatenating the paths
sect : typ (Ω (X∙ ×∙ Y∙)) → typ (Ω (X∙ ⋁∙ₗ Y∙))
sect p = cong (inl ∘ fst) p ∙ push _ ∙ cong (inr ∘ snd) p ∙ sym (push _)

rInv : ∀ c → cong fun (sect c) ≡ c
rInv c = congFunct fun _ _
  ∙ cong (cong (fun ∘ inl ∘ fst) c ∙_)
    (congFunct fun (push _) _
    ∙ sym (lUnit _)
    ∙ lemma₂  -- can't be inlined because lossy unification
    ∙ sym (rUnit _))
  ∙ lemma₁ (cong fst c) (cong snd c)
  where
    lemma₁ : (p : x₀ ≡ x₀) (q : y₀ ≡ y₀)
      → cong (_, y₀) p ∙ cong (x₀ ,_) q ≡ cong₂ _,_ p q
    lemma₁ p q = cong ΣPathP (ΣPathP
      (congFunct fst (cong (_, y₀) p) _ ∙ sym (rUnit _) ,
      congFunct snd (cong (_, y₀) p) _ ∙ sym (lUnit _)))

    lemma₂ : cong fun
      (cong (inr ∘ snd) c ∙ sym (push _))
      ≡ cong (⋁↪ ∘ inr ∘ snd) c ∙ refl
    lemma₂ = congFunct fun _ _

-- Now the splitting lemma gives us something in terms of the fiber of ⋁↪.
-- So we try to characterize the type.
module _ where
  open FlatteningLemma
    (λ (_ : Unit) → x₀) (λ _ → y₀)
    (λ x → (x , y₀) ≡ (x₀ , y₀)) (λ y → (x₀ , y) ≡ (x₀ , y₀))
    (λ _ → idEquiv _)

  private
    E≡ : ∀ u → E u ≡ (⋁↪ u ≡ (x₀ , y₀))
    E≡ (inl x) = refl
    E≡ (inr x) = refl
    E≡ (push a i) j = uaIdEquiv {A = typ (Ω (X∙ ×∙ Y∙))} j i

    Pushout≃ : Pushout Σf Σg ≃ join (typ (Ω Y∙)) (typ (Ω X∙))
    Pushout≃ = pushoutEquiv _ _ _ _
        (ΣUnit _ ∙ₑ invEquiv ΣPathP≃PathPΣ ∙ₑ Σ-swap-≃)
        (Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ ∙ₑ Σ-swap-≃)
          ∙ₑ invEquiv Σ-assoc-≃
          ∙ₑ invEquiv (fiberProjEquiv X _ x₀))
        (Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ)
          ∙ₑ invEquiv Σ-assoc-≃
          ∙ₑ invEquiv (fiberProjEquiv Y _ y₀))
        (funExt λ _ → transportRefl _)
        (funExt λ _ → transportRefl _)
      ∙ₑ joinPushout≃join _ _

  fiber⋁↪≃ : fiber fun (x₀ , y₀) ≃ join (typ (Ω Y∙)) (typ (Ω X∙))
  fiber⋁↪≃ = Σ-cong-equiv-snd (λ a → pathToEquiv (sym (E≡ a)))
    ∙ₑ flatten ∙ₑ Pushout≃

HMSplit : typ (Ω (X∙ ⋁∙ₗ Y∙)) ≡ typ (Ω X∙) × typ (Ω Y∙) × typ (Ω (Susp∙ (Ω Y∙ ⋀ Ω X∙)))
HMSplit = splitting
  ∙ cong₂ (λ A B∙ → A × typ (Ω B∙)) (sym ΣPathP≡PathPΣ)
      (ua∙ fiber⋁↪≃ refl ∙ ΣPathP
        (sym (isoToPath SmashJoinIso) , toPathP refl))
  ∙ ua Σ-assoc-≃
  where open Split (inl x₀) ⋁↪ sect rInv
