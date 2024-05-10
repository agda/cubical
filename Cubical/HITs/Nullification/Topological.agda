{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

open import Cubical.HITs.Nullification.Base
open import Cubical.HITs.Nullification.Properties

module Cubical.HITs.Nullification.Topological
  {ℓα ℓs}
  {A : Type ℓα}
  (S : A → Type ℓs)
  where

variable
  ℓ ℓ' : Level

nullTypes : Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓs)) ℓα )
nullTypes {ℓ} = Σ[ X ∈ Type (ℓ-max ℓ ℓs) ] isNull S X

nullTypeEquivIsNull : (A : nullTypes {ℓ = ℓ}) (B : nullTypes {ℓ = ℓ'}) →
  isNull S ((fst A) ≃ (fst B))
nullTypeEquivIsNull A B = isNullΣ (isNullΠ (λ _ → snd B)) (isNullIsEquiv (snd A) (snd B))

nullTypes≡isNull : (A B : nullTypes {ℓ = ℓ}) → isNull S (A ≡ B)
nullTypes≡isNull {ℓ = ℓ} A B =
  equivPreservesIsNull (invEquiv e) (nullTypeEquivIsNull {ℓ = ℓ} {ℓ' = ℓ} A B)
  where
    e : (A ≡ B) ≃ ((fst A) ≃ (fst B))
    e =
      A ≡ B ≃⟨ invEquiv (Σ≡PropEquiv λ _ → isPropIsNull) ⟩
      (fst A) ≡ (fst B) ≃⟨ univalence ⟩
      (fst A) ≃ (fst B) ■

module _ {ℓ} (isPropS : (α : A) → isProp (S α)) where
  injNullTypes : (α : A) → hasSection (const {A = nullTypes {ℓ = ℓ}} {B = S α})
  fst (injNullTypes α) f = ((z : S α) → fst (f z)) , isNullΠ (λ z → snd (f z))
  snd (injNullTypes α) f = funExt (λ z → Σ≡Prop (λ _ → isPropIsNull) (ua (e z)))
    where
      e : (z : S α) → ((z : S α) → fst (f z)) ≃ fst (f z)
      e z =
        ((z : S α) → fst (f z))
          ≃⟨ invEquiv
            (equivΠ
              (invEquiv
                (isContr→≃Unit
                  (inhProp→isContr z (isPropS α)))) λ _ → idEquiv _) ⟩
        (Unit → fst (f z))
          ≃⟨ ΠUnit (λ _ → fst (f z)) ⟩
        fst (f z)
          ■

  isNullNullTypes : isNull S (nullTypes {ℓ = ℓ})
  isNullNullTypes =
    SeparatedAndInjective→Null (nullTypes {ℓ = ℓ})
      (nullTypes≡isNull {ℓ = ℓ}) (injNullTypes)
