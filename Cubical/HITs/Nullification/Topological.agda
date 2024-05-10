{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)

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

module _ (isPropS : (α : A) → isProp (S α)) where
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
  isNullNullTypes {ℓ} =
    SeparatedAndInjective→Null (nullTypes {ℓ = ℓ})
      (nullTypes≡isNull {ℓ = ℓ}) (injNullTypes {ℓ = ℓ})


  topUnitWeaklyEmb : {X : Type ℓ} (x y : X) → Path (Null S X) ∣ x ∣ ∣ y ∣ ≃ Null S (x ≡ y)
  topUnitWeaklyEmb {ℓ} {X} x y = extensionToE ∣ y ∣
    where
      E : (Null S X) → nullTypes {ℓ = ℓ-max ℓ ℓα}
      E = rec (isNullNullTypes {ℓ = ℓ-max ℓ ℓα}) (λ y' → (Null S (x ≡ y')) , isNull-Null S)

      extensionToE : (z : Null S X) → (∣ x ∣ ≡ z) ≃ fst (E z)
      extensionToE = recognizeId (fst ∘ E) ∣ refl ∣
        ((∣ x ∣ , ∣ refl ∣) ,
          (uncurry
            (elim (λ _ → isNullΠ isnull)
              λ y → elim isnull (J (λ y p → (∣ x ∣ , ∣ refl ∣) ≡ (∣ y ∣ , ∣ p ∣)) refl))))

        where
          isnull : {z : Null S X} → (e : fst (E z)) →
            isNull S (Path (Σ _ (fst ∘ E)) (∣ x ∣ , ∣ refl ∣) (z , e))
          isnull e = isNull≡ (isNullΣ (isNull-Null S) (λ z → snd (E z)))

  topUnitWeaklyInj : {X : Type ℓ} (x y : X) → Path (Null S X) ∣ x ∣ ∣ y ∣ → Null S (x ≡ y)
  topUnitWeaklyInj x y = fst (topUnitWeaklyEmb x y)

  topPreservesHLevel : {X : Type ℓ} (n : HLevel) → (isOfHLevel n X) → isOfHLevel n (Null S X)
  topPreservesHLevel zero l =
    ∣ fst l ∣ , elim (λ _ → isNull≡ (isNull-Null S)) (λ y → cong ∣_∣ (snd l y))
  topPreservesHLevel (suc zero) l =
    elim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null S)))
      (λ x → elim (λ y → isNull≡ (isNull-Null S)) (λ y → cong ∣_∣ (l x y)))
  topPreservesHLevel (suc (suc n)) l =
    elim (λ x → isNullΠ (λ y → isNullIsOfHLevel _ (isNull≡ (isNull-Null S))))
      (λ x → elim (λ y → isNullIsOfHLevel _ (isNull≡ (isNull-Null S)))
        (λ y → isOfHLevelRespectEquiv (suc n) (invEquiv (topUnitWeaklyEmb x y))
          (topPreservesHLevel (suc n) (l x y))))
