{-
  A topological modality is by definition the nullification of a family of
  propositions. They are always lex modalities. We show that together
  with a couple of useful corollaries. We roughly follow the proofs
  from Rijke, Shulman, Spitters, Modalities in homotopy type theory.
-}

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

private variable
  ℓ ℓ' : Level

{-
  We use the formulation of lexness that the universe of null types is
  null itself.

  We choose the level of the universe of null types to be as low as
  possible such that it is null when the generators are propositions.
-}
NullType : Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓs)) ℓα )
NullType {ℓ} = Σ[ X ∈ Type (ℓ-max ℓ ℓs) ] isNull S X

{-
  We can show that the universe is separated in general.
-}
NullType≡isNull : (X Y : NullType {ℓ = ℓ}) → isNull S (X ≡ Y)
NullType≡isNull {ℓ = ℓ} X Y =
  equivPreservesIsNull (invEquiv e) (isNullEquiv (snd X) (snd Y))
  where
    e : (X ≡ Y) ≃ ((fst X) ≃ (fst Y))
    e =
      X ≡ Y ≃⟨ invEquiv (Σ≡PropEquiv λ _ → isPropIsNull) ⟩
      (fst X) ≡ (fst Y) ≃⟨ univalence ⟩
      (fst X) ≃ (fst Y) ■

module _ (isPropS : (α : A) → isProp (S α)) where
  {- Recall that a type Z is injective when we can extend any map S α → Z to
     an element of Z. We show this is the case for Z = NullType.
  -}
  NullTypeIsInj : (α : A) → hasSection (const {A = NullType {ℓ = ℓ}} {B = S α})
  fst (NullTypeIsInj α) f = ((z : S α) → fst (f z)) , isNullΠ (λ z → snd (f z))
  snd (NullTypeIsInj α) f = funExt (λ z → Σ≡Prop (λ _ → isPropIsNull) (ua (e z)))
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

  isNullNullTypes : isNull S (NullType {ℓ = ℓ})
  isNullNullTypes {ℓ} =
    SeparatedAndInjective→Null (NullType {ℓ = ℓ})
      (NullType≡isNull {ℓ = ℓ}) (NullTypeIsInj {ℓ = ℓ})

  topUnitWeaklyEmb : {X : Type ℓ} (x y : X) → Path (Null S X) ∣ x ∣ ∣ y ∣ ≃ Null S (x ≡ y)
  topUnitWeaklyEmb {ℓ} {X} x y = extensionToE ∣ y ∣
    where
      E : (Null S X) → NullType {ℓ = ℓ-max ℓ ℓα}
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
  topPreservesHLevel zero = NullPreservesContr
  topPreservesHLevel (suc zero) = NullPreservesProp
  topPreservesHLevel (suc (suc n)) l =
    elim (λ x → isNullΠ (λ y → isNullIsOfHLevel _ (isNull≡ (isNull-Null S))))
      (λ x → elim (λ y → isNullIsOfHLevel _ (isNull≡ (isNull-Null S)))
        (λ y → isOfHLevelRespectEquiv (suc n) (invEquiv (topUnitWeaklyEmb x y))
          (topPreservesHLevel (suc n) (l x y))))
