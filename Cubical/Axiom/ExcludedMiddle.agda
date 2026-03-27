module Cubical.Axiom.ExcludedMiddle where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Surjection

open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Empty as Empty

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Join as Join

open import Cubical.Relation.Nullary

open import Cubical.Axiom.Choice

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

LEM : (ℓ : Level) → Type (ℓ-suc ℓ)
LEM ℓ = ∀ {A : Type ℓ} → isProp A → Dec A

isPropLEM : isProp (LEM ℓ)
isPropLEM = isPropImplicitΠ (λ A → isPropΠ (λ isPropA → isPropDec isPropA))

-- Diaconescu's Theorem: LEM is implied by AC
module _ (ℓ : Level) where
  Diaconescu : (∀ (A : Type ℓ) → satAC∃ ℓ-zero ℓ A) → LEM ℓ
  Diaconescu AC {A} isPropA = PT.rec (isPropDec isPropA)
    (uncurry section→Dec)
    (invIsEq (AC (join 𝟚 A) (λ _ → 𝟚) λ a x → inB x ≡ a) inl-surj)
    where
    -- aka the closed modality of A
    𝟚/A : Type ℓ
    𝟚/A = join 𝟚 A
    inB : 𝟚 → join 𝟚 A
    inA : A → join 𝟚 A
    inB = inl
    inA = inr

    push' : ∀ (b1 b2 : 𝟚) → A → inB b1 ≡ inB b2
    push' b1 b2 x = push b1 x ∙ sym (push b2 x)

    𝟚/A-Quorec :
      (f : 𝟚 → C)
      → ((b1 b2 : 𝟚) (a : A) → f b1 ≡ f b2)
      → 𝟚/A → C
    𝟚/A-Quorec {C = C} f resp = Join.elim f (λ b → f true)
      λ b a → resp b true a

    module _ {b} where
      𝟚/A-effective-motive : ∀ b' → Type _
      𝟚/A-effective-motive b' = join (b ≡ b') A

      isProp-motive : ∀ {b'} → isProp (𝟚/A-effective-motive b')
      isProp-motive = isPropJoin (isSetBool _ _) isPropA

      𝟚/A-effective : ∀ {b'} → inB b ≡ inB b'
        → 𝟚/A-effective-motive b'
      𝟚/A-effective {b'} = λ p → transport (λ i → helper (p i)) (inl refl) where
        helper : 𝟚/A → Type ℓ
        helper = 𝟚/A-Quorec 𝟚/A-effective-motive
          λ b3 b4 a → hPropExt isProp-motive isProp-motive
            (λ _ → inr a)
            λ _ → inr a

    wlog-key : inB true ≡ inB false → A
    wlog-key p = elimProp {C = λ _ → A} (λ _ → isPropA)
      (λ true≡false → Empty.rec (true≢false true≡false)) (λ b → b)
        (𝟚/A-effective p)

    -- Key lemma: if inB equates two different booleans, then A holds.
    key : ∀ {b} → inB b ≡ inB (not b) → A
    key {false} x = wlog-key (sym x)
    key {true} x = wlog-key x

    inl-surj : isSurjection inB
    inl-surj = elimProp (λ _ → PT.squash₁)
      (λ b → ∣ (b , refl) ∣₁)
      λ a → ∣ (true , (push true a)) ∣₁

    module _ (inl⁻ : 𝟚/A → 𝟚) (inlinl⁻≡id : ∀ b → inB (inl⁻ b) ≡ b) where
      Dec-isRetractinB⁻ : Dec (retract inB inl⁻)
      Dec-isRetractinB⁻ = DecΠBool (λ b → (inl⁻ (inB b)) ≟ b)

      retr→¬A : retract inB inl⁻ → A → ⊥
      retr→¬A retr a = true≢false
        (isoFunInjective (iso inB inl⁻ inlinl⁻≡id retr) true false
        (push' true false a))

      ¬retr→A : (retract inB inl⁻ → ⊥) → A
      ¬retr→A ¬retr = key (uncurry case-analysis counter-example) where
        counter-example : Σ[ b ∈ 𝟚 ] ¬ inl⁻ (inB b) ≡ b
        counter-example = ¬ΠBool→¬Σ (λ b → inl⁻ (inB b) ≟ b) ¬retr

        case-analysis : ∀ b → ¬ inl⁻ (inB b) ≡ b → inB b ≡ inB (not b)
        case-analysis b bleh = sym (inlinl⁻≡id (inB b)) ∙ cong inB (¬≡b→≡notb _ _ bleh)

      section→Dec : Dec A
      section→Dec = decRec (λ f → no (retr→¬A f)) (λ x → yes (¬retr→A x))
        Dec-isRetractinB⁻
