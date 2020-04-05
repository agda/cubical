{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.Modalities.Lex where

open import Cubical.Foundations.Everything


module LexModality
  (◯ : ∀ {ℓ} → Type ℓ → Type ℓ)
  (η : ∀ {ℓ} {A : Type ℓ} → A → ◯ A)
  (isModal : ∀ {ℓ} → Type ℓ → Type ℓ)
  (let isModalFam = λ {ℓ ℓ′ : Level} {A : Type ℓ} (B : A → Type ℓ′) → (x : A) → isModal (B x))
  (idemp : ∀ {ℓ} {A : Type ℓ} → isModal (◯ A))
  (≡-modal : ∀ {ℓ} {A : Type ℓ} {x y : A} (A-mod : isModal A) → isModal (x ≡ y))
  (◯-ind : ∀ {ℓ ℓ′} {A : Type ℓ} {B : ◯ A → Type ℓ′} (B-mod : isModalFam B) (f : (x : A) → B (η x)) → ([x] : ◯ A) → B [x])
  (◯-ind-β : ∀ {ℓ ℓ′} {A : Type ℓ} {B : ◯ A → Type ℓ′} (B-mod : isModalFam B) (f : (x : A) → B (η x)) (x : A) → ◯-ind B-mod f (η x) ≡ f x)
  (let Type◯ = λ (ℓ : Level) → Σ (Type ℓ) isModal)
  (◯-lex : ∀ {ℓ} → isModal (Type◯ ℓ))
  where

  η-at : ∀ {ℓ} (A : Type ℓ) → A → ◯ A
  η-at _ = η


  module _ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (B-mod : isModal B) (f : A → B) where
    ◯-rec : ◯ A → B
    ◯-rec = ◯-ind (λ _ → B-mod) f

    ◯-rec-β : (x : A) → ◯-rec (η x) ≡ f x
    ◯-rec-β = ◯-ind-β (λ _ → B-mod) f

  module _ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f : A → B) where
    ◯-map : ◯ A → ◯ B
    ◯-map = ◯-rec idemp λ x → η (f x)

    ◯-map-β : (x : A) → ◯-map (η x) ≡ η (f x)
    ◯-map-β x = ◯-rec-β idemp _ x


  module η-at-modal {ℓ} (A : Type ℓ) (A-mod : isModal A) where
    inv : ◯ A → A
    inv = ◯-rec A-mod λ x → x

    is-section : section inv η
    is-section = ◯-rec-β _ _

    is-retract : retract inv η
    is-retract = ◯-ind (λ _ → ≡-modal idemp) λ x i → η (is-section x i)

    η-iso : Iso A (◯ A)
    Iso.fun η-iso = η
    Iso.inv η-iso = inv
    Iso.rightInv η-iso = is-retract
    Iso.leftInv η-iso = is-section

    η-is-equiv : isEquiv (η-at A)
    η-is-equiv = isoToIsEquiv η-iso


  ◯-lift-fam : ∀ {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) → ◯ A → Type◯ ℓ′
  ◯-lift-fam B [a] = η-at-modal.inv _ ◯-lex (◯-map (λ a → ◯ (B a) , idemp) [a])

  ⟨◯⟩ : ∀ {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) → ◯ A → Type ℓ′
  ⟨◯⟩ B [a] = ◯-lift-fam B [a] .fst

  ⟨◯⟩-modal : ∀ {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) → isModalFam (⟨◯⟩ B)
  ⟨◯⟩-modal B [a] = ◯-lift-fam B [a] .snd

  ⟨◯⟩-η : ∀ {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) (x : A) → ⟨◯⟩ B (η x) ≡ ◯ (B x)
  ⟨◯⟩-η B x =
    ⟨◯⟩ B (η x)
      ≡⟨ refl ⟩
    η-at-modal.inv _ ◯-lex (◯-map (λ a → ◯ (B a) , idemp) (η x)) .fst
      ≡[ i ]⟨ η-at-modal.inv _ ◯-lex (◯-map-β (λ a → ◯ (B a) , idemp) x i) .fst ⟩
    η-at-modal.inv _ ◯-lex (η (◯ (B x) , idemp)) .fst
      ≡[ i ]⟨ η-at-modal.is-section _ ◯-lex (◯ (B x) , idemp) i .fst ⟩
    ◯ (B x) ∎


  -- TODO
  module _ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where
    postulate
      Σ-modal : isModal A → isModalFam B → isModal (Σ A B)
      Π-modal : isModalFam B → isModal ((x : A) → B x)



  module _ {ℓ} {A B : Type ℓ} where
    rw_by_ : (x : A) → A ≡ B → B
    rw x by α = transport α x

    rw←_by_ : (x : A) → B ≡ A → B
    rw← x by α = transport (sym α) x

    rw-roundtrip : (x : A) (p : A ≡ B) → transport (sym p) (transport p x) ≡ x
    rw-roundtrip x p = transport⁻Transport p x

  abstract-along : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : A → Type ℓ′} (p : A ≡ B) → ((x : B) → C (rw← x by p)) → ((x : A) → C x)
  abstract-along {_} {_} {A} {B} {C} p f = rw f by λ i → (x : p (~ i)) → C (transp (λ j → p (~ i ∧ ~ j)) i x)

  un-funext : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} {f g : (x : A) → B x} → f ≡ g → ∀ x → f x ≡ g x
  un-funext ϕ x i = ϕ i x

  module Σ-commute {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where

    ◯Σ = ◯ (Σ A B)
    Σ◯ = Σ (◯ A) (⟨◯⟩ B)

    Σ◯-modal : isModal Σ◯
    Σ◯-modal = Σ-modal idemp (⟨◯⟩-modal _)

    push-sg-η : Σ A B → Σ◯
    push-sg-η (a , b) .fst = η a
    push-sg-η (a , b) .snd =
      rw← η b by
        ⟨◯⟩-η B a

    push-sg : ◯Σ → Σ◯
    push-sg = ◯-rec Σ◯-modal push-sg-η

    unpush-sg-split : (x : ◯ A) (y : ⟨◯⟩ B x) → ◯Σ
    unpush-sg-split =
      ◯-ind (λ _ → Π-modal (λ _ → idemp)) λ x →
      abstract-along {C = λ _ → ◯Σ} (⟨◯⟩-η B x)
      (◯-map λ y → x , y)

    unpush-sg-split-η/fst : (x : A) → unpush-sg-split (η x) ≡ abstract-along (⟨◯⟩-η B x) (◯-map (λ y → x , y))
    unpush-sg-split-η/fst = ◯-ind-β _ _

    unpush-sg : Σ◯ → ◯Σ
    unpush-sg (x , y) = unpush-sg-split x y

    unpush-sg-η-compute : ∀ p → unpush-sg (η (p .fst) , rw← η (p .snd) by ⟨◯⟩-η B (p .fst)) ≡ η p
    unpush-sg-η-compute (x , y) =
      unpush-sg (η x , rw← η y by ⟨◯⟩-η B x)
        ≡[ i ]⟨ unpush-sg-split-η/fst x i (rw← η y by ⟨◯⟩-η B x) ⟩
      rw ◯-map (λ z → x , z) (rw rw← η y by ⟨◯⟩-η B x by ⟨◯⟩-η B x) by (λ _ → ◯Σ)
        ≡⟨ transportRefl _ ⟩
      ◯-map (λ y₁ → x , y₁) (rw rw← η y by ⟨◯⟩-η B x by ⟨◯⟩-η B x)
        ≡⟨ cong (◯-map (λ z → x , z)) (rw-roundtrip _ (λ i → ⟨◯⟩-η B x (~ i))) ⟩
      ◯-map (λ y₁ → x , y₁) (η y)
        ≡⟨ ◯-map-β _ _ ⟩
      η (x , y) ∎


    is-retract-η : (x : A) (y : B x) → push-sg (unpush-sg (η x , rw← η y by ⟨◯⟩-η B x)) ≡ (η x , rw← η y by ⟨◯⟩-η B x)
    is-retract-η x y =
      push-sg (unpush-sg (η x , rw← η y by ⟨◯⟩-η B x))
        ≡⟨ cong push-sg (unpush-sg-η-compute _) ⟩
      push-sg (η (x , y))
        ≡⟨ ◯-ind-β (λ x₁ → Σ◯-modal) push-sg-η (x , y) ⟩
      push-sg-η (x , y) ∎

    is-section-η : (p : Σ A B) → unpush-sg (push-sg (η p)) ≡ η p
    is-section-η p =
      unpush-sg (push-sg (η p))
        ≡⟨ cong unpush-sg (◯-ind-β (λ _ → Σ◯-modal) push-sg-η p) ⟩
      unpush-sg (η (p .fst) , (rw← η (p .snd) by ⟨◯⟩-η B (p .fst)))
        ≡⟨ unpush-sg-η-compute p ⟩
      η p ∎

    is-section : section unpush-sg push-sg
    is-section = ◯-ind (λ _ → ≡-modal idemp) is-section-η

    is-retract-split : (x : ◯ A) (y : ⟨◯⟩ B x) → push-sg (unpush-sg (x , y)) ≡ (x , y)
    is-retract-split =
      ◯-ind (λ _ → Π-modal λ _ → ≡-modal Σ◯-modal) λ x →
      abstract-along (⟨◯⟩-η B x) (◯-ind (λ _ → ≡-modal Σ◯-modal) (is-retract-η x))

    is-retract : retract unpush-sg push-sg
    is-retract (x , y) = is-retract-split x y

    push-sg-is-equiv : isEquiv push-sg
    push-sg-is-equiv = isoToIsEquiv (iso push-sg unpush-sg is-retract is-section)
