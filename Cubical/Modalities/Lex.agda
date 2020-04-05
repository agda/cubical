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


  module ModalUnit {ℓ} (A : Type ℓ) (A-mod : isModal A) where
    inv : ◯ A → A
    inv = ◯-rec A-mod λ x → x

    η-retract : retract η inv
    η-retract = ◯-rec-β _ _

    η-section : section η inv
    η-section = ◯-ind (λ _ → ≡-modal idemp) λ x i → η (η-retract x i)

    η-iso : Iso A (◯ A)
    Iso.fun η-iso = η
    Iso.inv η-iso = inv
    Iso.rightInv η-iso = η-section
    Iso.leftInv η-iso = η-retract

    η-is-equiv : isEquiv (η-at A)
    η-is-equiv = isoToIsEquiv η-iso

  module LiftFam {ℓ ℓ′} {A : Type ℓ} (B : A → Type ℓ′) where
    module M = ModalUnit (Type◯ ℓ′) ◯-lex

    ◯-lift-fam : ◯ A → Type◯ ℓ′
    ◯-lift-fam = M.inv ∘ ◯-map (λ a → ◯ (B a) , idemp)

    ⟨◯⟩ : ◯ A → Type ℓ′
    ⟨◯⟩ [a] = ◯-lift-fam [a] .fst

    ⟨◯⟩-modal : isModalFam ⟨◯⟩
    ⟨◯⟩-modal [a] = ◯-lift-fam [a] .snd

    ⟨◯⟩-compute : (x : A) → ⟨◯⟩ (η x) ≡ ◯ (B x)
    ⟨◯⟩-compute x =
      ⟨◯⟩ (η x)
        ≡[ i ]⟨ M.inv (◯-map-β (λ a → ◯ (B a) , idemp) x i) .fst ⟩
      M.inv (η (◯ (B x) , idemp)) .fst
        ≡[ i ]⟨ M.η-retract (◯ (B x) , idemp) i .fst ⟩
      ◯ (B x) ∎

  open LiftFam using (⟨◯⟩; ⟨◯⟩-modal; ⟨◯⟩-compute)



  -- TODO
  module _ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where
    postulate
      Σ-modal : isModal A → isModalFam B → isModal (Σ A B)
      Π-modal : isModalFam B → isModal ((x : A) → B x)

  abstract-along : ∀ {ℓ ℓ′} {A B : Type ℓ} {C : A → Type ℓ′} (p : A ≡ B) → ((x : B) → C (transport (sym p) x)) → ((x : A) → C x)
  abstract-along {C = C} p f = transport (λ i → (x : p (~ i)) → C (transp (λ j → p (~ i ∧ ~ j)) i x)) f

  module Σ-commute {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where

    ◯Σ = ◯ (Σ A B)
    Σ◯ = Σ (◯ A) (⟨◯⟩ B)

    Σ◯-modal : isModal Σ◯
    Σ◯-modal = Σ-modal idemp (⟨◯⟩-modal _)

    push-sg-η : Σ A B → Σ◯
    push-sg-η (a , b) .fst = η a
    push-sg-η (a , b) .snd = transport (sym (⟨◯⟩-compute B a)) (η b)

    push-sg : ◯Σ → Σ◯
    push-sg = ◯-rec Σ◯-modal push-sg-η

    unpush-sg-split : (x : ◯ A) (y : ⟨◯⟩ B x) → ◯Σ
    unpush-sg-split =
      ◯-ind (λ _ → Π-modal λ _ → idemp) λ x →
      abstract-along {C = λ _ → ◯Σ} (⟨◯⟩-compute B x)
      (◯-map (x ,_))


    unpush-sg : Σ◯ → ◯Σ
    unpush-sg (x , y) = unpush-sg-split x y

    unpush-sg-compute : ∀ x y → unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y)) ≡ η (x , y)
    unpush-sg-compute x y =
      unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y))
        ≡[ i ]⟨ unpush-sg-split-compute x i (transport (sym (⟨◯⟩-compute B x)) (η y)) ⟩
      transport refl (◯-map _ (transport (⟨◯⟩-compute B x) (transport (sym (⟨◯⟩-compute B x)) (η y))))
        ≡⟨ transportRefl _ ⟩
      ◯-map _ (transport (⟨◯⟩-compute B x) (transport (sym (⟨◯⟩-compute B x)) (η y)))
        ≡⟨ cong (◯-map _) (transport⁻Transport (sym (⟨◯⟩-compute B x)) _) ⟩
      ◯-map _ (η y)
        ≡⟨ ◯-map-β _ _ ⟩
      η (x , y) ∎

      where
        unpush-sg-split-compute : (x : A) → unpush-sg-split (η x) ≡ abstract-along (⟨◯⟩-compute B x) (◯-map (x ,_))
        unpush-sg-split-compute = ◯-ind-β _ _



    push-unpush-compute : (x : A) (y : B x) → push-sg (unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y))) ≡ (η x , transport (sym (⟨◯⟩-compute B x)) (η y))
    push-unpush-compute x y =
      push-sg (unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y)))
        ≡⟨ cong push-sg (unpush-sg-compute _ _) ⟩
      push-sg (η (x , y))
        ≡⟨ ◯-ind-β (λ _ → Σ◯-modal) push-sg-η (x , y) ⟩
      push-sg-η (x , y) ∎

    unpush-push-compute : (p : Σ A B) → unpush-sg (push-sg (η p)) ≡ η p
    unpush-push-compute p =
      unpush-sg (push-sg (η p))
        ≡⟨ cong unpush-sg (◯-ind-β (λ _ → Σ◯-modal) push-sg-η p) ⟩
      unpush-sg (η (p .fst) , transport (sym (⟨◯⟩-compute B (p .fst))) (η (p .snd)))
        ≡⟨ unpush-sg-compute _ _ ⟩
      η p ∎

    is-section : section unpush-sg push-sg
    is-section = ◯-ind (λ _ → ≡-modal idemp) unpush-push-compute

    is-retract : retract unpush-sg push-sg
    is-retract (x , y) = is-retract-split x y
      where
        is-retract-split : (x : ◯ A) (y : ⟨◯⟩ B x) → push-sg (unpush-sg (x , y)) ≡ (x , y)
        is-retract-split =
          ◯-ind (λ _ → Π-modal λ _ → ≡-modal Σ◯-modal) λ x →
          abstract-along (⟨◯⟩-compute B x) λ y →
          ◯-ind (λ _ → ≡-modal Σ◯-modal) (push-unpush-compute x) y

    push-sg-is-equiv : isEquiv push-sg
    push-sg-is-equiv = isoToIsEquiv (iso push-sg unpush-sg is-retract is-section)
