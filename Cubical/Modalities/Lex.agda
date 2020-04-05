{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Cubical.Foundations.Everything

module Cubical.Modalities.Lex
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


private
  variable
     ℓ ℓ′ : Level

η-at : (A : Type ℓ) → A → ◯ A
η-at _ = η

module _ {A : Type ℓ} {B : Type ℓ′} (B-mod : isModal B) (f : A → B) where
  ◯-rec : ◯ A → B
  ◯-rec = ◯-ind (λ _ → B-mod) f

  ◯-rec-β : (x : A) → ◯-rec (η x) ≡ f x
  ◯-rec-β = ◯-ind-β (λ _ → B-mod) f

module _ {A : Type ℓ} {B : Type ℓ′} (f : A → B) where
  ◯-map : ◯ A → ◯ B
  ◯-map = ◯-rec idemp λ x → η (f x)

  ◯-map-β : (x : A) → ◯-map (η x) ≡ η (f x)
  ◯-map-β x = ◯-rec-β idemp _ x


module IsModalToUnitIsEquiv (A : Type ℓ) (A-mod : isModal A) where
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

unit-is-equiv-to-is-modal : {A : Type ℓ} → isEquiv (η-at A) → isModal A
unit-is-equiv-to-is-modal p = transport (cong isModal (sym (ua (η , p)))) idemp

abstract
  retract-is-modal
    : {A : Type ℓ} {B : Type ℓ′}
    → (A-mod : isModal A) (f : A → B) (g : B → A) (r : retract g f)
    → isModal B
  retract-is-modal {A = A} {B = B} A-mod f g r =
    unit-is-equiv-to-is-modal (isoToIsEquiv (iso η η-inv η-section η-retract))
    where
      η-inv : ◯ B → B
      η-inv = f ∘ ◯-rec A-mod g

      η-retract : retract η η-inv
      η-retract b = cong f (◯-rec-β A-mod g b) ∙ r b

      η-section : section η η-inv
      η-section = ◯-ind (λ _ → ≡-modal idemp) (cong η ∘ η-retract)


module LiftFam {A : Type ℓ} (B : A → Type ℓ′) where
  module M = IsModalToUnitIsEquiv (Type◯ ℓ′) ◯-lex

  abstract
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

module _ {A : Type ℓ} {B : A → Type ℓ′} where
  abstract
    Π-modal : isModalFam B → isModal ((x : A) → B x)
    Π-modal B-mod = retract-is-modal idemp η-inv η retr
      where
        η-inv : ◯ ((x : A) → B x) → (x : A) → B x
        η-inv [f] x = ◯-rec (B-mod x) (λ f → f x) [f]

        retr : retract η η-inv
        retr f = funExt (λ x → ◯-rec-β (B-mod x) _ f)

    Σ-modal : isModal A → isModalFam B → isModal (Σ A B)
    Σ-modal A-mod B-mod = retract-is-modal idemp η-inv η retr
      where
        h : ◯ (Σ A B) → A
        h = ◯-rec A-mod fst

        h-β : (x : Σ A B) → h (η x) ≡ fst x
        h-β = ◯-rec-β A-mod fst

        f : (j : I) → (x : Σ A B) → B (h-β x j)
        f j x = transp (λ i → B (h-β x ((~ i) ∨ j))) j (snd x)

        k : (y : ◯ (Σ A B)) → B (h y)
        k = ◯-ind (B-mod ∘ h) (f i0)

        η-inv : ◯ (Σ A B) → Σ A B
        η-inv y = h y , k y

        p : (x : Σ A B) → k (η x) ≡ f i0 x
        p = ◯-ind-β (B-mod ∘ h) (f i0)

        almost : (x : Σ A B) → (h (η x) , f i0 x) ≡ x
        almost x i = h-β x i , f i x

        retr : (x : Σ A B) → η-inv (η x) ≡ x
        retr x = (λ i → h (η x) , p x i) ∙ (almost x)


abstract-along : {A B : Type ℓ} {C : A → Type ℓ′} (p : A ≡ B) → ((x : B) → C (transport (sym p) x)) → ((x : A) → C x)
abstract-along {C = C} p f = transport (λ i → (x : p (~ i)) → C (transp (λ j → p (~ i ∧ ~ j)) i x)) f

cong-fun : {A : Type ℓ} {B : A → Type ℓ′} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
cong-fun α x i = α i x

module Σ-commute {A : Type ℓ} (B : A → Type ℓ′) where

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
    abstract-along (⟨◯⟩-compute B x)
    (◯-map (x ,_))


  unpush-sg : Σ◯ → ◯Σ
  unpush-sg (x , y) = unpush-sg-split x y


  unpush-sg-compute : ∀ x y → unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y)) ≡ η (x , y)
  unpush-sg-compute x y =
    unpush-sg (η x , transport (sym (⟨◯⟩-compute B x)) (η y))
      ≡⟨ cong-fun (◯-ind-β _ _ _) _ ⟩
    transport refl (◯-map (x ,_) (transport (⟨◯⟩-compute B x) (transport (sym (⟨◯⟩-compute B x)) (η y))))
      ≡⟨ transportRefl _ ⟩
    ◯-map _ (transport (⟨◯⟩-compute B x) (transport (sym (⟨◯⟩-compute B x)) (η y)))
      ≡⟨ cong (◯-map _) (transport⁻Transport (sym (⟨◯⟩-compute B x)) _) ⟩
    ◯-map _ (η y)
      ≡⟨ ◯-map-β _ _ ⟩
    η (x , y) ∎

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


module FormalDiskBundle {A : Type ℓ} where
  𝔻 : A → Type ℓ
  𝔻 a = Σ A (λ x → η a ≡ η x)
