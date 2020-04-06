{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

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

module _ where
  private
    variable
      A : Type ℓ
      B : Type ℓ′


  module _ (B-mod : isModal B) (f : A → B) where
    abstract
      ◯-rec : ◯ A → B
      ◯-rec = ◯-ind (λ _ → B-mod) f

      ◯-rec-β : (x : A) → ◯-rec (η x) ≡ f x
      ◯-rec-β = ◯-ind-β (λ _ → B-mod) f

  module _ (f : A → B) where
    abstract
      ◯-map : ◯ A → ◯ B
      ◯-map = ◯-rec idemp λ x → η (f x)

      ◯-map-β : (x : A) → ◯-map (η x) ≡ η (f x)
      ◯-map-β x = ◯-rec-β idemp _ x



module IsModalToUnitIsEquiv (A : Type ℓ) (A-mod : isModal A) where
  abstract
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

abstract
  unit-is-equiv-to-is-modal : {A : Type ℓ} → isEquiv (η-at A) → isModal A
  unit-is-equiv-to-is-modal p = transport (cong isModal (sym (ua (η , p)))) idemp

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
        ≡⟨ cong (fst ∘ M.inv) (◯-map-β _ _) ⟩
      M.inv (η (◯ (B x) , idemp)) .fst
        ≡⟨ cong fst (M.η-retract _) ⟩
      ◯ (B x) ∎



open LiftFam using (⟨◯⟩; ⟨◯⟩-modal; ⟨◯⟩-compute)

module _ {A : Type ℓ} {B : A → Type ℓ′} where
  ⟨◯⟩←◯ : ∀ {a} → ◯ (B a) → ⟨◯⟩ B (η a)
  ⟨◯⟩←◯ = transport (sym (⟨◯⟩-compute B _))

  ⟨η⟩ : ∀ {a} → B a → ⟨◯⟩ B (η a)
  ⟨η⟩ = ⟨◯⟩←◯ ∘ η

  ⟨◯⟩→◯ : ∀ {a} → ⟨◯⟩ B (η a) → ◯ (B a)
  ⟨◯⟩→◯ = transport (⟨◯⟩-compute B _)


abstract-along : {A B : Type ℓ} {C : A → Type ℓ′} (p : A ≡ B) → ((x : B) → C (coe1→0 (λ i → p i) x)) → ((x : A) → C x)
abstract-along {C = C} p f = coe1→0 (λ i → (x : p i) → C (coei→0 (λ j → p j) i x)) f

cong-fun : {A : Type ℓ} {B : A → Type ℓ′} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
cong-fun α x i = α i x

pair-ext : {A : Type ℓ} {B : A → Type ℓ′} {p q : Σ A B} (α : p .fst ≡ q .fst) (β : PathP (λ i → B (α i)) (p .snd) (q .snd)) → p ≡ q
pair-ext α β i = α i , β i

module _ {A : Type ℓ} {B : A → Type ℓ′} where
  abstract
    Π-modal : isModalFam B → isModal ((x : A) → B x)
    Π-modal B-mod = retract-is-modal idemp η-inv η retr
      where
        η-inv : ◯ ((x : A) → B x) → (x : A) → B x
        η-inv [f] x = ◯-rec (B-mod x) (λ f → f x) [f]

        retr : retract η η-inv
        retr f = funExt λ x → ◯-rec-β (B-mod x) _ f

    Σ-modal : isModal A → isModalFam B → isModal (Σ A B)
    Σ-modal A-mod B-mod = retract-is-modal idemp η-inv η retr
      where
        h : ◯ (Σ A B) → A
        h = ◯-rec A-mod fst

        h-β : (x : Σ A B) → h (η x) ≡ fst x
        h-β = ◯-rec-β A-mod fst

        f : (i : I) (x : Σ A B) → B (h-β x i)
        f i x = coe1→i (λ j → B (h-β x j)) i (snd x)

        η-inv : ◯ (Σ A B) → Σ A B
        η-inv y = h y , ◯-ind (B-mod ∘ h) (f i0) y

        retr : (p : Σ A B) → η-inv (η p) ≡ p
        retr p =
          η-inv (η p)
            ≡⟨ pair-ext refl (◯-ind-β _ _ _) ⟩
          h (η p) , f i0 p
            ≡⟨ pair-ext (h-β _) (λ i → f i p) ⟩
          p ∎


data test : Set where
  t0 t1 : test

module Σ-commute {A : Type ℓ} (B : A → Type ℓ′) where
  ◯Σ = ◯ (Σ A B)

  module Σ◯ where
    Σ◯ = Σ (◯ A) (⟨◯⟩ B)
    abstract
      Σ◯-modal : isModal Σ◯
      Σ◯-modal = Σ-modal idemp (⟨◯⟩-modal _)

  open Σ◯

  η-Σ◯ : Σ A B → Σ◯
  η-Σ◯ (x , y) = η x , ⟨η⟩ y

  module Push where
    abstract
      fun : ◯Σ → Σ◯
      fun = ◯-rec Σ◯-modal η-Σ◯

      compute : fun ∘ η ≡ η-Σ◯
      compute = funExt (◯-ind-β _ _)

  module Unpush where
    body : (x : A) (y : B x) → ◯Σ
    body x y = η (x , y)

    abstract
      fun/split : (x : ◯ A) (y : ⟨◯⟩ B x) → ◯Σ
      fun/split =
        ◯-ind (λ _ → Π-modal λ _ → idemp) λ x →
        abstract-along (⟨◯⟩-compute B x)
        (◯-map (x ,_))

      fun : Σ◯ → ◯Σ
      fun (x , y) = fun/split x y

      compute : fun ∘ η-Σ◯ ≡ η
      compute =
        funExt λ p →
        fun (η-Σ◯ p)
          ≡⟨ cong-fun (◯-ind-β _ _ _) _ ⟩
        transport refl (◯-map _ _)
          ≡⟨ transportRefl _ ⟩
        ◯-map _ (⟨◯⟩→◯ (⟨η⟩ _))
          ≡⟨ cong (◯-map _) (transport⁻Transport (sym (⟨◯⟩-compute B _)) _) ⟩
        ◯-map _ (η _)
          ≡⟨ ◯-map-β _ _ ⟩
        η p ∎


  push-unpush-compute : Push.fun ∘ Unpush.fun ∘ η-Σ◯ ≡ η-Σ◯
  push-unpush-compute =
    Push.fun ∘ Unpush.fun ∘ η-Σ◯
      ≡⟨ cong (Push.fun ∘_) Unpush.compute ⟩
    Push.fun ∘ η
      ≡⟨ Push.compute ⟩
    η-Σ◯ ∎

  unpush-push-compute : Unpush.fun ∘ Push.fun ∘ η ≡ η
  unpush-push-compute =
    Unpush.fun ∘ Push.fun ∘ η
      ≡⟨ cong (Unpush.fun ∘_) Push.compute ⟩
    Unpush.fun ∘ η-Σ◯
      ≡⟨ Unpush.compute ⟩
    η ∎

  is-section : section Unpush.fun Push.fun
  is-section = ◯-ind (λ x → ≡-modal idemp) λ x i → unpush-push-compute i x

  is-retract : retract Unpush.fun Push.fun
  is-retract (x , y) = is-retract-split x y
    where
      is-retract-split : (x : ◯ A) (y : ⟨◯⟩ B x) → Push.fun (Unpush.fun (x , y)) ≡ (x , y)
      is-retract-split =
        ◯-ind (λ _ → Π-modal λ _ → ≡-modal Σ◯-modal) λ x →
        abstract-along
          (⟨◯⟩-compute B x)
          (◯-ind
           (λ _ → ≡-modal Σ◯-modal)
           λ y i → push-unpush-compute i (x , y))

  push-sg-is-equiv : isEquiv Push.fun
  push-sg-is-equiv = isoToIsEquiv (iso Push.fun Unpush.fun is-retract is-section)


module FormalDiskBundle {A : Type ℓ} where
  𝔻 : A → Type ℓ
  𝔻 a = Σ A (λ x → η a ≡ η x)
