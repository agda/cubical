
module Cubical.Induction.WellFounded where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

module _ {ℓ ℓ'} {A : Type ℓ} (_<_ : A → A → Type ℓ') where
  WFRec : ∀{ℓ''} → (A → Type ℓ'') → A → Type _
  WFRec P x = ∀ y → y < x → P y

  data Acc (x : A) : Type (ℓ-max ℓ ℓ') where
    acc : WFRec Acc x → Acc x

  WellFounded : Type _
  WellFounded = ∀ x → Acc x


module _ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'} where
  isPropAcc : ∀ x → isProp (Acc _<_ x)
  isPropAcc x (acc p) (acc q)
    = λ i → acc (λ y y<x → isPropAcc y (p y y<x) (q y y<x) i)

  isPropWellFounded : isProp (WellFounded _<_)
  isPropWellFounded p q i a = isPropAcc a (p a) (q a) i

  access : ∀{x} → Acc _<_ x → WFRec _<_ (Acc _<_) x
  access (acc r) = r

  private
    wfi : ∀{ℓ''} {P : A → Type ℓ''}
        → ∀ x → (wf : Acc _<_ x)
        → (∀ x → (∀ y → y < x → P y) → P x)
        → P x
    wfi x (acc p) e = e x λ y y<x → wfi y (p y y<x) e

  module WFI (wf : WellFounded _<_) where
    module _ {ℓ''} {P : A → Type ℓ''} (e : ∀ x → (∀ y → y < x → P y) → P x) where
      private
        wfi-compute : ∀ x ax → wfi x ax e ≡ e x (λ y _ → wfi y (wf y) e)
        wfi-compute x (acc p)
          = λ i → e x (λ y y<x → wfi y (isPropAcc y (p y y<x) (wf y) i) e)

      induction :  ∀ x → P x
      induction x = wfi x (wf x) e

      induction-compute : ∀ x → induction x ≡ (e x λ y _ → induction y)
      induction-compute x = wfi-compute x (wf x)

  wf→x≮x : WellFounded _<_ → ∀ {x} → ¬ (x < x)
  wf→x≮x wf {x} = aux x (wf x)
    where
      aux : ∀ x → Acc _<_ x → ¬ (x < x)
      aux x (acc r) x<x = aux x (r x x<x) x<x

  wf→x<y→x≢y : WellFounded _<_ → ∀ {x} {y} → x < y → ¬ (x ≡ y)
  wf→x<y→x≢y wf {x} x<y x≡y = wf→x≮x wf (subst (x <_) (sym x≡y) x<y)
