module Cubical.HITs.Colimit.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.SumFin

open import Cubical.Data.Graph
open import Cubical.HITs.Colimit.Base

open import Cubical.HITs.Pushout


-- Pushouts are colimits over the graph ⇐⇒

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where

  PushoutDiag : (A → B) → (A → C) → Diag (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) ⇐⇒
  (PushoutDiag f g) $g fzero             = Lift {j = ℓ-max ℓ  ℓ'' } B
  (PushoutDiag f g) $g fsuc fzero        = Lift {j = ℓ-max ℓ' ℓ'' } A
  (PushoutDiag f g) $g fsuc (fsuc fzero) = Lift {j = ℓ-max ℓ  ℓ'  } C
  _<$g>_ (PushoutDiag f g) {fsuc fzero} {fzero}             tt (lift a) = lift (f a)
  _<$g>_ (PushoutDiag f g) {fsuc fzero} {fsuc (fsuc fzero)} tt (lift a) = lift (g a)

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → B} {g : A → C} where

  PushoutCocone : Cocone _ (PushoutDiag f g) (Pushout f g)
  leg PushoutCocone fzero               (lift b) = inl b
  leg PushoutCocone (fsuc fzero)        (lift a) = inr (g a)
  leg PushoutCocone (fsuc (fsuc fzero)) (lift c) = inr c
  com PushoutCocone {fsuc fzero} {fzero}             tt i (lift a) = push a i
  com PushoutCocone {fsuc fzero} {fsuc (fsuc fzero)} tt i (lift a) = inr (g a)

  private
    module _ ℓq (Y : Type ℓq) where

      fwd : (Pushout f g → Y) → Cocone ℓq (PushoutDiag f g) Y
      fwd = postcomp PushoutCocone

      module _ (C : Cocone ℓq (PushoutDiag f g) Y) where
        coml : ∀ a → leg C fzero               (lift (f a)) ≡ leg C (fsuc fzero) (lift a)
        comr : ∀ a → leg C (fsuc (fsuc fzero)) (lift (g a)) ≡ leg C (fsuc fzero) (lift a)
        coml a i = com C {j = fsuc fzero} {k = fzero}             tt i (lift a)
        comr a i = com C {j = fsuc fzero} {k = fsuc (fsuc fzero)} tt i (lift a)

      bwd : Cocone ℓq (PushoutDiag f g) Y → (Pushout f g → Y)
      bwd C (inl b)    = leg C fzero (lift b)
      bwd C (inr c)    = leg C (fsuc (fsuc fzero)) (lift c)
      bwd C (push a i) = (coml C a ∙ sym (comr C a)) i

      bwd-fwd : ∀ F → bwd (fwd F) ≡ F
      bwd-fwd F i (inl b) = F (inl b)
      bwd-fwd F i (inr c) = F (inr c)
      bwd-fwd F i (push a j) = compPath-filler (coml (fwd F) a) (sym (comr (fwd F) a)) (~ i) j

      fwd-bwd : ∀ C → fwd (bwd C) ≡ C
      leg (fwd-bwd C i) fzero               (lift b) = leg C fzero (lift b)
      leg (fwd-bwd C i) (fsuc fzero)        (lift a) = comr C a i
      leg (fwd-bwd C i) (fsuc (fsuc fzero)) (lift c) = leg C (fsuc (fsuc fzero)) (lift c)
      com (fwd-bwd C i) {fsuc fzero} {fzero}             tt j (lift a) -- coml (fwd-bwd C i) = ...
        = compPath-filler (coml C a) (sym (comr C a)) (~ i) j
      com (fwd-bwd C i) {fsuc fzero} {fsuc (fsuc fzero)} tt j (lift a) -- comr (fwd-bwd C i) = ...
        = comr C a (i ∧ j)

      eqv : isEquiv {A = (Pushout f g → Y)} {B = Cocone ℓq (PushoutDiag f g) Y} (postcomp PushoutCocone)
      eqv = isoToIsEquiv (iso fwd bwd fwd-bwd bwd-fwd)

  isColimPushout : isColimit (PushoutDiag f g) (Pushout f g)
  cone isColimPushout = PushoutCocone
  univ isColimPushout = eqv

  colim≃Pushout : colim (PushoutDiag f g) ≃ Pushout f g
  colim≃Pushout = uniqColimit colimIsColimit isColimPushout
