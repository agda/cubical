{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Module.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group

private variable
  ℓ ℓ' : Level

module ModuleTheory (R : Ring ℓ') (M : LeftModule R ℓ) where
  open LeftModuleStr ⦃...⦄
  private
    module R = RingStr (snd R)
  private instance
    _ = snd M

  ⋆AnnihilL : (x : ⟨ M ⟩) → R.0r ⋆ x ≡ 0m
  ⋆AnnihilL x =
    let idempotent-+ = R.0r ⋆ x                ≡⟨ congL _⋆_ (sym (RingTheory.0Idempotent R)) ⟩
                       (R.0r R.+ R.0r) ⋆ x     ≡⟨ ⋆DistL+ R.0r R.0r x ⟩
                       (R.0r ⋆ x) + (R.0r ⋆ x) ∎
    in GroupTheory.idFromIdempotency (LeftModule→Group M) (R.0r ⋆ x) idempotent-+

  ⋆AnnihilR : (r : ⟨ R ⟩) → r ⋆ 0m ≡ 0m
  ⋆AnnihilR r = GroupTheory.idFromIdempotency (LeftModule→Group M) (r ⋆ 0m) helper
    where helper =
             r ⋆ 0m              ≡⟨ congR _⋆_ (sym (+IdL (0m))) ⟩
             r ⋆ (0m + 0m)       ≡⟨ ⋆DistR+ r 0m 0m ⟩
             (r ⋆ 0m) + (r ⋆ 0m) ∎


  minusByMult : (x : ⟨ M ⟩) → (R.- R.1r) ⋆ x ≡ - x
  minusByMult x =
    let open AbGroupTheory (LeftModule→AbGroup M)
    in implicitInverse
      (        x + (R.- R.1r) ⋆ x  ≡⟨ congL _+_ (sym (⋆IdL x)) ⟩
        R.1r ⋆ x + (R.- R.1r) ⋆ x  ≡⟨ sym (⋆DistL+ R.1r (R.- R.1r) x) ⟩
       (R.1r R.+ (R.- R.1r))  ⋆ x  ≡⟨ congL _⋆_ (R.+InvR R.1r) ⟩
       R.0r                   ⋆ x  ≡⟨ ⋆AnnihilL x ⟩
       0m ∎)
