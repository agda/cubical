{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (idfun; _∘_)

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

module _ {R : Ring ℓ'} (M : LeftModule R ℓ) where
  idLeftModuleHom : LeftModuleHom M M
  idLeftModuleHom = (idfun ⟨ M ⟩) , isLeftModuleHom where
    open IsLeftModuleHom
    isLeftModuleHom : IsLeftModuleHom (M .snd) (idfun ⟨ M ⟩) (M .snd)
    isLeftModuleHom .pres0 = refl
    isLeftModuleHom .pres+ x y = refl
    isLeftModuleHom .pres- x = refl
    isLeftModuleHom .pres⋆ r y = refl

module _ {R : Ring ℓ'} {M N P : LeftModule R ℓ} where
  -- Composition of left module homomorphisms
  compLeftModuleHom : LeftModuleHom M N → LeftModuleHom N P → LeftModuleHom M P
  compLeftModuleHom f g =
    fg , record { pres0 = pres0 ; pres+ = pres+ ; pres- = pres- ; pres⋆ = pres⋆ } where
      open LeftModuleStr (M .snd) using () renaming (0m to 0M; _+_ to _+M_; -_ to -M_; _⋆_ to _⋆M_)
      open LeftModuleStr (N .snd) using () renaming (0m to 0N; _+_ to _+N_; -_ to -N_; _⋆_ to _⋆N_)
      open LeftModuleStr (P .snd) using () renaming (0m to 0P; _+_ to _+P_; -_ to -P_; _⋆_ to _⋆P_)

      fg = g .fst ∘ f .fst

      pres0 : fg 0M ≡ 0P
      pres0 = cong (g .fst) (f .snd .IsLeftModuleHom.pres0) ∙ g .snd .IsLeftModuleHom.pres0

      pres+ : (x y : M .fst) → fg (x +M y) ≡ fg x +P fg y
      -- g(f(x+y)) ≡ g(f(x)+f(y)) ≡ g(f(x))+g(f(y))
      pres+ x y =
        let p = refl {x = g .fst (f .fst (x +M y))} in
        let p = p ∙ cong (g .fst) (f .snd .IsLeftModuleHom.pres+ x y) in
        let p = p ∙ g .snd .IsLeftModuleHom.pres+ (f .fst x) (f .fst y) in
        p

      pres- : (x : M .fst) → fg (-M x) ≡ -P (fg x)
      -- g(f(-x)) ≡ g(-f(x)) ≡ -g(f(x))
      pres- x =
        let p = refl {x = g .fst (f .fst (-M x))} in
        let p = p ∙ cong (g .fst) (f .snd .IsLeftModuleHom.pres- x) in
        let p = p ∙ g .snd .IsLeftModuleHom.pres- (f .fst x) in
        p

      pres⋆ : (r : ⟨ R ⟩) (y : M .fst) → fg (r ⋆M y) ≡ r ⋆P fg y
      -- g(f(r⋆y)) ≡ g(r⋆f(y)) ≡ r⋆g(f(y))
      pres⋆ r y =
        let p = refl {x = g .fst (f .fst (r ⋆M y))} in
        let p = p ∙ cong (g .fst) (f .snd .IsLeftModuleHom.pres⋆ r y) in
        let p = p ∙ g .snd .IsLeftModuleHom.pres⋆ r (f .fst y) in
        p
