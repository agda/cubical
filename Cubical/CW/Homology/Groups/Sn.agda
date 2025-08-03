{-# OPTIONS --lossy-unification #-}
module Cubical.CW.Homology.Groups.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Int
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.CW.ChainComplex
open import Cubical.CW.Instances.Sn

open Iso

module _ (n : ℕ) where
  ScardDiag : isContr (Fin (Scard (suc n) (suc n)))
  ScardDiag with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = inhProp→isContr fzero isPropFin1
  ... | gt x = ⊥.rec (¬m<ᵗm x)

  HₙSⁿ→ℤ-fun : (a : Fin (Scard (suc n) (suc n)) → ℤ) → ℤ
  HₙSⁿ→ℤ-fun a = a (ScardDiag .fst)

  HₙSⁿ→ℤ-coh :
       (a b : Fin (Scard (suc n) (suc n)) → ℤ)
    → (aker : ∂ (Sˢᵏᵉˡ (suc n)) n .fst a ≡ λ _ → 0)
    → (bker : ∂ (Sˢᵏᵉˡ (suc n)) n .fst b ≡ λ _ → 0)
    → (r : Σ[ t ∈ (Fin (Scard (suc n) (suc (suc n))) → ℤ) ]
             ∂ (Sˢᵏᵉˡ (suc n)) (suc n) .fst t ≡ λ q → a q - b q)
    → HₙSⁿ→ℤ-fun a ≡ HₙSⁿ→ℤ-fun b
  HₙSⁿ→ℤ-coh a b aker bker r with (n ≟ᵗ n) | (suc n ≟ᵗ n)
  ... | lt x | t = ⊥.rec (¬m<ᵗm x)
  ... | eq x | lt x₁ = ⊥.rec (¬-suc-n<ᵗn x₁)
  ... | eq x | eq x₁ = ⊥.rec (sucn≠n x₁)
  ... | eq x | gt x₁ = sym (+Comm (b fzero) 0
                     ∙ cong (_+ b fzero) (funExt⁻ (snd r) fzero)
                     ∙ sym (+Assoc (a fzero) (- b fzero) (b fzero))
                     ∙ cong (a fzero +_) (-Cancel' (b fzero)))
  ... | gt x | t = ⊥.rec (¬m<ᵗm x)

  HₙSⁿ→ℤ : H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n) . fst → ℤ
  HₙSⁿ→ℤ = SQ.elim (λ _ → isSetℤ) (λ a → HₙSⁿ→ℤ-fun (fst a))
    λ a b → PT.elim (λ _ → isSetℤ _ _)
      λ x →  HₙSⁿ→ℤ-coh (fst a) (fst b) (snd a) (snd b) (fst x , cong fst (snd x))

  ∂VanishS : (n : ℕ) (t : _) → ∂ (Sˢᵏᵉˡ (suc n)) n .fst t ≡ λ _ → pos 0
  ∂VanishS zero t = funExt λ { (zero , p) → ·Comm (t fzero) (pos 0)}
  ∂VanishS (suc n) t = funExt λ y → ⊥.rec (¬Scard' n y)

  ℤ→HₙSⁿ-fun : ℤ → H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n) . fst
  ℤ→HₙSⁿ-fun z = [ (λ _ → z) , ∂VanishS n (λ _ → z) ]

  ℤ→HₙSⁿ : GroupHom ℤGroup (H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n))
  fst (ℤ→HₙSⁿ) = ℤ→HₙSⁿ-fun
  snd (ℤ→HₙSⁿ) = makeIsGroupHom λ x y
    → cong [_] (Σ≡Prop (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
                refl)

  HₙSⁿ→ℤ→HₙSⁿ : (x : _) → ℤ→HₙSⁿ-fun (HₙSⁿ→ℤ x) ≡ x
  HₙSⁿ→ℤ→HₙSⁿ =
    SQ.elimProp (λ _ → GroupStr.is-set (snd (H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n))) _ _)
        λ {(a , p) → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
                               (funExt λ t → cong a (ScardDiag .snd t)))}

  ℤ≅HₙSⁿ : GroupIso ℤGroup (H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n))
  fun (fst ℤ≅HₙSⁿ) = ℤ→HₙSⁿ .fst
  inv (fst ℤ≅HₙSⁿ) = HₙSⁿ→ℤ
  rightInv (fst ℤ≅HₙSⁿ) = HₙSⁿ→ℤ→HₙSⁿ
  leftInv (fst ℤ≅HₙSⁿ) _ = refl
  snd ℤ≅HₙSⁿ = ℤ→HₙSⁿ .snd

  HₙSⁿ≅ℤ : GroupIso (H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n)) ℤGroup
  HₙSⁿ≅ℤ = invGroupIso ℤ≅HₙSⁿ

  genHₙSⁿ : H̃ˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) (suc n) .fst
  genHₙSⁿ = [ (λ _ → 1) , (∂VanishS n (λ _ → 1)) ]
