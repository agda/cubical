{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid.Base

private
  variable
    ℓ ℓ' : Level

module _
    (M : CommMonoid ℓ)
    (P : ⟨ M ⟩ → hProp ℓ')
    where
  open CommMonoidStr (snd M)
  module _
    (·Closed : (x y : ⟨ M ⟩) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x · y) ⟩)
    (εContained : ⟨ P ε ⟩)
    where
    private
      subtype = Σ[ x ∈ ⟨ M ⟩ ] ⟨ P x ⟩

    makeSubCommMonoid : CommMonoid _
    fst makeSubCommMonoid = subtype
    CommMonoidStr.ε (snd makeSubCommMonoid) = ε , εContained
    CommMonoidStr._·_ (snd makeSubCommMonoid) (x , xContained) (y , yContained) =
      (x · y) , ·Closed x y xContained yContained
    IsCommMonoid.isMonoid (CommMonoidStr.isCommMonoid (snd makeSubCommMonoid)) =
      makeIsMonoid
        (isOfHLevelΣ 2 (isSetFromIsCommMonoid isCommMonoid) λ _ → isProp→isSet (snd (P _)))
        (λ x y z → Σ≡Prop (λ _ → snd (P _)) (assoc (fst x) (fst y) (fst z)))
        (λ x → Σ≡Prop (λ _ → snd (P _)) (rid (fst x)))
        λ x → Σ≡Prop (λ _ → snd (P _)) (lid (fst x))
    IsCommMonoid.comm (CommMonoidStr.isCommMonoid (snd makeSubCommMonoid)) =
      λ x y → Σ≡Prop (λ _ → snd (P _)) (comm (fst x) (fst y))

module CommMonoidTheory (M' : CommMonoid ℓ) where
 open CommMonoidStr (snd M')
 private M = ⟨ M' ⟩

 commAssocl : (x y z : M) → x · (y · z) ≡ y · (x · z)
 commAssocl x y z = assoc x y z ∙∙ cong (_· z) (comm x y) ∙∙ sym (assoc y x z)

 commAssocr : (x y z : M) → x · y · z ≡ x · z · y
 commAssocr x y z = sym (assoc x y z) ∙∙ cong (x ·_) (comm y z) ∙∙ assoc x z y


 commAssocr2 : (x y z : M) → x · y · z ≡ z · y · x
 commAssocr2 x y z = commAssocr _ _ _ ∙∙ cong (_· y) (comm _ _) ∙∙ commAssocr _ _ _

 commAssocSwap : (x y z w : M) → (x · y) · (z · w) ≡ (x · z) · (y · w)
 commAssocSwap x y z w = assoc (x · y) z w ∙∙ cong (_· w) (commAssocr x y z)
                                               ∙∙ sym (assoc (x · z) y w)
