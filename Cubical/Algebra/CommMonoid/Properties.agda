module Cubical.Algebra.CommMonoid.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

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
        (isOfHLevelΣ 2 is-set λ _ → isProp→isSet (snd (P _)))
        (λ x y z → Σ≡Prop (λ _ → snd (P _)) (·Assoc (fst x) (fst y) (fst z)))
        (λ x → Σ≡Prop (λ _ → snd (P _)) (·IdR (fst x)))
        λ x → Σ≡Prop (λ _ → snd (P _)) (·IdL (fst x))
    IsCommMonoid.·Comm (CommMonoidStr.isCommMonoid (snd makeSubCommMonoid)) =
      λ x y → Σ≡Prop (λ _ → snd (P _)) (·Comm (fst x) (fst y))

module CommMonoidTheory (M' : CommMonoid ℓ) where
 open CommMonoidStr (snd M')
 private M = ⟨ M' ⟩

 commAssocl : (x y z : M) → x · (y · z) ≡ y · (x · z)
 commAssocl x y z = ·Assoc x y z ∙∙ cong (_· z) (·Comm x y) ∙∙ sym (·Assoc y x z)

 commAssocr : (x y z : M) → x · y · z ≡ x · z · y
 commAssocr x y z = sym (·Assoc x y z) ∙∙ cong (x ·_) (·Comm y z) ∙∙ ·Assoc x z y


 commAssocr2 : (x y z : M) → x · y · z ≡ z · y · x
 commAssocr2 x y z = commAssocr _ _ _ ∙∙ cong (_· y) (·Comm _ _) ∙∙ commAssocr _ _ _

 commAssocSwap : (x y z w : M) → (x · y) · (z · w) ≡ (x · z) · (y · w)
 commAssocSwap x y z w = ·Assoc (x · y) z w ∙∙ cong (_· w) (commAssocr x y z)
                                               ∙∙ sym (·Assoc (x · z) y w)

 rotate : ∀ a b c → a · b · c ≡ b · c · a
 rotate a b c = cong (λ u → u · c) (·Comm a b) ∙ commAssocr b a c

 rotate' : ∀ a b c → a · b · c ≡ c · a · b
 rotate' a b c = commAssocr a b c ∙ cong (λ u → u · b) (·Comm a c)

 interchange   : ∀ a b c d -> (a · b) · (c · d) ≡ (a · c) · (b · d)
 interchange   a b c d = sym (·Assoc a b (c · d)) ∙
   cong (a ·_) (commAssocl b c d) ∙ ·Assoc a c (b · d)

 commAssocCross : ∀ a b c d -> (a · b) · (c · d) ≡ (c · a) · (d · b)
 commAssocCross a b c d =
   interchange a b c d ∙ cong₂ (λ u v → u · v) (·Comm a c) (·Comm b d)

 interchange-assoc : ∀ a b c d → a · b · c · d ≡ (a · c) · (b · d)
 interchange-assoc a b c d =
   sym (·Assoc (a · b) c d) ∙ (interchange a b c d)

 assoc₄ : ∀ a b c d -> a · (b · c) · d ≡ (a · b) · (c · d)
 assoc₄ a b c d =
   cong (λ u → u · d) (·Assoc a b c) ∙ sym (·Assoc (a · b) c d)

 interchangeComm' : ∀ a b c d -> (a · b) · (c · d) ≡ (c · b) · (d · a)
 interchangeComm' a b c d = commAssocCross a b c d ∙
   cong (λ u →  (c · a) · u) (·Comm d b) ∙ interchange c a b d ∙
   cong (λ x → ((c · b) · x)) (·Comm a d)

 hasInverse : (x : M) → Type ℓ
 hasInverse x = Σ[ -x ∈ M ] -x · x ≡ ε

 isPropHasInverse : ∀ x → isProp (hasInverse x)
 isPropHasInverse x yinv zinv
   = Σ≡Prop (λ a → is-set (a · x) ε)
    (PathPΣ (MonoidTheory.isPropHasInverse (CommMonoid→Monoid M') x
                                           (hasInverseToMonoid x yinv)
                                           (hasInverseToMonoid x zinv))
                                               .fst)
   where
     hasInverseToMonoid : ∀ x
                        → hasInverse x
                        → MonoidTheory.hasInverse (CommMonoid→Monoid M') x
     hasInverseToMonoid x (y , yinv) = y , yinv , ·Comm x y ∙ yinv
