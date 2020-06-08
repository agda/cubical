{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Group.Morphism where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Structures.Group.Base
open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Group {ℓ}
    H : Group {ℓ'}

-- The following definitions of isGroupHom and isGroupIso are level-wise heterogeneous.
-- When applied to groups G and H of the same level, the underlying notion is exactly that
-- used in binaryFunSNS.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.
-- Maybe a more general definition of the SIP taking into account such heterogeneous
-- equivalences could make this redundant.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) → (⟨ G ⟩ → ⟨ H ⟩) → Type (ℓ-max ℓ ℓ')
isGroupHom G H f = (g g' : ⟨ G ⟩) → f (g ⋆¹ g') ≡ (f g ⋆² f g') where
  _⋆¹_ = group-operation G
  _⋆²_ = group-operation H

isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → group-is-set H _ _

isGroupIso : (G : Group {ℓ}) (H : Group {ℓ'}) → (⟨ G ⟩ ≃ ⟨ H ⟩) → Type (ℓ-max ℓ ℓ')
isGroupIso G H (f , eq) = isGroupHom G H f

GroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
GroupHom G H = Σ (⟨ G ⟩ → ⟨ H ⟩) (isGroupHom G H)

GroupIso : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
GroupIso {ℓ} {ℓ'} G H = Σ (⟨ G ⟩ ≃ ⟨ H ⟩) (isGroupIso G H)

-- Morphism composition
isGroupHomComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (fst g ∘ fst f)
isGroupHomComp F G H (f , morph-f) (g , morph-g) x y =
  cong g (morph-f _ _) ∙ morph-g _ _
  
compGroupHom : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → GroupHom F G → GroupHom G H → GroupHom F H
compGroupHom F G H (f , morph-f) (g , morph-g) =
  g ∘ f , isGroupHomComp F G H (f , morph-f) (g , morph-g)

compGroupIso : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → GroupIso F G → GroupIso G H → GroupIso F H
compGroupIso F G H (f , morph-f)  (g , morph-g) =
  compEquiv f g , isGroupHomComp F G H (fst f , morph-f) (fst g , morph-g)

-- Isomorphism inversion
isGroupHomInv : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupIso G H) → isGroupHom H G (invEq (fst f))
isGroupHomInv G H  ((f , eq) , morph) h h' = isInj-f _ _ (
  f (g (h ⋆² h') )
    ≡⟨ retEq (f , eq) _ ⟩
  h ⋆² h'
    ≡⟨ sym (λ i → retEq (f , eq) h i ⋆² retEq (f , eq) h' i) ⟩
  f (g h) ⋆² f (g h')
    ≡⟨ sym (morph _ _) ⟩
  f (g h ⋆¹ g h') ∎)
  where
  _⋆¹_ = group-operation G
  _⋆²_ = group-operation H
  g = invEq (f , eq)
  isEmbedding-f : isEmbedding f
  isEmbedding-f = isEquiv→isEmbedding eq
  isInj-f : (x y : ⟨ G ⟩) → f x ≡ f y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding eq x y)

invGroup : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupIso G H → GroupIso H G
invGroup G H (f , morph) = invEquiv f , isGroupHomInv G H (f , morph)

-- Homomorphism and Isomorphism equality
groupHomEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupHom G H) → (fst f ≡ fst g) → f ≡ g
groupHomEq G H f g p = ΣProp≡ (λ _ → isPropIsGroupHom G H) p

groupIsoEq : (G : Group {ℓ}) (H : Group {ℓ'}) (f g : GroupIso G H) → (fst f ≡ fst g) → f ≡ g
groupIsoEq G H f g p = ΣProp≡ (λ _ → isPropIsGroupHom G H) p

-- Group paths equivalent to equality
group-is-SNS : SNS {ℓ} group-structure isGroupIso
group-is-SNS = add-axioms-SNS _ group-axioms-isProp binaryFunSNS

group-ua : (M N : Group {ℓ}) → (M ≃[ isGroupIso ] N) → M ≡ N
group-ua = sip group-is-SNS

group-univalence : (M N : Group {ℓ}) → (M ≃[ isGroupIso ] N) ≃ (M ≡ N)
group-univalence = SIP group-is-SNS
