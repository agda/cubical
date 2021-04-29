{-

This file contains basic theory about subgroups.

The definition is the same as the first definition of subgroups in:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#subgroups-sip

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Subgroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

private
  variable
    ℓ : Level

-- Generalized from Function.Logic. TODO: upstream
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Data.Unit
⊤ : ∀ {ℓ} → hProp ℓ
⊤ = Unit* , (λ _ _ _ → tt*)



-- We assume an ambient group
module _ (G' : Group {ℓ}) where

  open GroupStr (snd G')
  private G = ⟨ G' ⟩

  -- TODO: define as a record and give a name to the field? (c.f. ideals)
  isSubgroup : ℙ G → Type ℓ
  isSubgroup H = (1g ∈ H)
               × ((x y : G) → x ∈ H → y ∈ H → x · y ∈ H)
               × ((x : G) → x ∈ H → inv x ∈ H)

  -- TODO: define as a record?
  Subgroup : Type (ℓ-suc ℓ)
  Subgroup = Σ[ H ∈ ℙ G ] isSubgroup H

  isPropIsSubgroup : (H : ℙ G) → isProp (isSubgroup H)
  isPropIsSubgroup H = isProp×2 (∈-isProp H 1g)
                                (isPropΠ4 λ x y _ _ → ∈-isProp H (x · y))
                                (isPropΠ2 λ x _ → ∈-isProp H (inv x))

  isSetSubgroup : isSet Subgroup
  isSetSubgroup = isSetΣ (isSetℙ G) λ x → isProp→isSet (isPropIsSubgroup x)

  ⟪_⟫ : Subgroup → ℙ G
  ⟪ H , _ ⟫ = H

  isNormal : Subgroup → Type ℓ
  isNormal H = (g h : G) → h ∈ ⟪ H ⟫ → g · h · inv g ∈ ⟪ H ⟫ 

  isPropIsNormal : (H : Subgroup) → isProp (isNormal H)
  isPropIsNormal H = isPropΠ3 λ g h _ → ∈-isProp ⟪ H ⟫ (g · h · inv g)
  
  -- Examples of subgroups
  open GroupTheory G'

  -- We get view all of G as a subset of itself
  groupSubset : ℙ G
  groupSubset x = (x ≡ x) , is-set x x
  
  isSubgroupGroup : isSubgroup groupSubset
  isSubgroupGroup = refl , (λ x y _ _ → refl) , λ x _ → refl

  groupSubgroup : Subgroup
  groupSubgroup = groupSubset , isSubgroupGroup

  -- The trivial subgroup
  trivialSubset : ℙ G
  trivialSubset x = (x ≡ 1g) , is-set x 1g

  isSubgroupTrivialGroup : isSubgroup trivialSubset
  isSubgroupTrivialGroup = refl
                         , (λ x y hx hy → cong (_· y) hx ∙∙ lid y ∙∙ hy)
                         , λ x hx → cong inv hx ∙ inv1g

  trivialSubgroup : Subgroup
  trivialSubgroup = trivialSubset , isSubgroupTrivialGroup

  isNormalTrivialSubgroup : isNormal trivialSubgroup
  isNormalTrivialSubgroup g h h≡1 =
    (g · h · inv g)  ≡⟨ (λ i → g · h≡1 i · inv g) ⟩
    (g · 1g · inv g) ≡⟨ assoc _ _ _ ∙ cong (_· inv g) (rid g) ⟩
    (g · inv g)      ≡⟨ invr g ⟩
    1g ∎
