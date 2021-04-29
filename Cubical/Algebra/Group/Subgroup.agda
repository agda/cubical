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
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

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

  record isSubgroup (H : ℙ G) : Type ℓ where
    field
      id-closed  : (1g ∈ H)
      op-closed  : {x y : G} → x ∈ H → y ∈ H → x · y ∈ H
      inv-closed : {x : G} → x ∈ H → inv x ∈ H

  open isSubgroup

  Subgroup : Type (ℓ-suc ℓ)
  Subgroup = Σ[ H ∈ ℙ G ] isSubgroup H

  isPropIsSubgroup : (H : ℙ G) → isProp (isSubgroup H)
  id-closed (isPropIsSubgroup H h1 h2 i) =
    ∈-isProp H 1g (h1 .id-closed) (h2 .id-closed) i
  op-closed (isPropIsSubgroup H h1 h2 i) Hx Hy =
    ∈-isProp H _ (h1 .op-closed Hx Hy) (h2 .op-closed Hx Hy) i
  inv-closed (isPropIsSubgroup H h1 h2 i) Hx =
    ∈-isProp H _ (h1 .inv-closed Hx) (h2 .inv-closed Hx) i

  isSetSubgroup : isSet Subgroup
  isSetSubgroup = isSetΣ (isSetℙ G) λ x → isProp→isSet (isPropIsSubgroup x)

module _ {G' : Group {ℓ}} where

  open GroupStr (snd G')
  open isSubgroup
  private G = ⟨ G' ⟩

  ⟪_⟫ : Subgroup G' → ℙ G
  ⟪ H , _ ⟫ = H

  isNormal : Subgroup G' → Type ℓ
  isNormal H = (g h : G) → h ∈ ⟪ H ⟫ → g · h · inv g ∈ ⟪ H ⟫

  isPropIsNormal : (H : Subgroup G') → isProp (isNormal H)
  isPropIsNormal H = isPropΠ3 λ g h _ → ∈-isProp ⟪ H ⟫ (g · h · inv g)

  -- Examples of subgroups
  open GroupTheory G'

  -- We can view all of G as a subset of itself
  groupSubset : ℙ G
  groupSubset x = (x ≡ x) , is-set x x

  isSubgroupGroup : isSubgroup G' groupSubset
  id-closed isSubgroupGroup = refl
  op-closed isSubgroupGroup _ _ = refl
  inv-closed isSubgroupGroup _ = refl

  groupSubgroup : Subgroup G'
  groupSubgroup = groupSubset , isSubgroupGroup

  -- The trivial subgroup
  trivialSubset : ℙ G
  trivialSubset x = (x ≡ 1g) , is-set x 1g

  isSubgroupTrivialGroup : isSubgroup G' trivialSubset
  id-closed isSubgroupTrivialGroup = refl
  op-closed isSubgroupTrivialGroup hx hy = cong (_· _) hx ∙∙ lid _ ∙∙ hy
  inv-closed isSubgroupTrivialGroup hx = cong inv hx ∙ inv1g

  trivialSubgroup : Subgroup G'
  trivialSubgroup = trivialSubset , isSubgroupTrivialGroup

  isNormalTrivialSubgroup : isNormal trivialSubgroup
  isNormalTrivialSubgroup g h h≡1 =
    (g · h · inv g)  ≡⟨ (λ i → g · h≡1 i · inv g) ⟩
    (g · 1g · inv g) ≡⟨ assoc _ _ _ ∙ cong (_· inv g) (rid g) ⟩
    (g · inv g)      ≡⟨ invr g ⟩
    1g ∎

-- Can one get this to work with different universes for G and H?
module _ {G H : Group {ℓ}} (ϕ : GroupHom G H) where

  open isSubgroup
  open GroupHom
  open GroupTheory

  private
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)
    f = fun ϕ

  imSubset : ℙ ⟨ H ⟩
  imSubset x = isInIm ϕ x , isPropIsInIm ϕ x

  isSubgroupIm : isSubgroup H imSubset
  id-closed isSubgroupIm = ∣ G.1g , hom1g ϕ ∣
  op-closed isSubgroupIm =
    map2 λ { (x , hx) (y , hy) → x G.· y , ϕ .isHom x y ∙ λ i → hx i H.· hy i }
  inv-closed isSubgroupIm = map λ { (x , hx) → G.inv x , homInv ϕ x ∙ cong H.inv hx }

  imSubgroup : Subgroup H
  imSubgroup = imSubset , isSubgroupIm

  kerSubset : ℙ ⟨ G ⟩
  kerSubset x = isInKer ϕ x , isPropIsInKer ϕ x

  isSubgroupKer : isSubgroup G kerSubset
  id-closed isSubgroupKer = hom1g ϕ
  op-closed isSubgroupKer {x} {y} hx hy =
    ϕ .isHom x y ∙∙ (λ i → hx i H.· hy i) ∙∙ H.rid _
  inv-closed isSubgroupKer hx = homInv ϕ _ ∙∙ cong H.inv hx ∙∙ inv1g H

  kerSubgroup : Subgroup G
  kerSubgroup = kerSubset , isSubgroupKer

  isNormalKer : isNormal kerSubgroup
  isNormalKer x y hy =
    f (x G.· y G.· G.inv x)         ≡⟨ ϕ .isHom _ _ ⟩
    f x H.· f (y G.· G.inv x)       ≡⟨ cong (f x H.·_) (ϕ .isHom _ _) ⟩
    f x H.· f y H.· f (G.inv x)     ≡⟨ (λ i → f x H.· hy i H.· f (G.inv x)) ⟩
    f x H.· (H.1g H.· f (G.inv x))  ≡⟨ cong (f x H.·_) (H.lid _) ⟩
    f x H.· f (G.inv x)             ≡⟨ cong (f x H.·_) (homInv ϕ x) ⟩
    f x H.· H.inv (f x)             ≡⟨ H.invr _ ⟩
    H.1g                            ∎
