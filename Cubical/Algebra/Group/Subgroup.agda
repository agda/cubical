{-

This file contains basic theory about subgroups.

The definition is the same as the first definition of subgroups in:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#subgroups-sip

-}
{-# OPTIONS --safe #-}
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

-- We assume an ambient group
module _ (G' : Group ℓ) where

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
  isSetSubgroup = isSetΣ isSetℙ λ x → isProp→isSet (isPropIsSubgroup x)

  Subgroup→Group : Subgroup → Group ℓ
  Subgroup→Group (H , Hh) = makeGroup-right 1HG _·HG_ invHG isSetHG assocHG ridHG invrHG
    where
    HG = Σ[ x ∈ G ] ⟨ H x ⟩
    isSetHG = isSetΣ is-set (λ x → isProp→isSet (H x .snd))

    1HG : HG
    1HG = (1g , (id-closed Hh))

    _·HG_ : HG → HG → HG
    (x , Hx) ·HG (y , Hy) = (x · y) , (op-closed Hh Hx Hy)

    invHG : HG → HG
    invHG (x , Hx) = inv x , inv-closed Hh Hx

    assocHG : (x y z : HG) → x ·HG (y ·HG z) ≡ (x ·HG y) ·HG z
    assocHG (x , Hx) (y , Hy) (z , Hz) =
      ΣPathP (assoc x y z , isProp→PathP (λ i → H (assoc x y z i) .snd) _ _)

    ridHG : (x : HG) → x ·HG 1HG ≡ x
    ridHG (x , Hx) = ΣPathP (rid x , isProp→PathP (λ i → H (rid x i) .snd) _ _)

    invrHG : (x : HG) → x ·HG invHG x ≡ 1HG
    invrHG (x , Hx) = ΣPathP (invr x , isProp→PathP (λ i → H (invr x i) .snd) _ _)

⟪_⟫ : {G' : Group ℓ} → Subgroup G' → ℙ (G' .fst)
⟪ H , _ ⟫ = H

module _ {G' : Group ℓ} where

  open GroupStr (snd G')
  open isSubgroup
  open GroupTheory G'
  private G = ⟨ G' ⟩

  isNormal : Subgroup G' → Type ℓ
  isNormal H = (g h : G) → h ∈ ⟪ H ⟫ → g · h · inv g ∈ ⟪ H ⟫

  isPropIsNormal : (H : Subgroup G') → isProp (isNormal H)
  isPropIsNormal H = isPropΠ3 λ g h _ → ∈-isProp ⟪ H ⟫ (g · h · inv g)

  ·CommNormalSubgroup : (H : Subgroup G') (Hnormal : isNormal H) {x y : G}
                      → x · y ∈ ⟪ H ⟫ → y · x ∈ ⟪ H ⟫
  ·CommNormalSubgroup H Hnormal {x = x} {y = y} Hxy =
    subst-∈ ⟪ H ⟫ rem (Hnormal (inv x) (x · y) Hxy)
      where
      rem : inv x · (x · y) · inv (inv x) ≡ y · x
      rem = inv x · (x · y) · inv (inv x) ≡⟨ assoc _ _ _ ⟩
            (inv x · x · y) · inv (inv x) ≡⟨ (λ i → assoc (inv x) x y i · invInv x i) ⟩
            ((inv x · x) · y) · x         ≡⟨ cong (λ z → (z · y) · x) (invl x) ⟩
            (1g · y) · x                  ≡⟨ cong (_· x) (lid y) ⟩
            y · x                         ∎


  -- Examples of subgroups

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

NormalSubgroup : (G : Group ℓ) → Type _
NormalSubgroup G = Σ[ G ∈ Subgroup G ] isNormal G


-- Can one get this to work with different universes for G and H?
module _ {G H : Group ℓ} (ϕ : GroupHom G H) where

  open isSubgroup
  open GroupTheory

  private
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)
    f = ϕ .fst
    module ϕ = IsGroupHom (ϕ .snd)

  imSubset : ℙ ⟨ H ⟩
  imSubset x = isInIm ϕ x , isPropIsInIm ϕ x

  isSubgroupIm : isSubgroup H imSubset
  id-closed isSubgroupIm = ∣ G.1g , ϕ.pres1 ∣
  op-closed isSubgroupIm =
    map2 λ { (x , hx) (y , hy) → x G.· y , ϕ.pres· x y ∙ λ i → hx i H.· hy i }
  inv-closed isSubgroupIm = map λ { (x , hx) → G.inv x , ϕ.presinv x ∙ cong H.inv hx }

  imSubgroup : Subgroup H
  imSubgroup = imSubset , isSubgroupIm

  imGroup : Group ℓ
  imGroup = Subgroup→Group _ imSubgroup

  kerSubset : ℙ ⟨ G ⟩
  kerSubset x = isInKer ϕ x , isPropIsInKer ϕ x

  isSubgroupKer : isSubgroup G kerSubset
  id-closed isSubgroupKer = ϕ.pres1
  op-closed isSubgroupKer {x} {y} hx hy =
    ϕ.pres· x y ∙∙ (λ i → hx i H.· hy i) ∙∙ H.rid _
  inv-closed isSubgroupKer hx = ϕ.presinv _ ∙∙ cong H.inv hx ∙∙ inv1g H

  kerSubgroup : Subgroup G
  kerSubgroup = kerSubset , isSubgroupKer

  isNormalKer : isNormal kerSubgroup
  isNormalKer x y hy =
    f (x G.· y G.· G.inv x)         ≡⟨ ϕ.pres· _ _ ⟩
    f x H.· f (y G.· G.inv x)       ≡⟨ cong (f x H.·_) (ϕ.pres· _ _) ⟩
    f x H.· f y H.· f (G.inv x)     ≡⟨ (λ i → f x H.· hy i H.· f (G.inv x)) ⟩
    f x H.· (H.1g H.· f (G.inv x))  ≡⟨ cong (f x H.·_) (H.lid _) ⟩
    f x H.· f (G.inv x)             ≡⟨ cong (f x H.·_) (ϕ.presinv x) ⟩
    f x H.· H.inv (f x)             ≡⟨ H.invr _ ⟩
    H.1g                            ∎
