-- The SIP applied to groups
{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.Group.GroupPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Properties
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Functions.Embedding

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso
open GroupStr
open IsGroupHom

𝒮ᴰ-Group : DUARel (𝒮-Univ ℓ) GroupStr ℓ
𝒮ᴰ-Group =
  𝒮ᴰ-Record (𝒮-Univ _) IsGroupEquiv
    (fields:
      data[ _·_ ∣ autoDUARel _ _ ∣ pres· ]
      data[ 1g ∣ autoDUARel _ _ ∣ pres1 ]
      data[ inv ∣ autoDUARel _ _ ∣ presinv ]
      prop[ isGroup ∣ (λ _ _ → isPropIsGroup _ _ _) ])
  where
  open GroupStr
  open IsGroupHom

GroupPath : (M N : Group ℓ) → GroupEquiv M N ≃ (M ≡ N)
GroupPath = ∫ 𝒮ᴰ-Group .UARel.ua


-- The module below defines a group induced from an equivalence
-- between a group G and a type A which preserves the full raw group
-- structure from G to A. This version is useful when proving that
-- some type equivalent to a group is a group while also specifying
-- the binary operation, unit and inverse.
module _ (G : Group ℓ) {A : Type ℓ}
  (m : A → A → A)
  (u : A)
  (inverse : A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p· : ∀ x y → e .fst (G .snd ._·_ x y) ≡ m (e .fst x) (e .fst y))
  (pu : e .fst (G .snd .1g) ≡ u)
  (pinv : ∀ x → e .fst (G .snd .inv x) ≡ inverse (e .fst x))
  where

  private
    module G = GroupStr (G .snd)

    BaseΣ : Type (ℓ-suc ℓ)
    BaseΣ = Σ[ B ∈ Type ℓ ] (B → B → B) × B × (B → B)

    FamilyΣ : BaseΣ → Type ℓ
    FamilyΣ (B , m , u , i) = IsGroup u m i

    inducedΣ : FamilyΣ (A , m , u , inverse)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel BaseΣ) (e , p· , pu , pinv))
        G.isGroup

  InducedGroup : Group ℓ
  InducedGroup .fst = A
  InducedGroup .snd ._·_ = m
  InducedGroup .snd .1g = u
  InducedGroup .snd .inv = inverse
  InducedGroup .snd .isGroup = inducedΣ

  InducedGroupEquiv : GroupEquiv G InducedGroup
  fst InducedGroupEquiv = e
  snd InducedGroupEquiv = makeIsGroupHom p·

  InducedGroupPath : G ≡ InducedGroup
  InducedGroupPath = GroupPath _ _ .fst InducedGroupEquiv


-- The module below defines a group induced from an equivalence which
-- preserves the binary operation (i.e. a group isomorphism). This
-- version is useful when proving that some type equivalent to a group
-- G is a group when one doesn't care about what the unit and inverse
-- are. When using this version the unit and inverse will both be
-- defined by transporting over the unit and inverse from G to A.
module _ (G : Group ℓ) {A : Type ℓ}
  (m : A → A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p· : ∀ x y → e .fst (G .snd ._·_ x y) ≡ m (e .fst x) (e .fst y))
  where

  private
    module G = GroupStr (G .snd)

    FamilyΣ : Σ[ B ∈ Type ℓ ] (B → B → B) → Type ℓ
    FamilyΣ (B , n) = Σ[ e ∈ B ] Σ[ i ∈ (B → B) ] IsGroup e n i

    inducedΣ : FamilyΣ (A , m)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel (Σ[ B ∈ Type ℓ ] (B → B → B))) (e , p·))
        (G.1g , G.inv , G.isGroup)

  InducedGroupFromPres· : Group ℓ
  InducedGroupFromPres· .fst = A
  InducedGroupFromPres· .snd ._·_ = m
  InducedGroupFromPres· .snd .1g = inducedΣ .fst
  InducedGroupFromPres· .snd .inv = inducedΣ .snd .fst
  InducedGroupFromPres· .snd .isGroup = inducedΣ .snd .snd

  InducedGroupEquivFromPres· : GroupEquiv G InducedGroupFromPres·
  fst InducedGroupEquivFromPres· = e
  snd InducedGroupEquivFromPres· = makeIsGroupHom p·

  InducedGroupPathFromPres· : G ≡ InducedGroupFromPres·
  InducedGroupPathFromPres· = GroupPath _ _ .fst InducedGroupEquivFromPres·

uaGroup : {G H : Group ℓ} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

caracGroup≡ : {G H : Group ℓ} (p q : G ≡ H) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
caracGroup≡ _ _ α =
  isEmbedding→Inj (iso→isEmbedding (invIso ΣPathIsoPathΣ)) _ _ $
  Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetGroupStr _) _ _) α

uaGroupId : (G : Group ℓ) → uaGroup (idGroupEquiv {G = G}) ≡ refl
uaGroupId G = caracGroup≡ _ _ uaIdEquiv

uaCompGroupEquiv : {F G H : Group ℓ} (f : GroupEquiv F G) (g : GroupEquiv G H)
                 → uaGroup (compGroupEquiv f g) ≡ uaGroup f ∙ uaGroup g
uaCompGroupEquiv f g = caracGroup≡ _ _ (
  cong ⟨_⟩ (uaGroup (compGroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  cong ⟨_⟩ (uaGroup f) ∙ cong ⟨_⟩ (uaGroup g)
    ≡⟨ sym (cong-∙ ⟨_⟩ (uaGroup f) (uaGroup g)) ⟩
  cong ⟨_⟩ (uaGroup f ∙ uaGroup g) ∎)

-- J-rule for GroupEquivs
GroupEquivJ : {G : Group ℓ} (P : (H : Group ℓ) → GroupEquiv G H → Type ℓ')
  → P G idGroupEquiv
  → ∀ {H} e → P H e
GroupEquivJ P p e = 𝒮-J-customRefl≅ (∫ 𝒮ᴰ-Group) P p e

GroupEquivJ>_ : {ℓ : Level} {ℓ' : Level} {G : Group ℓ}
   {P : (H : Group ℓ) → GroupEquiv G H → Type ℓ'} →
   P G idGroupEquiv → (H : Group ℓ) (e : GroupEquiv G H) → P H e
GroupEquivJ>_ {P = P} ids H = GroupEquivJ (λ H e → P H e) ids

isGroupoidGroup : ∀ {ℓ} → isGroupoid (Group ℓ)
isGroupoidGroup G H =
  isOfHLevelRespectEquiv 2 (GroupPath _ _)
    (isOfHLevelΣ 2 (isOfHLevel≃ 2 (GroupStr.is-set (snd G)) (GroupStr.is-set (snd H)))
      λ _ → isProp→isSet (isPropIsGroupHom _ _))

module _ {ℓ ℓ'} {A : Type ℓ}
  (G : A → Group ℓ')
  (G-coh : (x y : A) → GroupEquiv (G x) (G y))
  (G-coh-coh : (x y z : A) (g : fst (G x))
    → fst (fst (G-coh y z)) ((fst (fst (G-coh x y)) g))
     ≡ fst (fst (G-coh x z)) g ) where

  PropTrunc→Group-coh : (x y : A) → G x ≡ G y
  PropTrunc→Group-coh x y = uaGroup (G-coh x y)

  PropTrunc→Group-coh-coh : (x y z : A) → compGroupEquiv (G-coh x y) (G-coh y z) ≡ G-coh x z
  PropTrunc→Group-coh-coh x y z =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt (G-coh-coh x y z)))

  PropTrunc→Group : ∥ A ∥₁ → Group ℓ'
  PropTrunc→Group = rec→Gpd isGroupoidGroup
    G
    (record { link = PropTrunc→Group-coh
            ; coh₁ = coh-coh })
    where
    coh-coh : (x y z : A)
      → Square (PropTrunc→Group-coh x y) (PropTrunc→Group-coh x z)
                refl (PropTrunc→Group-coh y z)
    coh-coh x y z =
      compPathL→PathP
          (sym (lUnit _)
        ∙∙ sym (uaCompGroupEquiv (G-coh x y) (G-coh y z))
        ∙∙ cong uaGroup (PropTrunc→Group-coh-coh x y z))

-- action of of uaGroup on GroupHom
module _ {ℓ ℓ' : Level} {G1 : Group ℓ} {H1 : Group ℓ'} where
  private
    pre-PathPGroupHom : ∀
      (G2 : Group ℓ)
      (eG : GroupEquiv G1 G2)
      (H2 : Group ℓ') (eH : GroupEquiv H1 H2)
      (ϕ : GroupHom G1 H1) (ψ : GroupHom G2 H2)
      → compGroupHom (GroupEquiv→GroupHom eG) ψ
       ≡ compGroupHom ϕ (GroupEquiv→GroupHom eH)
      → PathP (λ i → GroupHom (uaGroup eG i) (uaGroup eH i))
               ϕ ψ
    pre-PathPGroupHom =
      GroupEquivJ> (GroupEquivJ>
       λ ϕ ψ → λ s
      → toPathP ((λ s
      → transport (λ i → GroupHom (uaGroupId G1 s i) (uaGroupId H1 s i)) ϕ)
      ∙ transportRefl ϕ
      ∙ Σ≡Prop (λ _ → isPropIsGroupHom _ _) (sym (cong fst s))))

  PathPGroupHom : {G2 : Group ℓ} (eG : GroupEquiv G1 G2)
                  {H2 : Group ℓ'} (eH : GroupEquiv H1 H2)
                  {ϕ : GroupHom G1 H1} {ψ : GroupHom G2 H2}
      → compGroupHom (GroupEquiv→GroupHom eG) ψ
       ≡ compGroupHom ϕ (GroupEquiv→GroupHom eH)
      → PathP (λ i → GroupHom (uaGroup eG i) (uaGroup eH i)) ϕ ψ
  PathPGroupHom eG eH p = pre-PathPGroupHom _ eG _ eH _ _ p

  module _ {H2 : Group ℓ'} (eH : GroupEquiv H1 H2)
           {ϕ : GroupHom G1 H1} {ψ : GroupHom G1 H2} where
    PathPGroupHomₗ : ψ ≡ compGroupHom ϕ (GroupEquiv→GroupHom eH)
        → PathP (λ i → GroupHom G1 (uaGroup eH i)) ϕ ψ
    PathPGroupHomₗ p =
      transport (λ k → PathP (λ i → GroupHom (uaGroupId G1 k i) (uaGroup eH i)) ϕ ψ)
        (PathPGroupHom idGroupEquiv eH
         (Σ≡Prop (λ _ → isPropIsGroupHom _ _) (cong fst p)))

    PathPGroupHomₗ' : compGroupHom ψ (GroupEquiv→GroupHom (invGroupEquiv eH)) ≡ ϕ
        → PathP (λ i → GroupHom G1 (uaGroup eH i)) ϕ ψ
    PathPGroupHomₗ' p =
      PathPGroupHomₗ
        (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
          (funExt (λ s → sym (secEq (fst eH) (fst ψ s))))
      ∙ cong (λ ϕ → compGroupHom ϕ (GroupEquiv→GroupHom eH)) p)

  module _ {G2 : Group ℓ} (eG : GroupEquiv G1 G2)
           {ϕ : GroupHom G1 H1} {ψ : GroupHom G2 H1}
    where
    PathPGroupHomᵣ : compGroupHom (GroupEquiv→GroupHom eG) ψ ≡ ϕ
      → PathP (λ i → GroupHom (uaGroup eG i) H1) ϕ ψ
    PathPGroupHomᵣ p =
      transport (λ k → PathP (λ i → GroupHom (uaGroup eG i) (uaGroupId H1 k i)) ϕ ψ)
        (PathPGroupHom eG idGroupEquiv
         (Σ≡Prop (λ _ → isPropIsGroupHom _ _) (cong fst p)))

    PathPGroupHomᵣ' : ψ ≡ compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eG)) ϕ
      → PathP (λ i → GroupHom (uaGroup eG i) H1) ϕ ψ
    PathPGroupHomᵣ' p = PathPGroupHomᵣ
      (cong (compGroupHom (GroupEquiv→GroupHom eG)) p
      ∙ Σ≡Prop (λ _ → isPropIsGroupHom _ _)
         (funExt λ x → cong (fst ϕ) (retEq (fst eG) x)))
