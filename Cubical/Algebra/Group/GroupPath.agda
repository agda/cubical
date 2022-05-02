-- The SIP applied to groups
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.GroupPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

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

-- TODO: Induced structure results are temporarily inconvenient while we transition between algebra
-- representations
module _ (G : Group ℓ) {A : Type ℓ} (m : A → A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p· : ∀ x y → e .fst (G .snd ._·_ x y) ≡ m (e .fst x) (e .fst y))
  where

  private
    module G = GroupStr (G .snd)

    FamilyΣ : Σ[ B ∈ Type ℓ ] (B → B → B) → Type ℓ
    FamilyΣ (B , n) =
      Σ[ e ∈ B ]
      Σ[ i ∈ (B → B) ]
      IsGroup e n i

    inducedΣ : FamilyΣ (A , m)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel (Σ[ B ∈ Type ℓ ] (B → B → B))) (e , p·))
        (G.1g , G.inv , G.isGroup)

  InducedGroup : Group ℓ
  InducedGroup .fst = A
  InducedGroup .snd ._·_ = m
  InducedGroup .snd .1g = inducedΣ .fst
  InducedGroup .snd .inv = inducedΣ .snd .fst
  InducedGroup .snd .isGroup = inducedΣ .snd .snd

  InducedGroupEquiv : GroupEquiv G InducedGroup
  fst InducedGroupEquiv = e
  snd InducedGroupEquiv = makeIsGroupHom p·

  InducedGroupPath : G ≡ InducedGroup
  InducedGroupPath = GroupPath _ _ .fst InducedGroupEquiv

uaGroup : {G H : Group ℓ} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

-- Group-ua functoriality
Group≡ : (G H : Group ℓ) → (
  Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ]
  Σ[ q ∈ PathP (λ i → p i) (1g (snd G)) (1g (snd H)) ]
  Σ[ r ∈ PathP (λ i → p i → p i → p i) (_·_ (snd G)) (_·_ (snd H)) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (inv (snd G)) (inv (snd H)) ]
  PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup (snd G)) (isGroup (snd H)))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv theIso
  where
  theIso : Iso _ _
  fun theIso (p , q , r , s , t) i = p i , groupstr (q i) (r i) (s i) (t i)
  inv theIso x = cong ⟨_⟩ x , cong (1g ∘ snd) x , cong (_·_ ∘ snd) x , cong (inv ∘ snd) x , cong (isGroup ∘ snd) x
  rightInv theIso _ = refl
  leftInv theIso _ = refl

caracGroup≡ : {G H : Group ℓ} (p q : G ≡ H) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
caracGroup≡ {G = G} {H = H} p q P =
  sym (transportTransport⁻ (ua (Group≡ G H)) p)
                                   ∙∙ cong (transport (ua (Group≡ G H))) helper
                                   ∙∙ transportTransport⁻ (ua (Group≡ G H)) q
    where
    helper : transport (sym (ua (Group≡ G H))) p ≡ transport (sym (ua (Group≡ G H))) q
    helper = Σ≡Prop
               (λ _ → isPropΣ
                         (isOfHLevelPathP' 1 (is-set (snd H)) _ _)
                         λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd H)) _ _)
                         λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd H)) _ _)
                         λ _ → isOfHLevelPathP 1 (isPropIsGroup _ _ _) _ _)
               (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

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
GroupEquivJ {G = G} P p {H} e =
  transport (λ i → P (GroupPath G H .fst e i)
    (transp (λ j → GroupEquiv G (GroupPath G H .fst e (i ∨ ~ j))) i e))
      (subst (P G) (sym lem) p)
  where
  lem : transport (λ j → GroupEquiv G (GroupPath G H .fst e (~ j))) e
       ≡ idGroupEquiv
  lem = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
       (Σ≡Prop (λ _ → isPropIsEquiv _)
         (funExt λ x → (λ i → fst (fst (fst e .snd .equiv-proof
                          (transportRefl (fst (fst e) (transportRefl x i)) i))))
                         ∙ retEq (fst e) x))
