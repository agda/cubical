
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Higher where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.EilenbergMacLane1
open import Cubical.HITs.EilenbergMacLane1


import Cubical.Foundations.GroupoidLaws as GL

private
  variable
    ℓ ℓ' : Level


record HigherGroup ℓ : Type (ℓ-suc ℓ) where
  constructor highergroup
  field
    base : Pointed ℓ
    isConn : isConnected 2 (typ base)

record BGroup ℓ (n k : ℕ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor bgroup
  field
    base : Pointed ℓ
    isConn : isConnected (k + 1) (typ base)
    isTrun : isOfHLevel (n + k + 2) (typ base)

module _ where
  open BGroup
  η-BGroup : {n k : ℕ} {BG BH : BGroup ℓ n k}
             → (p : typ (base BG) ≡ typ (base BH))
             → (q : PathP (λ i → p i) (pt (base BG)) (pt (base BH)))
             → BG ≡ BH
  base (η-BGroup p q i) .fst = p i
  base (η-BGroup p q i) .snd = q i
  isConn (η-BGroup {k = k} {BG = BG} {BH = BH} p q i) = r i
    where
      r : PathP (λ i → isConnected (k + 1) (p i)) (isConn BG) (isConn BH)
      r = isProp→PathP (λ _ → isPropIsOfHLevel 0) (isConn BG) (isConn BH)
  isTrun (η-BGroup {n = n} {k = k} {BG = BG} {BH = BH} p q i) = s i
    where
      s : PathP (λ i → isOfHLevel (n + k + 2) (p i)) (isTrun BG) (isTrun BH)
      s = isProp→PathP (λ i → isPropIsOfHLevel (n + k + 2)) (isTrun BG) (isTrun BH)


BGroupHom :  {n k : ℕ} (G : BGroup ℓ n k) (H : BGroup ℓ' n k) → Type (ℓ-max ℓ ℓ')
BGroupHom G H = (BGroup.base G) →∙ (BGroup.base H)

BGroupIso :  {n k : ℕ} (G : BGroup ℓ n k) (H : BGroup ℓ' n k) → Type (ℓ-max ℓ ℓ')
BGroupIso G H = (BGroup.base G) ≃∙ (BGroup.base H)

BGroupIso→≡ : {n k : ℕ} {BG BH : BGroup ℓ n k}
                (f : BGroupIso BG BH)
                → BG ≡ BH
BGroupIso→≡ {BG = BG} {BH = BH} f = η-BGroup (ua (≃∙→≃ f)) (toPathP ((uaβ ((≃∙→≃ f)) (pt (BGroup.base BG))) ∙ f .fst .snd))

carrier : {ℓ : Level} {n k : ℕ} (G : BGroup ℓ n k) → Pointed ℓ
carrier {k = k} BG = (Ω^ k) base
  where
    open BGroup BG

1BGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
1BGroup ℓ = BGroup ℓ 0 1

1BGroup→Group : {ℓ : Level} (BG : 1BGroup ℓ) → Group {ℓ}
1BGroup→Group BG =
  makeGroup {G = (pt base) ≡ (pt base)}
            refl
            _∙_
            sym
            (isTrun (pt base) (pt base))
            GL.assoc
            (λ a → sym (GL.rUnit a))
            (λ g → sym (GL.lUnit g))
            GL.rCancel
            GL.lCancel
    where
      open BGroup BG

Group→1BGroup : (G : Group {ℓ}) → 1BGroup ℓ
BGroup.base (Group→1BGroup G) .fst = EM₁ G
BGroup.base (Group→1BGroup G) .snd = embase
BGroup.isConn (Group→1BGroup G) = EM₁Connected G
BGroup.isTrun (Group→1BGroup G) = EM₁Groupoid G



open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

module _ (BG : 1BGroup ℓ) (BH : 1BGroup ℓ') where
  private
    π₁BG = 1BGroup→Group BG
    π₁BH = 1BGroup→Group BH
  -- π₁ functorial action for 1BGroups
  π₁→ : BGroupHom BG BH → GroupHom π₁BG π₁BH
  GroupHom.fun (π₁→ f) g = sym (snd f) ∙∙ cong (fst f) g ∙∙ snd f
  GroupHom.isHom (π₁→ f) g g' =
    (f₂- ∙∙ cong f₁ (g ∙ g') ∙∙ f₂)
      ≡⟨ doubleCompPath-elim' f₂- (cong f₁ (g ∙ g')) f₂ ⟩
    (f₂- ∙ cong f₁ (g ∙ g') ∙ f₂)
      ≡⟨ {!!} ⟩
    (f₂- ∙ (cong f₁ g ∙ cong f₁ g') ∙ f₂)
      ≡⟨ {!!} ⟩
    (f₂- ∙ (cong f₁ g ∙ refl ∙ cong f₁ g') ∙ f₂)
      ≡⟨ {!!} ⟩
    (f₂- ∙ (cong f₁ g ∙ (f₂ ∙ f₂-) ∙ cong f₁ g') ∙ f₂)
      ≡⟨ {!!} ⟩
    (f₂- ∙ cong f₁ g ∙ f₂) ∙ (f₂- ∙ cong f₁ g' ∙ f₂)
      ≡⟨ {!!} ⟩
    (f₂- ∙∙ cong f₁ g ∙∙ f₂) ∙ (f₂- ∙∙ cong f₁ g' ∙∙ f₂) ∎
    where
      f₁ = fst f
      f₂ = snd f
      f₂- = sym (snd f)


module _ (H : Group {ℓ}) (BG : 1BGroup ℓ') where
  private
    EM₁H = Group→1BGroup H
    π₁EM₁H = 1BGroup→Group EM₁H
    π₁BG = 1BGroup→Group BG
    π₁→' : BGroupHom EM₁H BG → GroupHom π₁EM₁H π₁BG
    π₁→' = π₁→ EM₁H BG

  H→π₁EM₁H : GroupHom H π₁EM₁H
  GroupHom.fun H→π₁EM₁H = Iso.inv (ΩEM₁Iso H)
  GroupHom.isHom H→π₁EM₁H = {!!}

  π₁← : GroupHom π₁EM₁H π₁BG → BGroupHom EM₁H BG
  π₁← f .fst =
    rec' H
        (BGroup.isTrun BG)
        (BGroup.base BG .snd)
        (GroupHom.fun (compGroupHom H→π₁EM₁H f))
        λ g h → sym (GroupHom.isHom (compGroupHom H→π₁EM₁H f) g h)
  π₁← f .snd =
    (π₁← f) .fst (pt (BGroup.base EM₁H))
      ≡⟨ refl ⟩
    pt (BGroup.base BG) ∎

  π₁←-onIso : GroupEquiv π₁EM₁H π₁BG → BGroupIso EM₁H BG
  π₁←-onIso f .fst = π₁← (GroupEquiv.hom f)
  π₁←-onIso f .snd = isEmbedding×isSurjection→isEquiv (isEmbedding-φ , isSurjection-φ)
    where
      φ : BGroupHom EM₁H BG
      φ = π₁← (GroupEquiv.hom f)
      isEmbedding-φ : isEmbedding (fst φ)
      isEmbedding-φ = {!!}

      isSurjection-φ : isSurjection (fst φ)
      isSurjection-φ = {!!}

IsoGroup1BGroup : (ℓ : Level) → Iso (Group {ℓ}) (1BGroup ℓ)
Iso.fun (IsoGroup1BGroup ℓ) = Group→1BGroup
Iso.inv (IsoGroup1BGroup ℓ) = 1BGroup→Group
Iso.leftInv (IsoGroup1BGroup ℓ) G = η-Group (ΩEM₁≡ G) {!!} {!!} {!!} {!!}
Iso.rightInv (IsoGroup1BGroup ℓ) BG = BGroupIso→≡ (π₁←-onIso π₁BG BG φ)
  where
    π₁BG = 1BGroup→Group BG
    EM₁π₁BG = Group→1BGroup π₁BG
    π₁EM₁π₁BG = 1BGroup→Group EM₁π₁BG

    φ : GroupEquiv π₁EM₁π₁BG π₁BG
    φ = equivFun (invEquiv (GroupPath π₁EM₁π₁BG π₁BG)) (η-Group (ΩEM₁≡ π₁BG) {!!} {!!} {!!} {!!})
