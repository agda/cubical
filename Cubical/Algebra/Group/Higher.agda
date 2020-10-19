
{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Higher where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Base
open import Cubical.Homotopy.PointedFibration
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.EilenbergMacLane1
open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.Truncation.FromNegOne as Trunc renaming (rec to trRec)
open import Cubical.HITs.SetTruncation
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

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

BGroupΣ : {ℓ : Level} (n k : ℕ) → Type (ℓ-suc ℓ)
BGroupΣ {ℓ} n k = Σ[ A ∈ Type ℓ ] A × (isConnected (k + 1) A) × (isOfHLevel (n + k + 2) A)

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

-- morphisms

BGroupHom : {n k : ℕ} (G : BGroup ℓ n k) (H : BGroup ℓ' n k) → Type (ℓ-max ℓ ℓ')
BGroupHom G H = (BGroup.base G) →∙ (BGroup.base H)

BGroupHomΣ : {n k : ℕ} (BG : BGroupΣ {ℓ} n k) (BH : BGroupΣ {ℓ'} n k) → Type (ℓ-max ℓ ℓ')
BGroupHomΣ (base , pt , _) (base' , pt' , _) = (base , pt) →∙ (base' , pt')

isOfHLevel-BGroupHomΣ : {n k : ℕ} (BG : BGroupΣ {ℓ} n k) (BH : BGroupΣ {ℓ'} n k)
                        → isOfHLevel (n + 2) (BGroupHomΣ BG BH)
isOfHLevel-BGroupHomΣ {n = n} {k = k} BG BH = x'
  where
    z : isOfHLevel (n + k + 2) (fst BH)
    z = snd (snd (snd BH))
    z' : isOfHLevel (n + 1 + 1 + k) (fst BH)
    z' = subst (λ m → isOfHLevel m (fst BH))
               (n + k + 2 ≡⟨ sym (+-assoc n k 2) ⟩
               n + (k + 2) ≡⟨ cong (n +_) (+-comm k 2) ⟩
               n + (2 + k) ≡⟨ +-assoc n 2 k ⟩
               (n + 2) + k ≡⟨ cong (_+ k) (+-assoc n 1 1) ⟩
               n + 1 + 1 + k ∎)
               z
    x : isOfHLevel (n + 1 + 1) (BGroupHomΣ BG BH)
    x = sec∙Trunc (fst BG , fst (snd BG)) (fst (snd (snd BG))) λ _ → (fst BH , fst (snd BH)) , z'
    x' : isOfHLevel (n + 2) (BGroupHomΣ BG BH)
    x' = subst (λ m → isOfHLevel m (BGroupHomΣ BG BH)) (sym (+-assoc n 1 1)) x

BGroupIso : {n k : ℕ} (G : BGroup ℓ n k) (H : BGroup ℓ' n k) → Type (ℓ-max ℓ ℓ')
BGroupIso G H = (BGroup.base G) ≃∙ (BGroup.base H)


BGroupIdIso : {n k : ℕ} (BG : BGroup ℓ n k) → BGroupIso BG BG
BGroupIdIso BG = idEquiv∙ (BGroup.base BG)

BGroupIso→≡ : {n k : ℕ} {BG BH : BGroup ℓ n k}
                (f : BGroupIso BG BH)
                → BG ≡ BH
BGroupIso→≡ {BG = BG} {BH = BH} f = η-BGroup (ua (≃∙→≃ f)) (toPathP ((uaβ ((≃∙→≃ f)) (pt (BGroup.base BG))) ∙ f .fst .snd))


-- getters
carrier : {ℓ : Level} {n k : ℕ} (G : BGroup ℓ n k) → Pointed ℓ
carrier {k = k} BG = (Ω^ k) base
  where
    open BGroup BG

basetype : {ℓ : Level} {n k : ℕ} (BG : BGroup ℓ n k) → Type ℓ
basetype BG = typ (BGroup.base BG)

basepoint : {ℓ : Level} {n k : ℕ} (BG : BGroup ℓ n k) → basetype BG
basepoint BG = pt (BGroup.base BG)

baseΣ : {ℓ : Level} {n k : ℕ} (BG : BGroupΣ {ℓ} n k) → Σ[ A ∈ Type ℓ ] A
baseΣ (base , * , _ , _) = (base , *)

-- special cases
1BGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
1BGroup ℓ = BGroup ℓ 0 1

1BGroupΣ : {ℓ : Level} → Type (ℓ-suc ℓ)
1BGroupΣ {ℓ} = BGroupΣ {ℓ} 0 1

-- first fundamental group of 1BGroups
π₁-1BGroup : {ℓ : Level} (BG : 1BGroup ℓ) → Group {ℓ}
π₁-1BGroup BG =
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

π₁-1BGroupΣ : {ℓ : Level} (BG : BGroupΣ {ℓ} 0 1) → Group {ℓ}
π₁-1BGroupΣ (BG , pt , conn , trunc) = π₁-1BGroup (bgroup (BG , pt) conn trunc)

-- coercions
Group→1BGroup : (G : Group {ℓ}) → 1BGroup ℓ
BGroup.base (Group→1BGroup G) .fst = EM₁ G
BGroup.base (Group→1BGroup G) .snd = embase
BGroup.isConn (Group→1BGroup G) = EM₁Connected G
BGroup.isTrun (Group→1BGroup G) = EM₁Groupoid G

-- functoriality of π₁ on 1BGroups
module _ (BG : 1BGroup ℓ) (BH : 1BGroup ℓ') where
  private
    π₁BG = π₁-1BGroup BG
    π₁BH = π₁-1BGroup BH

  π₁-1BGroup-functor : BGroupHom BG BH → GroupHom π₁BG π₁BH
  GroupHom.fun (π₁-1BGroup-functor f) g = sym (snd f) ∙∙ cong (fst f) g ∙∙ snd f
  GroupHom.isHom (π₁-1BGroup-functor f) g g' = q
    where
      f₁ = fst f
      f₂ = snd f
      f₂- = sym (snd f)
      abstract
        q = (f₂- ∙∙ cong f₁ (g ∙ g') ∙∙ f₂)
                 ≡⟨ doubleCompPath-elim' f₂- (cong f₁ (g ∙ g')) f₂ ⟩
            f₂- ∙ cong f₁ (g ∙ g') ∙ f₂
              ≡⟨ cong (λ z → (f₂- ∙ z ∙ f₂))
                      (congFunct f₁ g g') ⟩
            f₂- ∙ (cong f₁ g ∙ cong f₁ g') ∙ f₂
              ≡⟨ cong (λ z → (f₂- ∙ (cong f₁ g ∙ z) ∙ f₂))
                      (lUnit (cong f₁ g')) ⟩
            f₂- ∙ (cong f₁ g ∙ refl ∙ cong f₁ g') ∙ f₂
              ≡⟨ cong (λ z → (f₂- ∙ (cong f₁ g ∙ z ∙ cong f₁ g') ∙ f₂))
                      (sym (rCancel f₂)) ⟩
            f₂- ∙ (cong f₁ g ∙ (f₂ ∙ f₂-) ∙ cong f₁ g') ∙ f₂
              ≡⟨ cong (λ z → (f₂- ∙ (cong f₁ g ∙ z) ∙ f₂))
                      (sym (assoc _ _ _)) ⟩
            f₂- ∙ (cong f₁ g ∙ (f₂ ∙ (f₂- ∙ cong f₁ g'))) ∙ f₂
              ≡⟨ cong (λ z → (f₂- ∙ z ∙ f₂))
                      (assoc _ _ _) ⟩
            (f₂- ∙ ((cong f₁ g ∙ f₂) ∙ (f₂- ∙ cong f₁ g')) ∙ f₂)
              ≡⟨ cong (f₂- ∙_)
                      (sym (assoc _ _ _)) ⟩
            (f₂- ∙ ((cong f₁ g ∙ f₂) ∙ ((f₂- ∙ cong f₁ g') ∙ f₂)))
              ≡⟨ cong (λ z → (f₂- ∙ ((cong f₁ g ∙ f₂) ∙ z)))
                      (sym (assoc _ _ _)) ⟩
            (f₂- ∙ ((cong f₁ g ∙ f₂) ∙ (f₂- ∙ cong f₁ g' ∙ f₂)))
              ≡⟨ assoc _ _ _ ⟩
            (f₂- ∙ cong f₁ g ∙ f₂) ∙ (f₂- ∙ cong f₁ g' ∙ f₂)
              ≡⟨ cong (_∙ (f₂- ∙ cong f₁ g' ∙ f₂))
                      (sym (doubleCompPath-elim' f₂- (cong f₁ g) f₂)) ⟩
            (f₂- ∙∙ cong f₁ g ∙∙ f₂) ∙ (f₂- ∙ cong f₁ g' ∙ f₂)
              ≡⟨ cong ((f₂- ∙∙ cong f₁ g ∙∙ f₂) ∙_)
                      (sym (doubleCompPath-elim' f₂- (cong f₁ g') f₂)) ⟩
            (f₂- ∙∙ cong f₁ g ∙∙ f₂) ∙ (f₂- ∙∙ cong f₁ g' ∙∙ f₂) ∎


-- π₁ is a left inverse to EM₁
π₁EM₁≃inv : (G : Group {ℓ}) → GroupEquiv G (π₁-1BGroup (Group→1BGroup G))
GroupEquiv.eq (π₁EM₁≃inv G) = isoToEquiv (invIso (ΩEM₁Iso G))
GroupEquiv.isHom (π₁EM₁≃inv G) g g' = emloop-comp G g g'

π₁EM₁≃ : (G : Group {ℓ}) → GroupEquiv (π₁-1BGroup (Group→1BGroup G)) G
π₁EM₁≃ G = invGroupEquiv (π₁EM₁≃inv G)


-- the functorial action of EM₁ on groups
-- is a left inverse to the functorial action of π₁
-- on 1BGroups.
module _ (H : Group {ℓ}) (BG : 1BGroup ℓ') where
  private
    EM₁H = Group→1BGroup H
    π₁EM₁H = π₁-1BGroup EM₁H
    π₁BG = π₁-1BGroup BG

  -- from the EM construction it follows
  -- that there is a homomorphism H → π₁ (EM₁ H)
  H→π₁EM₁H : GroupHom H π₁EM₁H
  H→π₁EM₁H = GroupEquiv.hom (π₁EM₁≃inv H)

  -- the promised functorial left inverse
  -- split up into the three components:
  -- function, is equivalence and pointedness.
  -- pointedness component is trivial

  -- on the object level
  EM₁-functor-lInv-function : GroupHom π₁EM₁H π₁BG → basetype EM₁H → basetype BG
  EM₁-functor-lInv-function f =
    rec' H
        (BGroup.isTrun BG)
        (basepoint BG)
        (GroupHom.fun (compGroupHom H→π₁EM₁H f))
        λ g h → sym (GroupHom.isHom (compGroupHom H→π₁EM₁H f) g h)

  EM₁-functor-lInv-pointed : (f : GroupHom π₁EM₁H π₁BG)
                             → EM₁-functor-lInv-function f (basepoint EM₁H) ≡ basepoint BG
  EM₁-functor-lInv-pointed f = refl

  -- produces an equivalence proof when given a group iso
  EM₁-functor-lInv-onIso-isEquiv : (f : GroupEquiv π₁EM₁H π₁BG)
                                 → isEquiv (EM₁-functor-lInv-function (GroupEquiv.hom f))
  EM₁-functor-lInv-onIso-isEquiv f =
    isEmbedding×isSurjection→isEquiv (isEmbedding-φ , isSurjection-φ)
    where
      φ₁ : basetype EM₁H → basetype BG
      φ₁ = EM₁-functor-lInv-function (GroupEquiv.hom f)
      abstract
        isEmbedding-φ : isEmbedding φ₁
        isEmbedding-φ = reduceToBp isEmbPt
          where
            isEmb : (x y : basetype EM₁H) → Type (ℓ-max ℓ ℓ')
            isEmb x y = isEquiv (cong {x = x} {y = y} φ₁)

            isPropIsEmb : (x y : basetype EM₁H) → isProp (isEmb x y)
            isPropIsEmb x y = isPropIsEquiv (cong {x = x} {y = y} φ₁)

            f-equiv : (basepoint EM₁H ≡ basepoint EM₁H) ≃ (basepoint BG ≡ basepoint BG)
            f-equiv =  GroupEquiv.eq f
            f₁ = fst f-equiv

            γ : ⟨ H ⟩ ≃ ⟨ π₁EM₁H ⟩
            γ = GroupEquiv.eq (π₁EM₁≃inv H)
            β : ⟨ π₁EM₁H ⟩ ≃ typ (carrier BG)
            β = f-equiv
            δ : ⟨ H ⟩ ≃ typ (carrier BG)
            δ = compEquiv γ β
            p : equivFun δ ≡ (λ h → cong φ₁ (equivFun γ h))
            p = refl
            η = (λ (h : ⟨ H ⟩) → cong φ₁ (equivFun γ h))
            isEquiv-η : isEquiv η
            isEquiv-η = equivFun≡→isEquiv δ η λ _ → refl
            congφ∼f : (h : ⟨ H ⟩) → f₁ (GroupHom.fun H→π₁EM₁H h) ≡ cong φ₁ (GroupHom.fun H→π₁EM₁H h)
            congφ∼f p = refl

            isEmbPt : isEmb (basepoint EM₁H) (basepoint EM₁H)
            isEmbPt = equivCompLCancel γ (cong φ₁) isEquiv-η

            g : Unit → basetype EM₁H
            g _ = basepoint EM₁H

            isConn-g : isConnectedFun 1 g
            isConn-g = isConnectedPoint 1 (BGroup.isConn EM₁H) (basepoint EM₁H)

            reduceToBp1 : ((a : Unit) → isEmb (basepoint EM₁H) (g a))
                         → (h' : basetype EM₁H) → isEmb (basepoint EM₁H) h'
            reduceToBp1 =
              Iso.inv (elim.isIsoPrecompose g
                                            1
                                            (λ h' → (isEmb (basepoint EM₁H) h') , isPropIsEmb (basepoint EM₁H) h')
                                            isConn-g)
            reduceToBp1' : isEmb (basepoint EM₁H) (basepoint EM₁H)
                         → (h' : basetype EM₁H) → isEmb (basepoint EM₁H) h'
            reduceToBp1' p = reduceToBp1 λ _ → p


            reduceToBp2 : (h' : basetype EM₁H) → isEmb (basepoint EM₁H) h'
                          → ((a : Unit) → isEmb (g a) h') → (h : basetype EM₁H) → isEmb h h'
            reduceToBp2 h' p =
              Iso.inv (elim.isIsoPrecompose g
                                            1
                                            (λ h → (isEmb h h') , (isPropIsEmb h h'))
                                            isConn-g)
            reduceToBp2' : ((h' : basetype EM₁H) → isEmb (basepoint EM₁H) h')
                           → (h h' : basetype EM₁H) → isEmb h h'
            reduceToBp2' Q h h' = reduceToBp2 h' (Q h') (λ _ → Q h') h


            reduceToBp : isEmb (basepoint EM₁H) (basepoint EM₁H) → (h h' : basetype EM₁H) → isEmb h h'
            reduceToBp p = reduceToBp2' (reduceToBp1' p)

        isSurjection-φ : isSurjection φ₁
        isSurjection-φ g = propTruncΣ← (λ x → φ₁ x ≡ g) ∣ basepoint EM₁H , fst r ∣
          where
            r : isContr ∥ φ₁ (basepoint EM₁H) ≡ g ∥
            r = isContrRespectEquiv (invEquiv propTrunc≃Trunc1)
                                    (isConnectedPath 1
                                                     (BGroup.isConn BG)
                                                     (φ₁ (basepoint EM₁H))
                                                     g)
