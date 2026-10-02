{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.EM where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

module _ {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') where
  dirPropProjFst : GroupHom (DirProd G H) G
  dirPropProjFst .fst = fst
  dirPropProjFst .snd = makeIsGroupHom λ _ _ → refl

  dirPropProjSnd : GroupHom (DirProd G H) H
  dirPropProjSnd .fst = snd
  dirPropProjSnd .snd = makeIsGroupHom λ _ _ → refl

  dirPropProjInjectFst : GroupHom G (DirProd G H)
  dirPropProjInjectFst .fst x = (x , GroupStr.1g (snd H))
  dirPropProjInjectFst .snd = makeIsGroupHom λ _ _
    → ΣPathP (refl , (sym (GroupStr.·IdR (snd H) (GroupStr.1g (snd H)))))

  dirPropProjInjectSnd : GroupHom H (DirProd G H)
  dirPropProjInjectSnd .fst x = (GroupStr.1g (snd G) , x)
  dirPropProjInjectSnd .snd = makeIsGroupHom λ _ _
    → ΣPathP (sym (GroupStr.·IdR (snd G) (GroupStr.1g (snd G))) , refl)

module _ {ℓ : Level} (H K : AbGroup ℓ) where
  EMProd→ProdEM : (n : ℕ)
    → EM (AbDirProd H K) n
    → (EM H n) × (EM K n)
  EMProd→ProdEM n x .fst =
    inducedFun-EM {G' = AbDirProd H K} {H' = H}
      (dirPropProjFst (AbGroup→Group H) (AbGroup→Group K)) n x
  EMProd→ProdEM n x .snd =
    inducedFun-EM {G' = AbDirProd H K} {H' = K}
      (dirPropProjSnd (AbGroup→Group H) (AbGroup→Group K)) n x

  EMProd→ProdEM∙ : (n : ℕ)
    → EM∙ (AbDirProd H K) n →∙ ((EM∙ H n) ×∙ (EM∙ K n))
  EMProd→ProdEM∙ n .fst = EMProd→ProdEM n
  EMProd→ProdEM∙ n .snd = ΣPathP (inducedFun-EM0ₖ n , inducedFun-EM0ₖ n)

  private
    iso1 : (n : ℕ)
      → Iso (EMProd→ProdEM (suc n) (0ₖ (suc n))
           ≡ EMProd→ProdEM (suc n) (0ₖ (suc n)))
            ((EM H n) × (EM K n))
    iso1 zero = compIso (invIso ΣPathIsoPathΣ)
      (prodIso (invIso (Iso-EM-ΩEM+1 {G = H} zero))
               (invIso (Iso-EM-ΩEM+1 {G = K} zero)))
    iso1 (suc n) =
      compIso (invIso ΣPathIsoPathΣ)
      (prodIso (invIso (Iso-EM-ΩEM+1 {G = H} (suc n)))
               (invIso (Iso-EM-ΩEM+1 {G = K} (suc n))))

    lem : (n : ℕ) (x : _)
       → (cong (EMProd→ProdEM (suc n)) (Iso.fun (Iso-EM-ΩEM+1 n) x))
         ≡ (Iso.inv (iso1 n) (EMProd→ProdEM n x))
    lem zero x = cong ΣPathP (ΣPathP
       ((sym (EMFun-EM→ΩEM+1 {G = AbDirProd H K} {H = H}
                {dirPropProjFst (AbGroup→Group H) (AbGroup→Group K)} zero x))
      , sym (EMFun-EM→ΩEM+1 {G = AbDirProd H K} {H = K}
                {dirPropProjSnd (AbGroup→Group H) (AbGroup→Group K)} zero x)))
    lem (suc n) x = cong ΣPathP (ΣPathP
       ((sym (EMFun-EM→ΩEM+1 {G = AbDirProd H K} {H = H}
                {dirPropProjFst (AbGroup→Group H) (AbGroup→Group K)} (suc n) x))
      , sym (EMFun-EM→ΩEM+1 {G = AbDirProd H K} {H = K}
                {dirPropProjSnd (AbGroup→Group H) (AbGroup→Group K)} (suc n) x)))

    lem2 : (n : ℕ)
      → Path (fst (Ω (EM∙ (AbDirProd H K) (suc n)))
           → EMProd→ProdEM (suc n) (0ₖ (suc n)) ≡
              EMProd→ProdEM (suc n) (0ₖ (suc n)))
              (cong (EMProd→ProdEM (suc n)))
              (Iso.inv (iso1 n) ∘ EMProd→ProdEM n ∘ Iso.inv (Iso-EM-ΩEM+1 n))
    lem2 n =
        funExt (λ x → cong (congS (EMProd→ProdEM (suc n)))
                        (sym (Iso.sec (Iso-EM-ΩEM+1 n) x)))
      ∙ cong (_∘ Iso.inv (Iso-EM-ΩEM+1 n)) (funExt (lem n))

  isEquiv-EMProd→ProdEM : (n : ℕ) → isEquiv (EMProd→ProdEM n)
  isEquiv-EMProd→ProdEM zero = idIsEquiv _
  isEquiv-EMProd→ProdEM (suc n) =
    isEmbedding×isSurjection→isEquiv
      (EM→Prop _ n (λ _ → isPropΠ λ _ → isPropIsEquiv _)
        (EM→Prop _ n (λ _ → isPropIsEquiv _)
          (subst isEquiv (sym (lem2 n))
            (compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 n)))
              (compEquiv (_ , (isEquiv-EMProd→ProdEM n))
                (isoToEquiv (invIso (iso1 n)))) .snd)))
     , uncurry (EM→Prop _ n (λ _ → isPropΠ λ _ → squash₁)
               (EM→Prop _ n (λ _ → squash₁)
               ∣ (0ₖ (suc n)) , EMProd→ProdEM∙ (suc n) .snd ∣₁)))

  ProdEM→EMProd : (n : ℕ)
    → (EM H n) × (EM K n)
    → EM (AbDirProd H K) n
  ProdEM→EMProd n (x , y) =
      (inducedFun-EM {G' = H} {H' = AbDirProd H K}
        (dirPropProjInjectFst (AbGroup→Group H) (AbGroup→Group K)) n x)
    +[ n ]ₖ
      (inducedFun-EM {G' = K} {H' = AbDirProd H K}
         (dirPropProjInjectSnd (AbGroup→Group H) (AbGroup→Group K)) n y)

EMDirProdEquiv : {ℓ : Level} (H K : AbGroup ℓ) (n : ℕ)
  → EM (AbDirProd H K) n ≃ (EM H n) × (EM K n)
EMDirProdEquiv H K n .fst = EMProd→ProdEM H K n
EMDirProdEquiv H K n .snd = isEquiv-EMProd→ProdEM H K n
