{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

module Cubical.Data.W.Indexed where

open _≅_

private
  variable
    ℓX ℓS ℓP : Level

module Types {X : Type ℓX} (S : X → Type ℓS) (P : ∀ x → S x → Type ℓP) (inX : ∀ x (s : S x) → P x s → X) where
  data IW (x : X) : Type (ℓ-max ℓX (ℓ-max ℓS ℓP)) where
    node : (s : S x) → (subtree : (p : P x s) → IW (inX x s p)) → IW x

  Subtree : ∀ {x} → (s : S x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Subtree {x} s = (p : P x s) → IW (inX x s p)

  RepIW : (x : X) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  RepIW x = Σ[ s ∈ S x ] Subtree s

open Types public

module _ {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} where

  getShape : ∀ {x} → IW S P inX x → S x
  getShape (node s subtree) = s

  getSubtree : ∀ {x} → (w : IW S P inX x) → (p : P x (getShape w)) → IW S P inX (inX x (getShape w) p)
  getSubtree (node s subtree) = subtree

  wExt : ∀ {x} (w w' : IW S P inX x)
    → (ps : getShape w ≡ getShape w')
    → (pw : PathP (λ i → Subtree S P inX (ps i)) (getSubtree w) (getSubtree w'))
    → w ≡ w'
  wExt (node s subtree) (node s' subtree') ps psubtree = cong₂ node ps psubtree

  isoRepIW : (x : X) → IW S P inX x ≅ RepIW S P inX x
  fun (isoRepIW x) (node s subtree) = s , subtree
  inv (isoRepIW x) (s , subtree) = node s subtree
  rightInv (isoRepIW x) (s , subtree) = refl
  leftInv (isoRepIW x) (node s subtree) = refl

  equivRepIW : (x : X) → IW S P inX x ≃ RepIW S P inX x
  equivRepIW x = isoToEquiv (isoRepIW x)

  --pathRepIW : (x : X) → IW S P inX x ≡ RepIW S P inX x
  --pathRepIW x = ua (equivRepIW x)

  isPropIW : (∀ x → isProp (S x)) → ∀ x → isProp (IW S P inX x)
  isPropIW isPropS x (node s subtree) (node s' subtree') =
    cong₂ node (isPropS x s s') (toPathP (funExt λ p → isPropIW isPropS _ _ (subtree' p)))

module IWPathTypes {X : Type ℓX} (S : X → Type ℓS) (P : ∀ x → S x → Type ℓP) (inX : ∀ x (s : S x) → P x s → X) where

  --somewhat inspired by https://github.com/jashug/IWTypes , but different.

  IndexCover : Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  IndexCover = Σ[ x ∈ X ] IW S P inX x × IW S P inX x

  ShapeCover : IndexCover → Type ℓS
  ShapeCover (x , w , w') = getShape w ≡ getShape w'

  ArityCover : ∀ xww' → ShapeCover xww' → Type ℓP
  ArityCover (x , w , w') ps = P x (getShape w')

  inXCover : ∀ xww' → (ps : ShapeCover xww') → ArityCover xww' ps → IndexCover
  inXCover (x , w , w') ps p = (inX x (getShape w') p) , (subst (Subtree S P inX) ps (getSubtree w) p , getSubtree w' p)

  Cover : ∀ {x : X} → (w w' : IW S P inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Cover {x} w w' = IW ShapeCover ArityCover inXCover (x , w , w')

module IWPath {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} where
  open IWPathTypes S P inX

  isoEncode : ∀ {x} (w w' : IW S P inX x) → (w ≡ w') ≅ Cover w w'
  isoEncodeSubtree : ∀ {x} (w w' : IW S P inX x) (ps : ShapeCover (x , w , w'))
    → (PathP (λ i → Subtree S P inX (ps i)) (getSubtree w) (getSubtree w'))
       ≅
       (∀ (p : P x (getShape w')) → IW ShapeCover ArityCover inXCover (inXCover (x , w , w') ps p))

  isoEncodeSubtree w w'@(node s' subtree') ps =
    PathPIsoPath (λ i → Subtree S P inX (ps i)) (getSubtree w) (getSubtree w') ⟫
    invIso (funExtIso) ⟫
    codomainIsoDep (λ p → isoEncode _ (subtree' p))
    where _⟫_ = compIso
          infixr 10 _⟫_
  fun (isoEncode w@(node s subtree) w'@(node s' subtree')) pw =
    node (cong getShape pw) (fun (isoEncodeSubtree w w' (cong getShape pw)) (cong getSubtree pw))
  inv (isoEncode w@(node s subtree) w'@(node s' subtree')) cw@(node ps csubtree) =
    cong₂ node ps (inv (isoEncodeSubtree w w' ps) csubtree)
  rightInv (isoEncode w@(node s subtree) w'@(node s' subtree')) cw@(node ps csubtree) =
    cong (node ps) (
      fun (isoEncodeSubtree w w' ps) (inv (isoEncodeSubtree w w' ps) csubtree)
        ≡⟨ rightInv (isoEncodeSubtree w w' ps) csubtree ⟩
      csubtree ∎
    )
  leftInv (isoEncode w@(node s subtree) w'@(node s' subtree')) pw =
    cong₂ node (cong getShape pw)
      (inv (isoEncodeSubtree w w' (cong getShape pw))
        (fun (isoEncodeSubtree w w' (cong getShape pw))
          (cong getSubtree pw)
        )
      )
      ≡⟨ cong (cong₂ node (cong getShape pw)) (leftInv (isoEncodeSubtree w w' (cong getShape pw)) (cong getSubtree pw)) ⟩
    cong₂ node (cong getShape pw) (cong getSubtree pw)
      ≡⟨ flipSquare (λ i → wExt (node (getShape (pw i)) (getSubtree (pw i))) (pw i) refl refl) ⟩
    pw ∎

  encode : ∀ {x} (w w' : IW S P inX x) → w ≡ w' → Cover w w'
  encode w w' = fun (isoEncode w w')

  decode : ∀ {x} (w w' : IW S P inX x) → Cover w w' → w ≡ w'
  decode w w' = inv (isoEncode w w')

  decodeEncode : ∀ {x} (w w' : IW S P inX x) → (pw : w ≡ w') → decode w w' (encode w w' pw) ≡ pw
  decodeEncode w w' = leftInv (isoEncode w w')

  encodeDecode : ∀ {x} (w w' : IW S P inX x) → (cw : Cover w w') → encode w w' (decode w w' cw) ≡ cw
  encodeDecode w w' = rightInv (isoEncode w w')

  equivEncode : ∀ {x} (w w' : IW S P inX x) → (w ≡ w') ≃ Cover w w'
  equivEncode w w' = isoToEquiv (isoEncode w w')

  --pathEncode : ∀ {x} (w w' : IW S P inX x) → (w ≡ w') ≡ Cover w w'
  --pathEncode w w' = ua (equivEncode w w')

open IWPathTypes
open IWPath

isOfHLevelSuc-IW : {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} →
  (n : HLevel) → (∀ x → isOfHLevel (suc n) (S x)) → ∀ x → isOfHLevel (suc n) (IW S P inX x)
isOfHLevelSuc-IW zero isHS x = isPropIW isHS x
isOfHLevelSuc-IW (suc n) isHS x w w' =
  isOfHLevelRetractFromIso (suc n) (isoEncode w w')
    (isOfHLevelSuc-IW n
      (λ (y , v , v') → isHS y (getShape v) (getShape v'))
      (x , w , w')
    )
