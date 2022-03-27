{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

module Cubical.Data.W where

open _≅_

private
  variable
    ℓX ℓS ℓP : Level

module Types {X : Type ℓX} (S : X → Type ℓS) (P : ∀ x → S x → Type ℓP) (inX : ∀ x (s : S x) → P x s → X) where
  data W : (x : X) → Type (ℓ-max ℓX (ℓ-max ℓS ℓP)) where
    node : ∀ {x} → (s : S x) → (subtree : (p : P x s) → W (inX x s p)) → W x

  Subtree : ∀ {x} → (s : S x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Subtree {x} s = (p : P x s) → W (inX x s p)

  RepW : (x : X) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  RepW x = Σ[ s ∈ S x ] Subtree s

open Types public

module _ {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} where

  getShape : ∀ {x} → W S P inX x → S x
  getShape (node s subtree) = s

  getSubtree : ∀ {x} → (w : W S P inX x) → (p : P x (getShape w)) → W S P inX (inX x (getShape w) p)
  getSubtree (node s subtree) = subtree

  wExt : ∀ {x} (w w' : W S P inX x)
    → (ps : getShape w ≡ getShape w')
    → (pw : PathP (λ i → Subtree S P inX (ps i)) (getSubtree w) (getSubtree w'))
    → w ≡ w'
  wExt (node s subtree) (node s' subtree') ps psubtree = cong₂ node ps psubtree

  isoRepW : (x : X) → W S P inX x ≅ RepW S P inX x
  fun (isoRepW x) (node s subtree) = s , subtree
  inv (isoRepW x) (s , subtree) = node s subtree
  rightInv (isoRepW x) (s , subtree) = refl
  leftInv (isoRepW x) (node s subtree) = refl

  equivRepW : (x : X) → W S P inX x ≃ RepW S P inX x
  equivRepW x = isoToEquiv (isoRepW x)

  pathRepW : (x : X) → W S P inX x ≡ RepW S P inX x
  pathRepW x = ua (equivRepW x)

  isPropW : (∀ x → isProp (S x)) → ∀ x → isProp (W S P inX x)
  isPropW isPropS x (node s subtree) (node s' subtree') =
    cong₂ node (isPropS x s s') (toPathP (funExt λ p → isPropW isPropS _ _ (subtree' p)))

{-
  isOfHLevelSuc-W : (n : HLevel) → (∀ x → isOfHLevel (suc n) (S x)) → ∀ x → isOfHLevel (suc n) (W S P inX x)
  isOfHLevelSuc-W zero isHS x = isPropW isHS x
  isOfHLevelSuc-W (suc n) isHS x = subst (isOfHLevel (2 + n)) (sym (pathRepW x))
    λ rw@(s , subtree) rw'@(s' , subtree') → subst (isOfHLevel (suc n)) (ΣPathTransport≡PathΣ rw rw') {!This doesn't help.!}
-}

module WPathTypes {X : Type ℓX} (S : X → Type ℓS) (P : ∀ x → S x → Type ℓP) (inX : ∀ x (s : S x) → P x s → X) where

  --somewhat inspired by https://github.com/jashug/IWTypes , but different.

  IndexCover : Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  IndexCover = Σ[ x ∈ X ] W S P inX x × W S P inX x

  ShapeCover : IndexCover → Type ℓS
  ShapeCover (x , w , w') = getShape w ≡ getShape w'

  ArityCover : ∀ xww' → ShapeCover xww' → Type ℓP
  ArityCover (x , w , w') ps = P x (getShape w')

  inXCover : ∀ xww' → (ps : ShapeCover xww') → ArityCover xww' ps → IndexCover
  inXCover (x , w , w') ps p = (inX x (getShape w') p) , (subst (Subtree S P inX) ps (getSubtree w) p , getSubtree w' p)

  Cover : ∀ {x : X} → (w w' : W S P inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Cover {x} w w' = W ShapeCover ArityCover inXCover (x , w , w')

module WPath {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} where
  open WPathTypes S P inX

  --reflCode : ∀ {x} (w : W S P inX x) → Cover w w
  --reflCode (node s subtree) = node refl (λ p → {!!})

  isoEncode : ∀ {x} (w w' : W S P inX x) → (w ≡ w') ≅ Cover w w'
  isoEncodeSubtree : ∀ {x} (w w' : W S P inX x) (ps : ShapeCover (x , w , w'))
    → (PathP (λ i → Subtree S P inX (ps i)) (getSubtree w) (getSubtree w'))
       ≅
       (∀ (p : P x (getShape w')) → W ShapeCover ArityCover inXCover (inXCover (x , w , w') ps p))

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

  encode : ∀ {x} (w w' : W S P inX x) → w ≡ w' → Cover w w'
  encode w w' = fun (isoEncode w w')

  decode : ∀ {x} (w w' : W S P inX x) → Cover w w' → w ≡ w'
  decode w w' = inv (isoEncode w w')

  decodeEncode : ∀ {x} (w w' : W S P inX x) → (pw : w ≡ w') → decode w w' (encode w w' pw) ≡ pw
  decodeEncode w w' = leftInv (isoEncode w w')

  encodeDecode : ∀ {x} (w w' : W S P inX x) → (cw : Cover w w') → encode w w' (decode w w' cw) ≡ cw
  encodeDecode w w' = rightInv (isoEncode w w')
  
  equivEncode : ∀ {x} (w w' : W S P inX x) → (w ≡ w') ≃ Cover w w'
  equivEncode w w' = isoToEquiv (isoEncode w w')

  pathEncode : ∀ {x} (w w' : W S P inX x) → (w ≡ w') ≡ Cover w w'
  pathEncode w w' = ua (equivEncode w w')

open WPathTypes
open WPath

isOfHLevelSuc-W : {X : Type ℓX} {S : X → Type ℓS} {P : ∀ x → S x → Type ℓP} {inX : ∀ x (s : S x) → P x s → X} →
  (n : HLevel) → (∀ x → isOfHLevel (suc n) (S x)) → ∀ x → isOfHLevel (suc n) (W S P inX x)
isOfHLevelSuc-W zero isHS x = isPropW isHS x
isOfHLevelSuc-W (suc n) isHS x w w' =
  subst (isOfHLevel (suc n)) (λ i → pathEncode w w' (~ i))
    (isOfHLevelSuc-W n
      (λ (y , v , v') → isHS y (getShape v) (getShape v'))
      (x , w , w')
    )
