{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

module Cubical.Data.W where

private
  variable
    ℓX ℓS ℓP : Level

data W {X : Type ℓX} (S : Type ℓS) (P : S → Type ℓP) (outX : S → X) (inX : ∀ s → P s → X) : X → Type (ℓ-max ℓX (ℓ-max ℓS ℓP)) where
  node : (s : S) → (subtree : (p : P s) → W S P outX inX (inX s p)) → W S P outX inX (outX s)
  
module _ {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where
  getShape : ∀ {x} → W S P outX inX x → S
  getShape (node s subtree) = s

  getSubtree : ∀ {x} → (w : W S P outX inX x) → (p : P (getShape w)) → W S P outX inX (inX _ p)
  getSubtree (node s subtree) = subtree

  outShape : ∀ {x} → (w : W S P outX inX x) → (outX (getShape w) ≡ x)
  outShape (node s subtree) = refl

module WPath {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where
  -- inspired by https://github.com/jashug/IWTypes

  Cover : ∀ {x} → (w w' : W S P outX inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Cover {x} w w' = W
    {X = Σ[ y ∈ X ] W S P outX inX y × W S P outX inX y}
    (Σ[ s ∈ S ] ((p : P s) → W S P outX inX (inX s p)) × ((p : P s) → W S P outX inX (inX s p)))
    (λ (s , subtree , subtree') → P s)
    (λ (s , subtree , subtree') → (outX s) , node s subtree , node s subtree')
    (λ (s , subtree , subtree') p → inX s p , subtree p , subtree' p)
    (x , w , w')

  reflCode : ∀ {x} → (w : W S P outX inX x) → Cover w w
  reflCode (node s subtree) = node (s , subtree , subtree) (λ p → reflCode (subtree p))

  encode : ∀ {x} → (w w' : W S P outX inX x) → w ≡ w' → Cover w w'
  encode w _ = J (λ w' pw → Cover w w') (reflCode w)

  encodeRefl : ∀ {x} → (w : W S P outX inX x) → encode w w refl ≡ reflCode w
  encodeRefl w = JRefl (λ w' pw → Cover w w') (reflCode w)

  decode : ∀ {x} → (w w' : W S P outX inX x) → Cover w w' → w ≡ w'
  decode .(node s subtree) .(node s subtree') (node (s , subtree , subtree') csubtree) i =
    node s λ p → decode (subtree p) (subtree' p) (csubtree p) i

  decodeRefl : ∀ {x} → (w : W S P outX inX x) → decode w w (reflCode w) ≡ refl
  decodeRefl (node s subtree) j i = node s λ p → decodeRefl (subtree p) j i

  decodeEncode : ∀ {x} → (w w' : W S P outX inX x) → (pw : w ≡ w') → decode w w' (encode w w' pw) ≡ pw
  decodeEncode w _ = J (λ w' pw → decode w w' (encode w w' pw) ≡ pw)
    (
      decode w w (encode w w refl)
        ≡⟨ cong (decode w w) (encodeRefl w) ⟩
      decode w w (reflCode w)
        ≡⟨ decodeRefl w ⟩
      refl ∎
    )
  
module _ {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where

  private
    wExt : ∀ x x' → (px : x ≡ x') → (w : W S P outX inX x) → (w' : W S P outX inX x')
      → (ps : getShape w ≡ getShape w')
      → (ppx : PathP (λ j → outShape w j ≡ outShape w' j) (cong outX ps) px)
      → PathP (λ i → (p : P (ps i)) → W S P outX inX (inX _ p)) (getSubtree w) (getSubtree w')
      → PathP (λ i → W S P outX inX (px i)) w w'
    wExt .(outX s) .(outX s') px (node s subtree) (node s' subtree') ps ppx psubtree i =
      transp (λ j → W S P outX inX (ppx j i)) (i ∨ ~ i) (node (ps i) (psubtree i))

  isOfHLevelSuc-W : ∀ (n : HLevel) (isHS : ∀ x → isOfHLevel (suc n) (fiber outX x))
    → ∀ x → isOfHLevel (suc n) (W S P outX inX x)
  isOfHLevelSuc-W zero isHS x w w' = wExt x x refl w w'
    (cong fst (isHS x (getShape w , outShape w) (getShape w' , outShape w')))
    {!!} -- use snd of the fiber
    {!!} -- PathP from Path, then recursion
  isOfHLevelSuc-W (suc n) isHS x = {!!}
    -- by induction on n
