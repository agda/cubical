{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Everything

module Cubical.Data.W where

private
  variable
    ℓI ℓS ℓP : Level

data W {I : Type ℓI} (S : I → Type ℓS) (P : ∀ i → S i → Type ℓP) (ℑ : ∀ i (s : S i) → P i s → I) :
  (i : I) → Type (ℓ-max ℓI (ℓ-max ℓS ℓP)) where
  node : ∀ {i} → (s : S i) → (subtrees : (p : P i s) → W S P ℑ (ℑ i s p)) → W S P ℑ i

module WPath {I : Type ℓI} (S : I → Type ℓS) (P : ∀ i → S i → Type ℓP) (ℑ : ∀ i (s : S i) → P i s → I) where
  private
    variable
      i i' j : I

  Cover : i ≡ i' → W S P ℑ i → W S P ℑ i' → Type (ℓ-max (ℓ-max ℓI ℓS) ℓP)
  Cover pi (node s subtrees) (node s' subtrees') =
    Σ[ ps ∈ PathP (λ α → S (pi α)) s s' ]
      ∀ p p' → (pp : PathP (λ α → P (pi α) (ps α)) p p') → Cover (λ α → ℑ (pi α) (ps α) (pp α)) (subtrees p) (subtrees' p')

  reflCode : (w : W S P ℑ i) → Cover refl w w
  reflCode (node s subtrees) = (λ α → s) , λ p p' pp → {!!}
  --(λ α → subtrees)

{-
  encode : (pi : i ≡ i') → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w'
  encode {i = i} {i' = _} =
              J (λ i' pi → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w')
              (λ w _ → J (λ w' pw → Cover refl w w') (reflCode w))

  encodeRefl : ∀ {i} (w : W S P ℑ i) → encode refl w w refl ≡ reflCode w
  encodeRefl {i} w =
    encode refl w w refl
      ≡⟨ funExt⁻ (funExt⁻ (funExt⁻ (JRefl
        (λ i' pi → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w')
        λ w _ → J (λ w' pw → Cover refl w w') (reflCode w)
      ) w) w) refl ⟩
    J (λ w' pw → Cover refl w w') (reflCode w) {w} refl
      ≡⟨ JRefl (λ w' pw → Cover refl w w') (reflCode w) ⟩
    reflCode w ∎

  decode : (pi : i ≡ i') → ∀ w w' → Cover pi w w' → PathP (λ α → W S P ℑ (pi α)) w w'
  decode pi (node s subtrees) (node s' subtrees') (ps , psubtrees) α = node (ps α) (psubtrees α)

  decodeRefl : ∀ {i} (w : W S P ℑ i) → decode refl w w (reflCode w) ≡ refl
  decodeRefl (node s subtrees) = refl

  decodeEncode : (pi : i ≡ i') → ∀ w w' → (pw : PathP (λ α → W S P ℑ (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw
  decodeEncode {i = i} {i' = _} =
                    J (λ i' pi → ∀ w w' → (pw : PathP (λ α → W S P ℑ (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw)
                    λ w _ → J (λ w' pw → decode refl w w' (encode refl w w' pw) ≡ pw) (
                      decode refl w w (encode refl w w refl)
                        ≡⟨ cong (decode refl w w) (encodeRefl w) ⟩
                      decode refl w w (reflCode w)
                        ≡⟨ decodeRefl w ⟩
                      refl ∎
                    )
-}
