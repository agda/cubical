{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Everything

module Cubical.Data.W where

private
  variable
    ℓI ℓS ℓP : Level

data W {I : Type ℓI} (S : I → Type ℓS) (P : ∀ i → S i → I → Type ℓP) : (i : I) → Type (ℓ-max ℓI (ℓ-max ℓS ℓP)) where
  node : ∀ {i} → (s : S i) → (subtrees : ∀ j → P i s j → W S P j) → W S P i

module WPath {I : Type ℓI} (S : I → Type ℓS) (P : ∀ i → S i → I → Type ℓP) where
  private
    variable
      i i' j : I

  Cover : i ≡ i' → W S P i → W S P i' → Type (ℓ-max (ℓ-max ℓI ℓS) ℓP)
  Cover pi (node s subtrees) (node s' subtrees') =
    Σ[ ps ∈ PathP (λ α → S (pi α)) s s' ] PathP (λ α → ∀ j → P (pi α) (ps α) j → W S P j) subtrees subtrees'

  reflCode : (w : W S P i) → Cover refl w w
  reflCode (node s subtrees) = (λ α → s) , (λ α → subtrees)

  encode : (pi : i ≡ i') → ∀ w w' → PathP (λ α → W S P (pi α)) w w' → Cover pi w w'
  encode {i = i} {i' = _} =
              J (λ i' pi → ∀ w w' → PathP (λ α → W S P (pi α)) w w' → Cover pi w w')
              (λ w _ → J (λ w' pw → Cover refl w w') (reflCode w))

  encodeRefl : ∀ {i} (w : W S P i) → encode refl w w refl ≡ reflCode w
  encodeRefl {i} w =
    encode refl w w refl
      ≡⟨ funExt⁻ (funExt⁻ (funExt⁻ (JRefl
        (λ i' pi → ∀ w w' → PathP (λ α → W S P (pi α)) w w' → Cover pi w w')
        λ w _ → J (λ w' pw → Cover refl w w') (reflCode w)
      ) w) w) refl ⟩
    J (λ w' pw → Cover refl w w') (reflCode w) {w} refl
      ≡⟨ JRefl (λ w' pw → Cover refl w w') (reflCode w) ⟩
    reflCode w ∎

  decode : (pi : i ≡ i') → ∀ w w' → Cover pi w w' → PathP (λ α → W S P (pi α)) w w'
  decode pi (node s subtrees) (node s' subtrees') (ps , psubtrees) α = node (ps α) (psubtrees α)

  decodeRefl : ∀ {i} (w : W S P i) → decode refl w w (reflCode w) ≡ refl
  decodeRefl (node s subtrees) = refl

  decodeEncode : (pi : i ≡ i') → ∀ w w' → (pw : PathP (λ α → W S P (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw
  decodeEncode {i = i} {i' = _} =
                    J (λ i' pi → ∀ w w' → (pw : PathP (λ α → W S P (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw)
                    λ w _ → J (λ w' pw → decode refl w w' (encode refl w w' pw) ≡ pw) (
                      decode refl w w (encode refl w w refl)
                        ≡⟨ cong (decode refl w w) (encodeRefl w) ⟩
                      decode refl w w (reflCode w)
                        ≡⟨ decodeRefl w ⟩
                      refl ∎
                    )
