{-
  Spaces of functions ; Numbered definitions and lemmas are from
  Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
module Cubical.Relation.Premetric.Instances.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.Instances.Rationals

open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Instances.SubSpace
open import Cubical.Relation.Premetric.Mappings

open OrderedFieldTheory    ℚOrderedField
open OrderedFieldReasoning ℚOrderedField
open 1/2∈ℚ
open PremetricStr
open PremetricTheory
open SubSpace

private
  variable
    ℓA ℓM ℓM' ℓN ℓN' ℓX ℓX' : Level

module FunctionSpace (A : Type ℓA) (N : PremetricSpace ℓN ℓN') where
  private module N = PremetricStr (snd N)

  open IsPremetric

  infix 5 _≈→[_]_

  -- Definition 2.14
  _≈→[_]_ : (A → ⟨ N ⟩) → ℚ₊ → (A → ⟨ N ⟩) → Type (ℓ-max ℓA ℓN')
  f ≈→[ ε ] g = ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x N.≈[ δ ] g x)

  -- Lemma 2.15
  ≈→→pointwise : ∀ f g ε → f ≈→[ ε ] g → ∀ x → f x N.≈[ ε ] g x
  ≈→→pointwise f g ε =
    PT.rec (isPropΠ λ x → N.isProp≈ (f x) (g x) ε)
    λ (δ , δ<ε , pw) x → isMonotone≈< N δ<ε (pw x)

  -- Theorem 2.16 (first part)
  isPremetric→ : IsPremetric _≈→[_]_
  isPremetric→ .is-set  = isSet→ N.is-set
  isPremetric→ .isProp≈ = λ _ _ _ → squash₁
  isPremetric→ .isRefl≈ = λ f ε →
    ∣ ε /2₊ , /2₊<id ε , (λ x → N.isRefl≈ (f x) (ε /2₊)) ∣₁
  isPremetric→ .isSym≈  = λ f g ε →
    PT.map λ (δ , δ<ε , pw) → (δ , δ<ε , λ x → N.isSym≈ (f x) (g x) δ (pw x))
  isPremetric→ .isSeparated≈ = λ f g f≈g →
    funExt λ x → N.isSeparated≈ (f x) (g x) λ ε → ≈→→pointwise f g ε (f≈g ε) x
  isPremetric→ .isTriangular≈ = λ f g h ε θ f≈g g≈h → do
    (δ₁ , δ₁<ε , fg) ← f≈g
    (δ₂ , δ₂<θ , gh) ← g≈h
    return
      ( δ₁ +₊ δ₂
      , +Mono< _ _ _ _ δ₁<ε δ₂<θ
      , λ x → N.isTriangular≈ _ _ _ _ _ (fg x) (gh x))
  isPremetric→ .isRounded≈ = λ f g ε f≈g → do
    (δ , δ<ε , pw) ← f≈g
    return
      (  mean₊ δ ε
      , <→mean< ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε
      , ∣ δ , <→<mean ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε , pw ∣₁)

  →PremetricSpace : PremetricSpace (ℓ-max ℓA ℓN) (ℓ-max ℓA ℓN')
  fst →PremetricSpace = A → ⟨ N ⟩
  _≈[_]_      (snd →PremetricSpace) = _≈→[_]_
  isPremetric (snd →PremetricSpace) = isPremetric→

  isCauchy→isPointwiseCauchy : ∀ s → isCauchy →PremetricSpace s
                             → ∀ x → isCauchy N (λ ε → s ε x)
  isCauchy→isPointwiseCauchy s sc x ε δ = ≈→→pointwise (s ε) (s δ) (ε +₊ δ) (sc ε δ) x

  -- Theorem 2.16 (second part)
  isComplete→ : isComplete N → isComplete →PremetricSpace
  fst (isComplete→ N-com s sc) = λ x → fst (N-com _ (isCauchy→isPointwiseCauchy s sc x))
  snd (isComplete→ N-com s sc) = λ ε θ →
    ∣ ε +₊ θ /2₊
    , +MonoL< _ _ ⟨ ε ⟩₊ (/2₊<id θ)
    , (λ x → snd (N-com _ (isCauchy→isPointwiseCauchy s sc x)) ε (θ /2₊)) ∣₁

-- Shorter notation
_→PrSp_ : Type ℓA → PremetricSpace ℓN ℓN' → PremetricSpace (ℓ-max ℓA ℓN) (ℓ-max ℓA ℓN')
A →PrSp N = FunctionSpace.→PremetricSpace A N

module _ (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') where
  private
    module M = PremetricStr (snd M)
    module N = PremetricStr (snd N)
    module M→N = FunctionSpace ⟨ M ⟩ N

  open IsNonExpansive
  open IsLipschitzWith

  Isometry[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  Isometry[_,_]PrSpace = ⊆PremetricSpace (⟨ M ⟩ →PrSp N)
    (λ f → IsIsometry (snd M) f (snd N))
    (λ f → isPropIsIsometry (snd M) f (snd N))

  NE[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  NE[_,_]PrSpace = ⊆PremetricSpace (⟨ M ⟩ →PrSp N)
    (λ f → IsNonExpansive (snd M) f (snd N))
    (λ f → isPropIsNonExpansive (snd M) f (snd N))

  C[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  C[_,_]PrSpace = ⊆PremetricSpace (⟨ M ⟩ →PrSp N)
    (λ f → isContinuous (snd M) f (snd N))
    (λ f → isPropIsContinuous (snd M) f (snd N))

  UC[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  UC[_,_]PrSpace = ⊆PremetricSpace (⟨ M ⟩ →PrSp N)
    (λ f → IsUContinuous (snd M) f (snd N))
    (λ f → isPropIsUContinuous (snd M) f (snd N))

  L[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  L[_,_]PrSpace = ⊆PremetricSpace (⟨ M ⟩ →PrSp N)
    (λ f → isLipschitz (snd M) f (snd N))
    (λ f → isPropIsLipschitz (snd M) f (snd N))

  module _ (N-com : isComplete N) where

    limNE : ∀ s sc → (∀ ε → IsNonExpansive (snd M) (s ε) (snd N))
          → IsNonExpansive (snd M) (fst (M→N.isComplete→ N-com s sc)) (snd N)
    pres≈ (limNE s sc s-ne) x y ε x≈y = let
        l , l-lim = M→N.isComplete→ N-com s sc
        s⟶l : ∀ z → isLimit N (λ ε → s ε z) (l z)
        s⟶l z ε θ = M→N.≈→→pointwise (s ε) l (ε +₊ θ) (l-lim ε θ) z
      in
        proof l x N.≈[ ε ] l y , N.isProp≈ (l x) (l y) ε by
      do
        ((δ , Δ) , δ+Δ≡ε , x≈[δ]y) ← isRounded≈Gap M ε x≈y
        let
          Δ/2+Δ/2+δ≡ε : ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ δ) ⟩₊ ≡ ⟨ ε ⟩₊
          Δ/2+Δ/2+δ≡ε =
            ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ δ) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ Δ /2₊ ⟩₊ _ _ ⟩
            ⟨ (Δ /2₊ +₊ Δ /2₊) +₊ δ ⟩₊ ≡⟨ cong (ℚ._+ _) (/2+/2≡id ⟨ Δ ⟩₊) ⟩
            ⟨ Δ +₊ δ ⟩₊                ≡⟨ ℚ.+Comm ⟨ Δ ⟩₊ ⟨ δ ⟩₊ ∙ δ+Δ≡ε ⟩
            ⟨ ε ⟩₊                     ∎

        return
          (subst≈ N _ _ Δ/2+Δ/2+δ≡ε $
            isLim≈+₂ N _ _ (l x) (l y) δ (Δ /2₊) (Δ /2₊) (s⟶l x) (s⟶l y) $
              pres≈ (s-ne (Δ /2₊)) x y δ x≈[δ]y)

    isCompleteNE : isComplete NE[_,_]PrSpace
    isCompleteNE = SubSpace.lim∈→isComplete
      (⟨ M ⟩ →PrSp N) _ (λ f → isPropIsNonExpansive (snd M) f (snd N))
      (M→N.isComplete→ N-com) λ x xs → limNE (fst ∘ x) xs (snd ∘ x)

  module EquiLipschitz where

    isEquiLipschitzWith : (ℚ₊ → ⟨ M ⟩ → ⟨ N ⟩) → ℚ₊ → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
    isEquiLipschitzWith s L = ∀ ε → IsLipschitzWith (snd M) (s ε) (snd N) L

    isEquiLipschitz : (ℚ₊ → ⟨ M ⟩ → ⟨ N ⟩) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
    isEquiLipschitz s = ∃[ L ∈ ℚ₊ ] isEquiLipschitzWith s L

    EquiL[_,_] : Type (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
    EquiL[_,_] = Σ[ s ∈ (ℚ₊ → ⟨ M ⟩ → ⟨ N ⟩) ] isEquiLipschitz s

    -- Lemma 2.17
    limEquiLipschitzWith : (N-com : isComplete N)
      → ∀ s sc L
      → isEquiLipschitzWith s L
      → IsLipschitzWith (snd M) (fst (M→N.isComplete→ N-com s sc)) (snd N) L
    pres≈ (limEquiLipschitzWith N-com s sc L L-lip) = λ x y ε x≈y →
      let
        l , l-lim = M→N.isComplete→ N-com s sc
      in
        proof l x N.≈[ L ·₊ ε ] l y , N.isProp≈ (l x) (l y) (L ·₊ ε) by
      do
        (δ , δ<ε , x≈[δ]y) ← M.isRounded≈ x y ε x≈y
        let
          Δ = [ (L ·₊ ε) -₊ (L ·₊ δ) ]⟨ [ (fst L) , (snd L) ]·< δ<ε ⟩

          s⟶l : ∀ z → isLimit N (λ ε → s ε z) (l z)
          s⟶l z ε θ = M→N.≈→→pointwise (s ε) l (ε +₊ θ) (l-lim ε θ) z

          Δ/2+Δ/2+Lδ≡Lε : ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ L ·₊ δ) ⟩₊ ≡ ⟨ L ·₊ ε ⟩₊
          Δ/2+Δ/2+Lδ≡Lε =
            ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ L ·₊ δ) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ Δ /2₊ ⟩₊ _ _ ⟩
            ⟨ (Δ /2₊ +₊ Δ /2₊) +₊ L ·₊ δ ⟩₊ ≡⟨ cong (ℚ._+ _) (/2+/2≡id ⟨ Δ ⟩₊) ⟩
            ⟨ Δ +₊ L ·₊ δ ⟩₊                ≡⟨ minusPlus₊ (L ·₊ ε) (L ·₊ δ) ⟩
            ⟨ L ·₊ ε ⟩₊                     ∎

        return
          (subst≈ N (l x) (l y) Δ/2+Δ/2+Lδ≡Lε $
            isLim≈+₂ N _ _ (l x) (l y) (L ·₊ δ) (Δ /2₊) (Δ /2₊) (s⟶l x) (s⟶l y) $
              pres≈ (L-lip (Δ /2₊)) x y δ x≈[δ]y)

    limEquiLipschitz : (N-com : isComplete N)
      → ∀ s → (sc : isCauchy (⟨ M ⟩ →PrSp N) s)
      → isEquiLipschitz s
      → isLipschitz (snd M) (fst (M→N.isComplete→ N-com s sc)) (snd N)
    limEquiLipschitz N-com s sc = PT.map
      (uncurry λ L isELip → L , limEquiLipschitzWith N-com s sc L isELip)

module ∘Properties (X : PremetricSpace ℓX ℓX') where
  module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} where

    open IsIsometry
    open IsNonExpansive
    open IsLipschitzWith
    open IsContinuousAt
    open IsUContinuous

    -- pre-composition with any kind of mappings is nonexpansive :

    -∘ᴵ_ : Isometry[ M , N ] → NE[ Isometry[ N , X ]PrSpace , Isometry[ M , X ]PrSpace ]
    fst (-∘ᴵ f)         = _∘Isometry f
    pres≈ (snd (-∘ᴵ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ⁿ_ : NE[ M , N ] → NE[ NE[ N , X ]PrSpace , NE[ M , X ]PrSpace ]
    fst (-∘ⁿ f)         = _∘NE f
    pres≈ (snd (-∘ⁿ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᴸ_ : L[ M , N ] → NE[ L[ N , X ]PrSpace , L[ M , X ]PrSpace ]
    fst (-∘ᴸ f)         = _∘L f
    pres≈ (snd (-∘ᴸ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᵘᶜ_ : UC[ M , N ] → NE[ UC[ N , X ]PrSpace , UC[ M , X ]PrSpace ]
    fst (-∘ᵘᶜ f)         = _∘UC f
    pres≈ (snd (-∘ᵘᶜ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᶜ_ : C[ M , N ] → NE[ C[ N , X ]PrSpace , C[ M , X ]PrSpace ]
    fst (-∘ᶜ f)         = _∘C f
    pres≈ (snd (-∘ᶜ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -- post-composition with a nonexpansive mappings is nonexpansive :

    _ⁿ∘ⁿ- : NE[ M , N ] → NE[ NE[ X , M ]PrSpace , NE[ X , N ]PrSpace ]
    fst (f ⁿ∘ⁿ-)         = f ∘NE_
    pres≈ (snd (f ⁿ∘ⁿ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᴸ- : NE[ M , N ] → NE[ L[ X , M ]PrSpace , L[ X , N ]PrSpace ]
    fst (f ⁿ∘ᴸ-)         = (NE→L f) ∘L_
    pres≈ (snd (f ⁿ∘ᴸ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᵘᶜ- : NE[ M , N ] → NE[ UC[ X , M ]PrSpace , UC[ X , N ]PrSpace ]
    fst (f ⁿ∘ᵘᶜ-)         = (NE→UC f) ∘UC_
    pres≈ (snd (f ⁿ∘ᵘᶜ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᶜ- : NE[ M , N ] → NE[ C[ X , M ]PrSpace , C[ X , N ]PrSpace ]
    fst (f ⁿ∘ᶜ-)         = (NE→C f) ∘C_
    pres≈ (snd (f ⁿ∘ᶜ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))
