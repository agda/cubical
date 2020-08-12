{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Strict2Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group

module _ {ℓ ℓ' : Level} where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  module VertCompNotation (𝒢 : ReflGraph ℓ ℓ') where
      G₁ = snd (fst (fst (fst (fst 𝒢))))
      G₀ = fst (fst (fst (fst (fst 𝒢))))
      σ = snd (snd (fst (fst (fst 𝒢))))
      τ = snd (fst 𝒢)
      ι = fst (snd (fst (fst (fst 𝒢))))
      s = GroupHom.fun σ
      t = GroupHom.fun τ
      𝒾 = GroupHom.fun ι
      𝒾s = λ (g : ⟨ G₁ ⟩) → 𝒾 (s g)
      𝒾t = λ (g : ⟨ G₁ ⟩) → 𝒾 (t g)
      split-τ = snd 𝒢
      split-σ = snd (fst (fst 𝒢))

      σι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-σ) g
      τι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-τ) g

      open GroupNotation₁ G₁ public
      open GroupNotation₀ G₀ public
      open GroupHom public

      isComposable : (g f : ⟨ G₁ ⟩) → Type ℓ
      isComposable g f = s g ≡ t f

      isPropIsComposable : (g f : ⟨ G₁ ⟩) → isProp (isComposable g f)
      isPropIsComposable g f c c' = set₀ (s g) (t f) c c'

      -- lemmas
      open MorphismLemmas
      abstract
        σ-g--isg : (g : ⟨ G₁ ⟩) → s (g -₁ 𝒾s g) ≡ 0₀
        σ-g--isg g = s (g -₁ 𝒾s g)
                      ≡⟨ σ .isHom g (-₁ 𝒾s g) ⟩
                    s g +₀ s (-₁ 𝒾s g)
                      ≡⟨ cong (s g +₀_)
                              (mapInv σ (𝒾s g)) ⟩
                    s g -₀ s (𝒾s g)
                      ≡⟨ cong (λ z → s g -₀ z)
                              (σι-≡-fun (s g)) ⟩
                    s g -₀ s g
                      ≡⟨ rCancel₀ (s g) ⟩
                    0₀ ∎

        isComp-g-isg : (g : ⟨ G₁ ⟩) → isComposable g (𝒾s g)
        isComp-g-isg g = sym (τι-≡-fun (s g))


  -- type of composition operations on the reflexive graph 𝒢
  record VertComp (𝒢 : ReflGraph ℓ ℓ') : Type ℓℓ' where
    no-eta-equality
    constructor vertcomp
    open VertCompNotation 𝒢

    field
      vcomp : (g f : ⟨ G₁ ⟩) → (isComposable g f) → ⟨ G₁ ⟩

    syntax vcomp g f p = g ∘⟨ p ⟩ f
    -- infix 9 vcomp

    field
      σ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → s (g ∘⟨ c ⟩ f) ≡ s f
      τ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → t (g ∘⟨ c ⟩ f) ≡ t g
      isHom-∘ : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                {g' f' : ⟨ G₁ ⟩} (c' : isComposable g' f')
                (c'' : isComposable (g +₁ g') (f +₁ f'))
                → (g +₁ g') ∘⟨ c'' ⟩ (f +₁ f') ≡ (g ∘⟨ c ⟩ f) +₁ (g' ∘⟨ c' ⟩ f')
      assoc-∘ : (h g f : ⟨ G₁ ⟩) (c : isComposable h g) (c' : isComposable g f)
                → h ∘⟨ c ∙ sym (τ-∘ g f c') ⟩ (g ∘⟨ c' ⟩ f) ≡ (h ∘⟨ c ⟩ g) ∘⟨ σ-∘ h g c ∙ c' ⟩ f
      lid-∘ : (f : ⟨ G₁ ⟩) (c : isComposable (𝒾 (t f)) f )
              → 𝒾 (t f) ∘⟨ c ⟩ f ≡ f
      rid-∘ : (g : ⟨ G₁ ⟩) (c : isComposable g (𝒾 (s g))) → g ∘⟨ c ⟩ 𝒾 (s g) ≡ g

      -- alternative lid/rid definition, but taking paramter c is more flexible
      -- lid-∘ : (f : ⟨ G₁ ⟩) → 𝒾 (t f) ∘⟨ σι-≡-fun (t f) ⟩ f ≡ f
  module _ (𝒢 : ReflGraph ℓ ℓ') where
    open VertCompNotation 𝒢

    module _ (𝒞 : VertComp 𝒢) where
      open VertComp 𝒞
      open MorphismLemmas
      abstract
        +-c : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
              (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
              → isComposable (g +₁ g') (f +₁ f')
        +-c g f c g' f' c' = σ .isHom g g'
                             ∙∙ cong (_+₀ s g') c
                             ∙∙ cong (t f +₀_) c'
                             ∙ sym (τ .isHom f f')
        ∘-cong-l-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                     {g' : ⟨ G₁ ⟩} (p : g ≡ g')
                     → isComposable g' f
        ∘-cong-l-c c p = cong s (sym p) ∙ c

        ∘-cong-r-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                     {f' : ⟨ G₁ ⟩} (p : f ≡ f')
                     → isComposable g f'
        ∘-cong-r-c c p = c ∙ cong t p

        ∘-cong-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                   {g' f' : ⟨ G₁ ⟩} (p : g ≡ g') (q : f ≡ f')
                     → isComposable g' f'
        ∘-cong-c c p q = ∘-cong-l-c c p ∙ cong t q

        ∘-cong-l : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                   {g' : ⟨ G₁ ⟩} (p : g ≡ g')
                   → g ∘⟨ c ⟩ f ≡ g' ∘⟨ ∘-cong-l-c c p ⟩ f
        ∘-cong-l {g = g} {f = f} c {g'} p = cong₂ (λ h d → h ∘⟨ d ⟩ f)
                                                  p
                                                  (toPathP (isPropIsComposable g'
                                                                               f
                                                                               (transp (λ i → isComposable (p i) f) i0 c)
                                                                               (∘-cong-l-c c p)))

        ∘-cong-r : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                   {f' : ⟨ G₁ ⟩} (p : f ≡ f')
                   → g ∘⟨ c ⟩ f ≡ g ∘⟨ ∘-cong-r-c c p ⟩ f'
        ∘-cong-r {g = g} c {f'} p = cong₂ (λ h d → g ∘⟨ d ⟩ h)
                                     p
                                     (toPathP (isPropIsComposable g
                                                                  f'
                                                                  (transp (λ i → isComposable g (p i)) i0 c)
                                                                  (∘-cong-r-c c p)))

        ∘-cong : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                   {g' f' : ⟨ G₁ ⟩} (p : g ≡ g') (q : f ≡ f')
                   → g ∘⟨ c ⟩ f ≡ g' ∘⟨ ∘-cong-c c p q ⟩ f'
        ∘-cong c p q = ∘-cong-l c p
                       ∙ ∘-cong-r (∘-cong-l-c c p) q

        ∘-lid' : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                 (c' : isComposable (𝒾s g) f)
                 → (𝒾s g) ∘⟨ c' ⟩ f ≡ f
        ∘-lid' {g} {f} c c' = (𝒾s g) ∘⟨ c' ⟩ f
                                  ≡⟨ ∘-cong-l c' (cong 𝒾 c) ⟩
                              𝒾t f ∘⟨ ∘-cong-l-c c' (cong 𝒾 c) ⟩ f
                                  ≡⟨ lid-∘ f (∘-cong-l-c c' (cong 𝒾 c)) ⟩
                              f ∎

        VertComp→+₁ : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
                      → g ∘⟨ c ⟩ f ≡ (g -₁ 𝒾s g) +₁ f
        VertComp→+₁ g f c = g ∘⟨ c ⟩ f
                              ≡⟨ ∘-cong c
                                        (sym (rId₁ g) ∙ cong (g +₁_) (sym (lCancel₁ isg)))
                                        (sym (lId₁ f) ∙ cong (_+₁ f) (sym (rCancel₁ isg))) ⟩
                            (g +₁ (-isg +₁ isg)) ∘⟨ c₁ ⟩ ((isg -₁ isg) +₁ f)
                              ≡⟨ ∘-cong-l c₁ (assoc₁ g -isg isg) ⟩
                            ((g -₁ isg) +₁ isg) ∘⟨ c₂ ⟩ ((isg -₁ isg) +₁ f)
                              ≡⟨ isHom-∘ c₄ c₃ c₂ ⟩
                            ((g -₁ isg) ∘⟨ c₄ ⟩ (isg -₁ isg)) +₁ (isg ∘⟨ c₃ ⟩ f)
                              ≡⟨ cong (_+₁ (isg ∘⟨ c₃ ⟩ f))
                                      (isHom-∘ c₅ c₆ c₇) ⟩
                            ((g ∘⟨ c₅ ⟩ isg) +₁ (-isg ∘⟨ c₆ ⟩ -isg)) +₁ (isg ∘⟨ c₃ ⟩ f)
                              ≡⟨ cong (λ z → (z +₁ (-isg ∘⟨ c₆ ⟩ -isg)) +₁ (isg ∘⟨ c₃ ⟩ f))
                                       (rid-∘ g (isComp-g-isg g)) ⟩
                            (g +₁ (-isg ∘⟨ c₆ ⟩ -isg)) +₁ (isg ∘⟨ c₃ ⟩ f)
                              ≡⟨ cong ((g +₁ (-isg ∘⟨ c₆ ⟩ -isg)) +₁_)
                                      (∘-lid' c c₃) ⟩
                            (g +₁ (-isg ∘⟨ c₆ ⟩ -isg)) +₁ f
                              ≡⟨ cong (λ z → (g +₁ z) +₁ f)
                                      (-isg ∘⟨ c₆ ⟩ -isg
                                        ≡⟨ ∘-cong-r c₆
                                                    -- prove that is(-isg)≡-isg
                                                    (sym (cong 𝒾s (sym (mapInv ι (s g)))
                                                         ∙∙ cong 𝒾 (σι-≡-fun (-₀ s g))
                                                         ∙∙ mapInv ι (s g))) ⟩
                                      -isg ∘⟨ c₈ ⟩
                                              (𝒾s -isg)
                                        ≡⟨ rid-∘ -isg c₈ ⟩
                                      -isg ∎) ⟩
                            (g -₁ isg) +₁ f ∎
                            where
                              isg = 𝒾s g
                              -isg = -₁ isg
                              itf = 𝒾t f

                              --
                              c₁ = ∘-cong-c c
                                            (sym (rId₁ g) ∙ cong (g +₁_) (sym (lCancel₁ isg)))
                                            (sym (lId₁ f) ∙ cong (_+₁ f) (sym (rCancel₁ isg)))
                              --
                              c₂ = ∘-cong-l-c c₁ (assoc₁ g -isg isg)
                              -- isg comp with f
                              c₃ = σι-≡-fun (s g) ∙ c
                              -- (g -₁ isg) comp. with (isg -₁ isg)
                              c₄ = s (g -₁ isg)
                                     ≡⟨ σ-g--isg g ⟩
                                   0₀
                                     ≡⟨ sym (cong t (rCancel₁ isg) ∙ mapId τ) ⟩
                                   t (isg -₁ isg) ∎
                              c₅ : isComposable g isg
                              c₅ = isComp-g-isg g
                              c₆ : isComposable -isg -isg
                              c₆ = s -isg
                                     ≡⟨ mapInv σ isg ⟩
                                   -₀ (s isg)
                                     ≡⟨ cong -₀_ (σι-≡-fun (s g)) ⟩
                                   -₀ (s g)
                                     ≡⟨ cong -₀_ (sym (τι-≡-fun (s g))) ⟩
                                   -₀ (t isg)
                                     ≡⟨ sym (mapInv τ isg) ⟩
                                   t -isg ∎
                              c1 : t (isg +₁ -isg) ≡ 0₀
                              c1 = {!τ .isHom isg -isg!} ∙ {!!}
                              c₇ : isComposable (g +₁ -isg) (𝒾s g +₁ -isg)
                              c₇ = s (g -₁ isg)
                                     ≡⟨ σ-g--isg g ⟩
                                   0₀
                                     ≡⟨ {!!} ⟩
                                   t (isg +₁ -isg) ∎
                              c₇' = s (g -₁ isg)
                                     ≡⟨ σ-g--isg g ⟩
                                   0₀
                                     ≡⟨ sym (rCancel₀ (t isg)) ⟩
                                   t isg -₀ t isg
                                     ≡⟨ cong (t isg +₀_ ) (sym (mapInv τ isg)) ⟩
                                   t isg +₀ t -isg
                                     ≡⟨ sym (τ .isHom isg -isg) ⟩
                                   t (isg -₁ isg) ∎
                              c₈ : isComposable -isg (𝒾s -isg)
                              c₈ = ∘-cong-r-c c₆
                                              (sym (cong 𝒾s (sym (mapInv ι (s g)))
                                                ∙∙ cong 𝒾 (σι-≡-fun (-₀ s g))
                                                ∙∙ mapInv ι (s g)))

    open VertComp
    η-VertComp : (𝒱 : VertComp 𝒢) → vertcomp (vcomp 𝒱) (σ-∘ 𝒱) (τ-∘ 𝒱) (isHom-∘ 𝒱) (assoc-∘ 𝒱) (lid-∘ 𝒱) (rid-∘ 𝒱) ≡ 𝒱
    vcomp (η-VertComp 𝒱 i) = vcomp 𝒱
    σ-∘ (η-VertComp 𝒱 i) = σ-∘ 𝒱
    τ-∘ (η-VertComp 𝒱 i) = τ-∘ 𝒱
    isHom-∘ (η-VertComp 𝒱 i) = isHom-∘ 𝒱
    assoc-∘ (η-VertComp 𝒱 i) = assoc-∘ 𝒱
    lid-∘(η-VertComp 𝒱 i) = lid-∘ 𝒱
    rid-∘ (η-VertComp 𝒱 i) = rid-∘ 𝒱

    module _ where
      isPropVertComp : isProp (VertComp 𝒢)
      vcomp (isPropVertComp 𝒞 𝒞' i) = funExt₃ (λ g f c → VertComp→+₁ 𝒞 g f c ∙ sym (VertComp→+₁ 𝒞' g f c)) i
      σ-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ P i
        where
          P : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → PathP (λ j → s (vcomp (isPropVertComp 𝒞 𝒞' j) g f c) ≡ s f) (σ-∘ 𝒞 g f c) (σ-∘ 𝒞' g f c)
          P g f c = isProp→PathP (λ j → set₀ (s (vcomp (isPropVertComp 𝒞 𝒞' j) g f c)) (s f)) (σ-∘ 𝒞 g f c) (σ-∘ 𝒞' g f c)
      τ-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ P i
        where
          P : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → PathP (λ j → t (vcomp (isPropVertComp 𝒞 𝒞' j) g f c) ≡ t g) (τ-∘ 𝒞 g f c) (τ-∘ 𝒞' g f c)
          P g f c = isProp→PathP (λ j → set₀ (t (vcomp (isPropVertComp 𝒞 𝒞' j) g f c)) (t g)) (τ-∘ 𝒞 g f c) (τ-∘ 𝒞' g f c)
      isHom-∘ (isPropVertComp 𝒞 𝒞' i) = {!!}
      assoc-∘ (isPropVertComp 𝒞 𝒞' i) = {!!}
      lid-∘ (isPropVertComp 𝒞 𝒞' i) = {!!}
      rid-∘ (isPropVertComp 𝒞 𝒞' i) = {!!}

  𝒮ᴰ-Strict2Group : URGStrᴰ (𝒮-ReflGraph ℓ ℓ')
                            VertComp
                            ℓ-zero
  𝒮ᴰ-Strict2Group = Subtype→Sub-𝒮ᴰ (λ 𝒢 → VertComp 𝒢 , isPropVertComp 𝒢)
                                   (𝒮-ReflGraph ℓ ℓ')

  Strict2Group : Type (ℓ-suc ℓℓ')
  Strict2Group = Σ[ 𝒢 ∈ ReflGraph ℓ ℓ' ] VertComp 𝒢
