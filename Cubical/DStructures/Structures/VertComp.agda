{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.VertComp where

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
open import Cubical.DStructures.Structures.ReflGraph

open MorphismLemmas
open GroupLemmas

private
  variable
    ℓ ℓ' : Level

record VertComp (𝒢 : ReflGraph ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor vertcomp
  open ReflGraphNotation 𝒢

  field
    vcomp : (g f : ⟨ G₁ ⟩) → (isComposable g f) → ⟨ G₁ ⟩

  syntax vcomp g f p = g ∘⟨ p ⟩ f
  -- infix 9 vcomp

  field
    σ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → s (g ∘⟨ c ⟩ f) ≡ s f
    τ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → t (g ∘⟨ c ⟩ f) ≡ t g
    isHom-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
              (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
              (c'' : isComposable (g +₁ g') (f +₁ f'))
              → (g +₁ g') ∘⟨ c'' ⟩ (f +₁ f') ≡ (g ∘⟨ c ⟩ f) +₁ (g' ∘⟨ c' ⟩ f')
    assoc-∘ : (h g f : ⟨ G₁ ⟩)
              (c-hg : isComposable h g)
              (c-gf  : isComposable g f)
              (c-h-gf : isComposable h (g ∘⟨ c-gf ⟩ f))
              (c-hg-f : isComposable (h ∘⟨ c-hg ⟩ g) f)
              → h ∘⟨ c-h-gf ⟩ (g ∘⟨ c-gf ⟩ f) ≡ (h ∘⟨ c-hg ⟩ g) ∘⟨ c-hg-f ⟩ f
    lid-∘ : (f : ⟨ G₁ ⟩) (c : isComposable (𝒾 (t f)) f)
            → 𝒾 (t f) ∘⟨ c ⟩ f ≡ f
    rid-∘ : (g : ⟨ G₁ ⟩) (c : isComposable g (𝒾 (s g))) → g ∘⟨ c ⟩ 𝒾 (s g) ≡ g

    -- alternative lid/rid definition, but taking paramter c is more flexible
    -- lid-∘ : (f : ⟨ G₁ ⟩) → 𝒾 (t f) ∘⟨ σι-≡-fun (t f) ⟩ f ≡ f
    -- assoc-∘ : (h g f : ⟨ G₁ ⟩) (c : isComposable h g) (c' : isComposable g f)
    --         → h ∘⟨ c ∙ sym (τ-∘ g f c') ⟩ (g ∘⟨ c' ⟩ f) ≡ (h ∘⟨ c ⟩ g) ∘⟨ σ-∘ h g c ∙ c' ⟩ f
               -- → h ∘⟨ c-hg ∙ sym (τ-∘ g f c-gf) ⟩ (g ∘⟨ c-gf ⟩ f)
               --  ≡ (h ∘⟨ c-hg ⟩ g) ∘⟨ σ-∘ h g c-hg ∙ c-gf ⟩ f


module _ {𝒢 : ReflGraph ℓ ℓ'} where
  open ReflGraphNotation 𝒢
  module _ (𝒞 : VertComp 𝒢) where

    open VertComp 𝒞

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
                           ≡⟨ isHom-∘ (g -₁ isg) (isg -₁ isg) c₄
                                      isg f c₃
                                      c₂ ⟩
                         ((g +₁ -isg) ∘⟨ c₄ ⟩ (isg +₁ -isg)) +₁ (isg ∘⟨ c₃ ⟩ f)
                           ≡⟨ cong (_+₁ (isg ∘⟨ c₃ ⟩ f))
                                   (isHom-∘ g isg c₅ -isg -isg c₆ c₄) ⟩
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
                                   -isg ∘⟨ c₈ ⟩ (𝒾s -isg)
                                     ≡⟨ rid-∘ -isg c₈ ⟩
                                   -isg ∎) ⟩
                         (g -₁ isg) +₁ f ∎
                         where
                           isg = 𝒾s g
                           -isg = -₁ isg
                           itf = 𝒾t f
                           c₁ : isComposable (g +₁ (-isg +₁ isg)) ((isg -₁ isg) +₁ f)
                           c₁ = ∘-cong-c c
                                         (sym (rId₁ g) ∙ cong (g +₁_) (sym (lCancel₁ isg)))
                                         (sym (lId₁ f) ∙ cong (_+₁ f) (sym (rCancel₁ isg)))
                           c₂ : isComposable ((g -₁ isg) +₁ isg) ((isg -₁ isg) +₁ f)
                           c₂ = ∘-cong-l-c c₁ (assoc₁ g -isg isg)
                           c₃ : isComposable isg f
                           c₃ = σι-≡-fun (s g) ∙ c
                           c₄ : isComposable (g -₁ isg) (isg -₁ isg)
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
                           c₈ : isComposable -isg (𝒾s -isg)
                           c₈ = ∘-cong-r-c c₆
                                           (sym (cong 𝒾s (sym (mapInv ι (s g)))
                                             ∙∙ cong 𝒾 (σι-≡-fun (-₀ s g))
                                             ∙∙ mapInv ι (s g)))

      -- properties of the interchange law
      IC2 : (g g' f : ⟨ G₁ ⟩) (c-gf : isComposable g f)
           →  (g' +₁ ((-₁ (𝒾s g')) +₁ (-₁ (𝒾s g)))) +₁ f ≡ ((-₁ (𝒾s g)) +₁ f) +₁ (g' -₁ (𝒾s g'))
      IC2 g g' f c-gf =
       (g' +₁ (-isg' +₁ -isg)) +₁ f
         ≡⟨ cong ((g' +₁ (-isg' +₁ -isg)) +₁_)
                 (sym (rCancel-rId G₁ f f') ∙ assoc₁ f f' -f') ⟩
       (g' +₁ (-isg' +₁ -isg)) +₁ ((f +₁ f') -₁ f')
         ≡⟨ assoc₁ (g' +₁ (-isg' +₁ -isg)) (f +₁ f') (-₁ f') ⟩
       ((g' +₁ (-isg' +₁ -isg)) +₁ (f +₁ f')) -₁ f'
         ≡⟨ cong (_-₁ f')
            (sym (lCancel-lId G₁ g _)) ⟩
       ((-g +₁ g) +₁ ((g' +₁ (-isg' +₁ -isg)) +₁ (f +₁ f'))) -₁ f'
         ≡⟨ cong (_-₁ f')
                 (sym (assoc₁ -g g _)) ⟩
       (-g +₁ (g +₁ ((g' +₁ (-isg' +₁ -isg)) +₁ (f +₁ f')))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ z) -₁ f')
                 (assoc₁ g _ (f +₁ f')) ⟩
       (-g +₁ ((g +₁ (g' +₁ (-isg' +₁ -isg))) +₁ (f +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ (z +₁ (f +₁ f'))) -₁ f')
                 (assoc₁ g g' (-isg' -₁ isg)) ⟩
       (-g +₁ (((g +₁ g') +₁ (-isg' +₁ -isg)) +₁ (f +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ z) -₁ f')
                 (sym q) ⟩
       (-g +₁ ((g +₁ g') ∘⟨ c-gf'+ ⟩ (f +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ z) -₁ f')
                 (isHom-∘ g f c-gf
                          g' f' c-gf'
                          c-gf'+) ⟩
       (-g +₁ ((g ∘⟨ c-gf ⟩ f) +₁ (g' ∘⟨ c-gf' ⟩ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ ((g ∘⟨ c-gf ⟩ f) +₁ z)) -₁ f')
                 (VertComp→+₁ g' f' c-gf') ⟩
       (-g +₁ ((g ∘⟨ c-gf ⟩ f) +₁ ((g' -₁ isg') +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ (z +₁ ((g' -₁ isg') +₁ f'))) -₁ f')
                 (VertComp→+₁ g f c-gf) ⟩
       (-g +₁ (((g -₁ isg) +₁ f) +₁ ((g' -₁ isg') +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ (z +₁ ((g' -₁ isg') +₁ f'))) -₁ f')
                 (sym (assoc₁ g -isg f)) ⟩
       (-g +₁ ((g +₁ (-isg +₁ f)) +₁ ((g' -₁ isg') +₁ f'))) -₁ f'
         ≡⟨ cong (λ z → (-g +₁ z) -₁ f')
                 (sym (assoc₁ g (-isg +₁ f) _)) ⟩
       (-g +₁ (g +₁ ((-isg +₁ f) +₁ ((g' -₁ isg') +₁ f')))) -₁ f'
         ≡⟨ cong (_-₁ f')
                 (assoc₁ -g g _) ⟩
       ((-g +₁ g) +₁ ((-isg +₁ f) +₁ ((g' -₁ isg') +₁ f'))) -₁ f'
         ≡⟨ cong (_-₁ f')
            (lCancel-lId G₁ g _) ⟩
       ((-isg +₁ f) +₁ ((g' -₁ isg') +₁ f')) -₁ f'
         ≡⟨ sym (assoc₁ (-isg +₁ f) _ -f') ⟩
       (-isg +₁ f) +₁ (((g' -₁ isg') +₁ f') -₁ f')
         ≡⟨ cong ((-isg +₁ f) +₁_)
                 (sym (assoc₁ (g' -₁ isg') f' -f')) ⟩
       (-isg +₁ f) +₁ ((g' -₁ isg') +₁ (f' -₁ f'))
         ≡⟨ cong ((-isg +₁ f) +₁_ )
                 (rCancel-rId G₁ (g' -₁ isg') f') ⟩
       (-isg +₁ f) +₁ (g' -₁ isg') ∎
       where
         -g = -₁ g
         isg = 𝒾s g
         isg' = 𝒾s g'
         -isg = -₁ isg
         -isg' = -₁ isg'
         f' = isg'
         -f' = -₁ f'
         c-gf' = isComp-g-isg g'
         c-gf'+ = +-c g f c-gf g' f' c-gf'
         q = (g +₁ g') ∘⟨ c-gf'+ ⟩ (f +₁ f')
               ≡⟨ VertComp→+₁ (g +₁ g') (f +₁ f') c-gf'+ ⟩
             ((g +₁ g') -₁ (𝒾s (g +₁ g'))) +₁ (f +₁ f')
               ≡⟨ cong (λ z → ((g +₁ g') -₁ z) +₁ (f +₁ f'))
                       (ι∘σ .isHom g g') ⟩
             ((g +₁ g') -₁ (isg +₁ isg')) +₁ (f +₁ f')
               ≡⟨ cong (λ z → ((g +₁ g') +₁ z) +₁ (f +₁ f'))
                       (invDistr G₁ isg isg') ⟩
             ((g +₁ g') +₁ (-isg' +₁ -isg)) +₁ (f +₁ f') ∎

      -- IC3 : (g g' f : ⟨ G₁ ⟩) (c-gf : isComposable g f)
        --    → {!!} ≡ {!!}
    --  IC3 g g' f c-gf = {!!}
  -- type of composition operations on the reflexive graph 𝒢

  open VertComp

  η-VertComp : (𝒱 : VertComp 𝒢) → vertcomp (vcomp 𝒱) (σ-∘ 𝒱) (τ-∘ 𝒱) (isHom-∘ 𝒱) (assoc-∘ 𝒱) (lid-∘ 𝒱) (rid-∘ 𝒱) ≡ 𝒱
  vcomp (η-VertComp 𝒱 i) = vcomp 𝒱
  σ-∘ (η-VertComp 𝒱 i) = σ-∘ 𝒱
  τ-∘ (η-VertComp 𝒱 i) = τ-∘ 𝒱
  isHom-∘ (η-VertComp 𝒱 i) = isHom-∘ 𝒱
  assoc-∘ (η-VertComp 𝒱 i) = assoc-∘ 𝒱
  lid-∘(η-VertComp 𝒱 i) = lid-∘ 𝒱
  rid-∘ (η-VertComp 𝒱 i) = rid-∘ 𝒱


  module _ (𝒞 𝒞' : VertComp 𝒢) where
    p∘ : vcomp 𝒞 ≡ vcomp 𝒞'
    p∘ = funExt₃ (λ g f c → VertComp→+₁ 𝒞 g f c ∙ sym (VertComp→+₁ 𝒞' g f c))

    pσ : PathP (λ j → (g f : ⟨ G₁ ⟩) (c : isComposable g f) → s (p∘ j g f c) ≡ s f) (σ-∘ 𝒞) (σ-∘ 𝒞')
    pσ = isProp→PathP (λ i → isPropΠ3 (λ g f c → set₀ (s (p∘ i g f c)) (s f))) (σ-∘ 𝒞) (σ-∘ 𝒞')

    passoc : PathP (λ i → (h g f : ⟨ G₁ ⟩)
                          (c-hg : isComposable h g)
                          (c-gf : isComposable g f)
                          (c-h-gf : isComposable h (p∘ i g f c-gf))
                          (c-hg-f : isComposable (p∘ i h g c-hg) f) →
                          p∘ i h (p∘ i g f c-gf) c-h-gf ≡ p∘ i (p∘ i h g c-hg) f c-hg-f) (assoc-∘ 𝒞) (assoc-∘ 𝒞')
    passoc = isProp→PathP (λ j → isPropΠ4 (λ h g f c-hg → isPropΠ3 (λ c-gf c-h-gf c-hg-f → set₁ (p∘ j h (p∘ j g f c-gf) c-h-gf) (p∘ j (p∘ j h g c-hg) f c-hg-f)))) (assoc-∘ 𝒞) (assoc-∘ 𝒞')
    -- (p∘ j h (p∘ j g f c-gf) c-h-gf ≡ p∘ j (p∘ j h g c-hg) f c-hg-f)

module _ (𝒢 : ReflGraph ℓ ℓ') where
  open ReflGraphNotation 𝒢
  open VertComp
  isPropVertComp : isProp (VertComp 𝒢)
  vcomp (isPropVertComp 𝒞 𝒞' i) = funExt₃ (λ g f c → VertComp→+₁ 𝒞 g f c ∙ sym (VertComp→+₁ 𝒞' g f c)) i
  -- σ-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ P i
  σ-∘ (isPropVertComp 𝒞 𝒞' i) = pσ 𝒞 𝒞' i
    where
      P : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
          → PathP (λ j → s (vcomp (isPropVertComp 𝒞 𝒞' j) g f c) ≡ s f)
                  (σ-∘ 𝒞 g f c)
                  (σ-∘ 𝒞' g f c)
      P g f c = isProp→PathP (λ j → set₀ (s (vcomp (isPropVertComp 𝒞 𝒞' j) g f c)) (s f)) (σ-∘ 𝒞 g f c) (σ-∘ 𝒞' g f c)
  τ-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ P i
    where
      P : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → PathP (λ j → t (vcomp (isPropVertComp 𝒞 𝒞' j) g f c) ≡ t g) (τ-∘ 𝒞 g f c) (τ-∘ 𝒞' g f c)
      P g f c = isProp→PathP (λ j → set₀ (t (vcomp (isPropVertComp 𝒞 𝒞' j) g f c)) (t g)) (τ-∘ 𝒞 g f c) (τ-∘ 𝒞' g f c)
  isHom-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ (λ g f c → funExt₃ (λ g' f' c' → funExt (λ c+ → P g f c g' f' c' c+))) i
    where
      P : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
          (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
          (c+ : isComposable (g +₁ g') (f +₁ f'))
          → PathP (λ j → vcomp (isPropVertComp 𝒞 𝒞' j) (g +₁ g') (f +₁ f') c+
                         ≡ (vcomp (isPropVertComp 𝒞 𝒞' j) g f c) +₁ (vcomp (isPropVertComp 𝒞 𝒞' j) g' f' c'))
                  (isHom-∘ 𝒞 g f c g' f' c' c+)
                  (isHom-∘ 𝒞' g f c g' f' c' c+)
      P g f c g' f' c' c+ = isProp→PathP (λ j → set₁ (vcomp (isPropVertComp 𝒞 𝒞' j) (g +₁ g') (f +₁ f') c+)
                                                     ((vcomp (isPropVertComp 𝒞 𝒞' j) g f c) +₁ (vcomp (isPropVertComp 𝒞 𝒞' j) g' f' c')))
                                         (isHom-∘ 𝒞 g f c g' f' c' c+)
                                         (isHom-∘ 𝒞' g f c g' f' c' c+)
  -- assoc-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₃ (λ h g f → funExt₂ (λ c-hg c-gf → funExt₂ (λ c-h-gf c-hg-f → P h g f c-hg c-gf c-h-gf c-hg-f))) i
  assoc-∘ (isPropVertComp 𝒞 𝒞' i) = passoc 𝒞 𝒞' i
  lid-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₂ P i
    where
      P : (f : ⟨ G₁ ⟩) (c : isComposable (𝒾 (t f)) f)
          → PathP (λ j → vcomp (isPropVertComp 𝒞 𝒞' j) (𝒾 (t f)) f c ≡ f) (lid-∘ 𝒞 f c) (lid-∘ 𝒞' f c)
      P f c = isProp→PathP (λ j → set₁ (vcomp (isPropVertComp 𝒞 𝒞' j) (𝒾 (t f)) f c) f) (lid-∘ 𝒞 f c) (lid-∘ 𝒞' f c)
  rid-∘ (isPropVertComp 𝒞 𝒞' i) = funExt₂ P i
    where
      P : (g : ⟨ G₁ ⟩) (c : isComposable g (𝒾 (s g)))
          → PathP (λ j → vcomp (isPropVertComp 𝒞 𝒞' j) g (𝒾 (s g)) c ≡ g) (rid-∘ 𝒞 g c) (rid-∘ 𝒞' g c)
      P g c = isProp→PathP (λ j → set₁ (vcomp (isPropVertComp 𝒞 𝒞' j) g (𝒾 (s g)) c) g) (rid-∘ 𝒞 g c) (rid-∘ 𝒞' g c)
