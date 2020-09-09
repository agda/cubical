{-
This module contains
- the type of vertical composition operations
  that can be defined on a reflexive graph


-}
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

open import Cubical.Algebra.Group
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

{-
-- The type of vertical composition operations
-- that can be defined over a reflexive graph 𝒢
--

-- we use the property isComposable instead of defining
-- a type of composable morphisms of G₁, because
-- otherwise it would be difficult to formulate
-- properties involving an odd number of composable morphisms
-- in a uniform and clean way.
-}
record VertComp (𝒢 : ReflGraph ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor vertcomp
  open ReflGraphNotation 𝒢
  open ReflGraphLemmas 𝒢

  -- the vertical composition operation with convenient syntax
  field
    vcomp : (g f : ⟨ G₁ ⟩) → isComposable g f → ⟨ G₁ ⟩
  syntax vcomp g f p = g ∘⟨ p ⟩ f

  field
    -- vcomp preserves source and target
    σ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → s (g ∘⟨ c ⟩ f) ≡ s f
    τ-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f) → t (g ∘⟨ c ⟩ f) ≡ t g
    -- vcomp is a homomorphism, also known as interchange law
    isHom-∘ : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
              (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
              (c'' : isComposable (g +₁ g') (f +₁ f'))
              → (g +₁ g') ∘⟨ c'' ⟩ (f +₁ f') ≡ (g ∘⟨ c ⟩ f) +₁ (g' ∘⟨ c' ⟩ f')
    -- vcomp is associative
    assoc-∘ : (h g f : ⟨ G₁ ⟩)
              (c-hg : isComposable h g)
              (c-gf  : isComposable g f)
              (c-h-gf : isComposable h (g ∘⟨ c-gf ⟩ f))
              (c-hg-f : isComposable (h ∘⟨ c-hg ⟩ g) f)
              → h ∘⟨ c-h-gf ⟩ (g ∘⟨ c-gf ⟩ f) ≡ (h ∘⟨ c-hg ⟩ g) ∘⟨ c-hg-f ⟩ f
    -- composing with identity arrows does nothing
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
  open ReflGraphLemmas 𝒢

  -- lemmas about a given vertical composition
  module _ (𝒞 : VertComp 𝒢) where

    open VertComp 𝒞

    -- These are all propositions, so we use abstract.
    -- Most of these lemmas are nontrivial, because we need to keep a
    -- proof of composability at hand.
    abstract
      -- if (g, f), and (g', f') are composable,
      -- then so is (g + g', f + f')
      +-c : (g f : ⟨ G₁ ⟩) (c : isComposable g f)
           (g' f' : ⟨ G₁ ⟩) (c' : isComposable g' f')
           → isComposable (g +₁ g') (f +₁ f')
      +-c g f c g' f' c' = σ .isHom g g'
                          ∙∙ cong (_+₀ s g') c
                          ∙∙ cong (t f +₀_) c'
                          ∙ sym (τ .isHom f f')

      -- if (g, f) is composable, and g ≡ g',
      -- then (g', f) is composable
      ∘-cong-l-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                  {g' : ⟨ G₁ ⟩} (p : g ≡ g')
                  → isComposable g' f
      ∘-cong-l-c c p = cong s (sym p) ∙ c

      -- if (g, f) is composable, and f ≡ f',
      -- then (g, f') is composable
      ∘-cong-r-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                  {f' : ⟨ G₁ ⟩} (p : f ≡ f')
                  → isComposable g f'
      ∘-cong-r-c c p = c ∙ cong t p

      -- if (g, f) are composable, and (g, f) ≡ (g', f'),
      -- then (g', f') is composable
      -- by combining the two lemmas above
      ∘-cong-c : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                {g' f' : ⟨ G₁ ⟩} (p : g ≡ g') (q : f ≡ f')
                  → isComposable g' f'
      ∘-cong-c c p q = ∘-cong-l-c c p ∙ cong t q

      -- if (g, f) is composable, and g ≡ g',
      -- then g ∘ f ≡ g' ∘ f
      ∘-cong-l : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                {g' : ⟨ G₁ ⟩} (p : g ≡ g')
                → g ∘⟨ c ⟩ f ≡ g' ∘⟨ ∘-cong-l-c c p ⟩ f
      ∘-cong-l {g = g} {f = f} c {g'} p = cong₂ (λ h d → h ∘⟨ d ⟩ f)
                                               p
                                               (toPathP (isPropIsComposable g'
                                                                            f
                                                                            (transp (λ i → isComposable (p i) f) i0 c)
                                                                            (∘-cong-l-c c p)))

      -- if (g, f) is composable, and f ≡ f',
      -- then g ∘ f ≡ g ∘ f'
      ∘-cong-r : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                {f' : ⟨ G₁ ⟩} (p : f ≡ f')
                → g ∘⟨ c ⟩ f ≡ g ∘⟨ ∘-cong-r-c c p ⟩ f'
      ∘-cong-r {g = g} c {f'} p = cong₂ (λ h d → g ∘⟨ d ⟩ h)
                                  p
                                  (toPathP (isPropIsComposable g
                                                               f'
                                                               (transp (λ i → isComposable g (p i)) i0 c)
                                                               (∘-cong-r-c c p)))

      -- if (g, f) are composable, and (g, f) ≡ (g', f'),
      -- then g ∘ f ≡ g' ∘ f'
      ∘-cong : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
                {g' f' : ⟨ G₁ ⟩} (p : g ≡ g') (q : f ≡ f')
                → g ∘⟨ c ⟩ f ≡ g' ∘⟨ ∘-cong-c c p q ⟩ f'
      ∘-cong c p q = ∘-cong-l c p
                    ∙ ∘-cong-r (∘-cong-l-c c p) q

      -- an alternate version of lid-∘
      -- where a composable g is assumed and ι (σ g)
      -- instead of ι (τ f) is used
      ∘-lid' : {g f : ⟨ G₁ ⟩} (c : isComposable g f)
              (c' : isComposable (𝒾s g) f)
              → (𝒾s g) ∘⟨ c' ⟩ f ≡ f
      ∘-lid' {g} {f} c c' = (𝒾s g) ∘⟨ c' ⟩ f
                               ≡⟨ ∘-cong-l c' (cong 𝒾 c) ⟩
                           𝒾t f ∘⟨ ∘-cong-l-c c' (cong 𝒾 c) ⟩ f
                               ≡⟨ lid-∘ f (∘-cong-l-c c' (cong 𝒾 c)) ⟩
                           f ∎

      -- Fundamental theorem:
      -- Any vertical composition is necessarily of the form
      -- g ∘⟨ _ ⟩ f  ≡ g - ι (σ g) + f
      -- This implies contractibility of VertComp 𝒢
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
                           -- abbreviations to reduce the amount of parentheses
                           isg = 𝒾s g
                           -isg = -₁ isg
                           itf = 𝒾t f
                           -- composability proofs,
                           -- none of which are really interesting.
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
           →  (g' +₁ (-is g' -₁ is g)) +₁ f ≡ (-is g +₁ f) +₁ (g' -₁ is g')
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
         -- abbreviations to reduce the number of parentheses
         -g = -₁ g
         isg = 𝒾s g
         isg' = 𝒾s g'
         -isg = -₁ isg
         -isg' = -₁ isg'
         f' = isg'
         -f' = -₁ f'
         -- composability proofs
         c-gf' = isComp-g-isg g'
         c-gf'+ = +-c g f c-gf g' f' c-gf'
         --
         q = (g +₁ g') ∘⟨ c-gf'+ ⟩ (f +₁ f')
               ≡⟨ VertComp→+₁ (g +₁ g') (f +₁ f') c-gf'+ ⟩
             ((g +₁ g') -₁ (𝒾s (g +₁ g'))) +₁ (f +₁ f')
               ≡⟨ cong (λ z → ((g +₁ g') -₁ z) +₁ (f +₁ f'))
                       (ι∘σ .isHom g g') ⟩
             ((g +₁ g') -₁ (isg +₁ isg')) +₁ (f +₁ f')
               ≡⟨ cong (λ z → ((g +₁ g') +₁ z) +₁ (f +₁ f'))
                       (invDistr G₁ isg isg') ⟩
             ((g +₁ g') +₁ (-isg' +₁ -isg)) +₁ (f +₁ f') ∎

      IC3 : (g g' f : ⟨ G₁ ⟩) (c-gf : isComposable g f)
            → (-₁ f) +₁ ((is g +₁ is g') -₁ g') ≡ (is g' -₁ g') +₁ ((-₁ f) +₁ is g)
      IC3 g g' f c-gf =
        -f +₁ ((isg +₁ isg') -₁ g')
          ≡⟨ cong (λ z → -f +₁ ((isg +₁ z) -₁ g'))
                  (sym (invInvo G₁ isg')) ⟩
        -f +₁ ((isg -₁ -isg') -₁ g')
          ≡⟨ cong (λ z → -f +₁ ((z -₁ -isg') -₁ g'))
                  (sym (invInvo G₁ isg)) ⟩
        -f +₁ (((-₁ -isg) -₁ -isg') -₁ g')
          ≡⟨ cong (λ z → -f +₁ (z -₁ g'))
                  (sym (invDistr G₁ -isg' -isg)) ⟩
        -f +₁ ((-₁ (-isg' +₁ -isg)) -₁ g')
          ≡⟨ cong (λ z → -f +₁ z)
                  (sym (invDistr G₁ g' (-isg' +₁ -isg))) ⟩
        -f -₁ (g' +₁ (-isg' +₁ -isg))
          ≡⟨ sym (invDistr G₁ _ f) ⟩
        -₁ ((g' +₁ (-isg' +₁ -isg)) +₁ f)
          ≡⟨ cong -₁_
                  (IC2 g g' f c-gf) ⟩
        -₁ ((-isg +₁ f) +₁ (g' -₁ isg'))
          ≡⟨ invDistr G₁ (-isg +₁ f) (g' -₁ isg') ⟩
        (-₁ (g' -₁ isg')) +₁ (-₁ (-isg +₁ f))
          ≡⟨ cong ((-₁ (g' -₁ isg')) +₁_)
                  (invDistr G₁ -isg f) ⟩
        (-₁ (g' -₁ isg')) +₁ (-f -₁ -isg)
          ≡⟨ cong (_+₁ (-f -₁ -isg))
                  (invDistr G₁ g' -isg') ⟩
        ((-₁ -isg') -₁ g') +₁ (-f -₁ -isg)
          ≡⟨ cong (λ z → (z -₁ g') +₁ (-f -₁ -isg))
                  (invInvo G₁ isg') ⟩
        (isg' -₁ g') +₁ (-f -₁ -isg)
          ≡⟨ cong (λ z → (isg' -₁ g') +₁ (-f +₁ z))
                  (invInvo G₁ isg) ⟩
        (isg' -₁ g') +₁ (-f +₁ isg) ∎
        where
          -f = -₁ f
          -g = -₁ g
          isg = 𝒾s g
          isg' = 𝒾s g'
          -isg = -₁ isg
          -isg' = -₁ isg'


      IC4 : (g g' f : ⟨ G₁ ⟩) (c-gf : isComposable g f)
            → f +₁ (((-is g) -₁ (is g')) +₁ g') ≡ ((-is g') +₁ g') +₁ (f -₁ (is g))
      IC4 g g' f c-gf =
        f +₁ ((-isg -₁ isg') +₁ g')
          ≡⟨ cong (λ z → f +₁ ((-isg -₁ isg') +₁ z))
                  (sym (invInvo G₁ g')) ⟩
        (f +₁ ((-isg -₁ isg') -₁ -g'))
          ≡⟨ cong (λ z → f +₁ ((-isg +₁ z) -₁ -g'))
                  (sym (mapInv ι∘σ g')) ⟩
        f +₁ ((-isg +₁ (is- g')) -₁ -g')
          ≡⟨ cong (λ z → f +₁ ((z +₁ (is- g')) -₁ -g'))
                  (sym (mapInv ι∘σ g)) ⟩
        f +₁ (((is- g) +₁ (is- g')) -₁ -g')
          ≡⟨ cong (_+₁ ((is- g +₁ is- g') -₁ -g'))
                  (sym (invInvo G₁ f)) ⟩
        (-₁ -f) +₁ (((is- g) +₁ (is- g')) -₁ -g')
          ≡⟨ IC3 -g -g' -f c--gf ⟩
        ((is- g') -₁ -g') +₁ ((-₁ -f) +₁ (is- g))
          ≡⟨ cong (λ z → (z -₁ -g') +₁ ((-₁ -f) +₁ (is- g)))
                  (mapInv ι∘σ g') ⟩
        (-isg' -₁ -g') +₁ ((-₁ -f) +₁ (is- g))
          ≡⟨ cong (λ z → (-isg' +₁ z) +₁ ((-₁ -f) +₁ (is- g)))
                  (invInvo G₁ g') ⟩
        (-isg' +₁ g') +₁ ((-₁ -f) +₁ (is- g))
          ≡⟨ cong (λ z → (-isg' +₁ g') +₁ (z +₁ (is- g)))
                  (invInvo G₁ f) ⟩
        (-isg' +₁ g') +₁ (f +₁ (is- g))
          ≡⟨ cong (λ z → (-isg' +₁ g') +₁ (f +₁ z))
                  (mapInv ι∘σ g) ⟩
        (-isg' +₁ g') +₁ (f -₁ isg) ∎
        where
          -f = -₁ f
          -g = -₁ g
          -g' = -₁ g'
          isg = 𝒾s g
          isg' = 𝒾s g'
          -isg = -₁ isg
          -isg' = -₁ isg'
          c--gf = s -g
                    ≡⟨ mapInv σ g ⟩
                  -₀ (s g)
                    ≡⟨ cong -₀_ c-gf ⟩
                  -₀ (t f)
                    ≡⟨ sym (mapInv τ f) ⟩
                  t -f ∎
      -- g = itf
      IC5 : (g' f : ⟨ G₁ ⟩)
            → f +₁ (((-it f) -₁ (is g')) +₁ g') ≡ ((-is g') +₁ g') +₁ (f -₁ (it f))
      IC5 g' f =
        f +₁ ((-itf -₁ isg') +₁ g')
          ≡⟨ cong (λ z → f +₁ (((-₁ (𝒾 z)) -₁ isg') +₁ g'))
                  (sym c-gf) ⟩
        f +₁ ((-isg -₁ isg') +₁ g')
          ≡⟨ IC4 g g' f c-gf ⟩
        (-isg' +₁ g') +₁ (f -₁ isg)
          ≡⟨ cong (λ z → (-isg' +₁ g') +₁ (f -₁ (𝒾 z)))
                  c-gf ⟩
        (-isg' +₁ g') +₁ (f -₁ itf) ∎
        where
          -f = -₁ f
          -itf = -it f
          itf = it f
          g = it f
          -g = -₁ g
          -g' = -₁ g'
          isg = 𝒾s g
          isg' = 𝒾s g'
          -isg = -₁ isg
          -isg' = -₁ isg'
          c-gf : isComposable g f
          c-gf = isComp-itf-f f

  open VertComp

  -- the record VertComp has no eta equality, so this can be used to
  -- construct paths between vertical compositions
  η-VertComp : (𝒱 : VertComp 𝒢) → vertcomp (vcomp 𝒱) (σ-∘ 𝒱) (τ-∘ 𝒱) (isHom-∘ 𝒱) (assoc-∘ 𝒱) (lid-∘ 𝒱) (rid-∘ 𝒱) ≡ 𝒱
  vcomp (η-VertComp 𝒱 i) = vcomp 𝒱
  σ-∘ (η-VertComp 𝒱 i) = σ-∘ 𝒱
  τ-∘ (η-VertComp 𝒱 i) = τ-∘ 𝒱
  isHom-∘ (η-VertComp 𝒱 i) = isHom-∘ 𝒱
  assoc-∘ (η-VertComp 𝒱 i) = assoc-∘ 𝒱
  lid-∘(η-VertComp 𝒱 i) = lid-∘ 𝒱
  rid-∘ (η-VertComp 𝒱 i) = rid-∘ 𝒱


  -- this is just a helper for the module below
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

-- proof that there is at most one vertical composition on a reflexive graph
module _ (𝒢 : ReflGraph ℓ ℓ') where
  open ReflGraphNotation 𝒢
  open ReflGraphLemmas 𝒢
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
