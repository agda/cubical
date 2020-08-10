
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Explicit.Interface where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Strict2Group.Explicit.Base
open import Cubical.Data.Strict2Group.Explicit.Notation

module S2GInterface {ℓ : Level} ((strict2groupexp C₀ C₁ s t i ∘ si ti s∘ t∘ isMorph∘ assoc∘ lUnit∘ rUnit∘) : Strict2GroupExp ℓ) where

  open S2GBaseNotation C₀ C₁ s t i ∘ public

  module Identities1 where
    -- to be consistent with the other notation
    tarId = ti
    srcId = si
    -- identity is preserved by id
    id1₀≡1₁ : id 1₀ ≡ 1₁
    id1₀≡1₁ = morphId {G = C₀} {H = C₁} i

  open Identities1 public

  module C₁×₀C₁ where

    -- the composable morphisms as record type
    record Co : Type ℓ where
      constructor co
      field
        g f : TC₁
        coh : CohCond g f

    -- syntax
    𝓁 𝓇 : Co → TC₁
    𝓁 = Co.g
    𝓇 = Co.f
    𝒸 : (gfc : Co) → CohCond (𝓁 gfc) (𝓇 gfc)
    𝒸 = Co.coh

    -- compose a co object using ∘
    ⊙ : Co → TC₁
    ⊙ gfc = ∘ (𝓁 gfc) (𝓇 gfc) (𝒸 gfc)

    -- basically ∘, but for the sake of interfacing, we don't want to use ∘
    ⊙' : (g f : TC₁) → CohCond g f → TC₁
    ⊙' g f c = ⊙ (co g f c)

    -- interface for those names aswell
    src⊙ : (gfc : Co) → src (⊙ gfc) ≡ src (𝓇 gfc)
    src⊙ (co g f c) = s∘ g f c

    tar⊙ : (gfc : Co) → tar (⊙ gfc) ≡ tar (𝓁 gfc)
    tar⊙ (co g f c) = t∘ g f c

    src⊙' : (g f : TC₁) → (c : CohCond g f) → src (⊙' g f c) ≡ src f
    src⊙' g f c = src⊙ (co g f c)

    tar⊙' : (g f : TC₁) → (c : CohCond g f) → tar (⊙' g f c) ≡ tar g
    tar⊙' g f c = tar⊙ (co g f c)

    -- multiplication in C₁×₀C₁
    _∙Co_ : (gfc gfc' : Co) → Co
    (co g f coh) ∙Co (co g' f' coh') =
      co (g ∙₁ g') (f ∙₁ f')
        (src∙₁ g g' ∙ cong (_∙₀ src g') coh ∙ cong (tar f ∙₀_) coh' ∙ sym (tar∙₁ f f'))

    -- unit element w.r.t. ∙c. Too bad there is no \_c
    1c : Co
    1c = co 1₁ 1₁ ((cong src (sym id1₀≡1₁)) ∙∙ si 1₀ ∙∙ sym (ti 1₀) ∙ cong tar id1₀≡1₁)

    -- the interchange law reformulated using ⊙
    isMorph⊙ : (gfc gfc' : Co) → ⊙ (gfc ∙Co gfc') ≡ ⊙ gfc ∙₁ ⊙ gfc'
    isMorph⊙ (co _ _ c) (co _ _ c') = isMorph∘ c c'

    -- associator notation
    assoc⊙' : (h g f : TC₁) → (c : CohCond g f) → (c' : CohCond h g) → ⊙' (⊙' h g c') f ((src⊙' h g c') ∙ c) ≡ ⊙' h (⊙' g f c) (c' ∙ (sym (tar⊙' g f c)))
    assoc⊙' h g f c c' = assoc∘ c c'

    -- the left and right unit laws reformulated using ⊙
    lUnit⊙ : (f : TC₁) → ⊙ (co (id (tar f)) f (srcId (tar f))) ≡ f
    lUnit⊙ = lUnit∘
    rUnit⊙ : (f : TC₁) → ⊙ (co f (id (src f)) (sym (tarId (src f)))) ≡ f
    rUnit⊙ = rUnit∘

    -- the path component of f in C₁
    ΣC₁p : (f : TC₁) → Type ℓ
    ΣC₁p f = Σ[ f' ∈ TC₁ ] (f ≡ f')

    private
      -- for given g, the type of f that g can be precomposed with
      _∘* : TC₁ → Type ℓ
      g ∘* = Σ[ f ∈ TC₁ ] (CohCond g f)
      -- for given f, the type of g that f can be postcomposed with
      *∘_ : TC₁ → Type ℓ
      *∘ f = Σ[ g ∈ TC₁ ] (CohCond g f)

      -- alternate notation for ∘
      -- this is used in ∘*≡ to λ-abstract in cong
      _∘*_ : (g : TC₁) (fc : g ∘*) → TC₁
      _∘*_ g (f , c) = ∘ g f c
      _*∘_ : (f : TC₁) (gc : *∘ f) → TC₁
      _*∘_ f (g , c) = ∘ g f c

      -- since we have proof irrelevance in C₀ we can show that f ≡ f' → g∘f ≡ g∘f'
      ∘*≡ : (g : TC₁) → (fc : g ∘*) → (f'p : ΣC₁p (fst fc)) → g ∘* fc ≡ g ∘* ((fst f'p) , snd fc ∙ cong tar (snd f'p))
      ∘*≡ g fc f'p = cong (g ∘*_) (ΣPathP (snd f'p , isProp→PathP (λ j → Group.setStruc C₀ (src g) (tar (snd f'p j))) (snd fc) (snd fc ∙ cong tar (snd f'p))))
      *∘≡ : (f : TC₁) → (gc : *∘ f) → (g'p : ΣC₁p (fst gc)) → f *∘ gc ≡ f *∘ (fst g'p , ((cong src (sym (snd g'p))) ∙ snd gc))
      *∘≡ f gc g'p = cong (_*∘_ f) (ΣPathP ((snd g'p) , (isProp→PathP (λ j → Group.setStruc C₀ (src (snd g'p j)) (tar f)) (snd gc) (cong src (sym (snd g'p)) ∙ snd gc))))

    -- ⊙ respecs paths on the right
    ⊙≡ : ((co g f c) : Co) → (f'p : ΣC₁p f) → ⊙ (co g f c) ≡ ⊙ (co g (fst f'p) (c ∙ (cong tar (snd f'p))))
    ⊙≡ (co g f c) (f' , f≡f') = ∘*≡ g (f , c) (f' , f≡f')

    -- ⊙ respects paths on the left
    ≡⊙ : ((co g f c) : Co) → ((g' , g≡g') : ΣC₁p g) → ⊙ (co g f c) ≡ ⊙ (co g' f (cong src (sym g≡g') ∙ c))
    ≡⊙ (co g f c) (g' , g≡g') = *∘≡ f (g , c) (g' , g≡g')

    -- ⊙ resepcts paths on the coherence condition
    ⊙≡c : ((co g f c) : Co) → (c' : CohCond g f) → ⊙ (co g f c) ≡ ⊙ (co g f c')
    ⊙≡c (co g f c) c' = cong (λ z → ⊙ (co g f z)) (Group.setStruc C₀ (src g) (tar f) c c')

    -- implicit version of ⊙≡c
    ⊙≡c~ : {g f : TC₁} (c c' : CohCond g f) → ⊙ (co g f c) ≡ ⊙ (co g f c')
    ⊙≡c~ {g} {f} c c' = cong (λ z → ⊙ (co g f z)) (Group.setStruc C₀ (src g) (tar f) c c')

    -- ⊙ respecting paths on the left also changes the coherence condition so this should be used instead
    ≡⊙c* : {g g' f : TC₁} (c : CohCond g f) (g≡g' : g ≡ g') (c' : CohCond g' f) → ⊙' g f c ≡ ⊙' g' f c'
    ≡⊙c* {g} {g'} {f} c g≡g' c' = (≡⊙ (co g f c) (g' , g≡g')) ∙ ⊙≡c~ ((cong src (sym g≡g')) ∙ c) c'

    -- ⊙ respecting paths on the right also changes the coherence condition so this should be used instead
    ⊙≡c* : {g f f' : TC₁} (c : CohCond g f) (f≡f' : f ≡ f') (c' : CohCond g f') → ⊙' g f c ≡ ⊙' g f' c'
    ⊙≡c* {g} {f} {f'} c f≡f' c' = (⊙≡ (co g f c) (f' , f≡f')) ∙ ⊙≡c~ (c ∙ cong tar f≡f') c'

    -- use the left and right unit law with an arbitrary coherence proof c
    lUnit⊙c : (f : TC₁) → (c : CohCond (id (tar f)) f) → ⊙ (co (id (tar f)) f c) ≡ f
    lUnit⊙c f c = (⊙≡c (co (id (tar f)) f c) (srcId (tar f))) ∙ (lUnit⊙ f)
    rUnit⊙c : (f : TC₁) → (c : CohCond f (id (src f))) → ⊙ (co f (id (src f)) c) ≡ f
    rUnit⊙c f c = (⊙≡c (co f (id (src f)) c) (sym (tarId (src f)))) ∙ (rUnit⊙ f)

  open C₁×₀C₁ public

  module Identities2 where
    -- source and target of unit element
    tar1₁≡1₀ : tar 1₁ ≡ 1₀
    tar1₁≡1₀ = morphId {G = C₁} {H = C₀} t
    src1₁≡1₀ = morphId {G = C₁} {H = C₀} s

    -- taking the source is the same as the target of the identity of the source
    src≡tarIdSrc : (f : TC₁) → CohCond f (id (src f))
    src≡tarIdSrc f = sym (ti (src f))

  open Identities2 public
