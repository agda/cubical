
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Morphism.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport


morphTransport : {ℓ ℓ' : Level} {G G' : Group ℓ} {H H' : Group ℓ'}
  (f : morph G H) (f' : morph G' H')
  (p-G : G ≡ G') (p-H : H ≡ H')
  (trf : (g : Group.type G)
    → transport (λ i → Group.type (p-H i)) (f .fst g) ≡ f' .fst (transport (λ i → Group.type (p-G i)) g))
  → transp (λ i → morph (p-G i) (p-H i)) i0 f ≡ f'
morphTransport {ℓ} {ℓ'} {G} {G'} {H} {H'}
  f f' p-G p-H trf = ΣPathP (p , p')
  where
    -- abbreviations
    TG = Group.type G
    TG' = Group.type G'

    _∙G'_ = isGroup.comp (Group.groupStruc G')
    _∙H'_ = isGroup.comp (Group.groupStruc H')

    -- Transport laws for type of G
    tr : TG → TG'
    tr = λ (g : TG) → transport (λ i → Group.type (p-G i)) g
    tr- : TG' → TG
    tr- = λ (g' : TG') → transport (λ i → Group.type (p-G (~ i))) g'

    trtr-≡ : (g' : TG') → tr (tr- g') ≡ g'
    trtr-≡ g' = transportTransport⁻ (λ i → Group.type (p-G i)) g'

    tr-tr≡ : (g : TG) → tr- (tr g) ≡ g
    tr-tr≡ g = transport⁻Transport (λ i → Group.type (p-G i)) g


    p = funExt (λ g' → (trf (tr- g')) ∙ (cong (fst f') (trtr-≡ g')))
    p' = isProp→PathP (λ i s t →
                         funExt (λ g'₀ →
                                funExt (λ g'₁ →
                                       Group.setStruc H' (p i (g'₀ ∙G' g'₁)) (p i g'₀ ∙H' p i g'₁) (s g'₀ g'₁) (t g'₀ g'₁))))
                      (snd (transp (λ i → morph (p-G i) (p-H i)) i0 f))
                      (snd f')
