{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Quotient.ImageQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring.Properties
open RingTheory

import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient as CQ

module _ {ℓ : Level} (R : CommRing ℓ) {X : Type ℓ} (f : X → ⟨ R ⟩) where
  module _ where
    open CommRingStr ⦃...⦄
    open CQ
    instance
     _ = str R

    data generatedIdeal : ⟨ R ⟩ → Type ℓ where
      single : ∀ x → generatedIdeal (f x)
      zero   : generatedIdeal 0r
      add    : ∀ {x y} → generatedIdeal x → generatedIdeal y →
                         generatedIdeal (x + y)
      mul    : ∀ {r x} → generatedIdeal x → generatedIdeal (r · x)
      squash : ∀ {x}   → isProp (generatedIdeal x)

    genIdeal : IdealsIn R
    genIdeal = makeIdeal (λ r → generatedIdeal r , squash)
      add zero λ r → mul

    _/Im_ : CommRing ℓ
    _/Im_ = R / genIdeal

    quotientImageHom : CommRingHom R _/Im_
    quotientImageHom = quotientHom R genIdeal

    instance
     _ = str _/Im_

    zeroOnImage : (x : X) → quotientImageHom $cr (f x) ≡ 0r
    zeroOnImage x = zeroOnIdeal genIdeal _ (single x)

  module _ {ℓ' : Level} {S : CommRing ℓ'} (g : CommRingHom R S)
    (gfx=0 : ∀ (x : X) → g $cr (f x) ≡ CommRingStr.0r (snd S)) where
    open CommIdeal R
    open IsCommRingHom (snd g)
    open CommRingStr ⦃...⦄
    instance
      _ = snd R
      _ = snd S
      _ = snd _/Im_

    extendToIdeal : (r : ⟨ R ⟩) → r ∈ genIdeal → g $cr r ≡ 0r
    extendToIdeal .(f x) (single x) = gfx=0 x
    extendToIdeal .(0r) zero = pres0
    extendToIdeal .(r + s) (add {r} {s} r∈I s∈I) =
      g $cr (r + s )
        ≡⟨ pres+ r s ⟩
      (g $cr r) + (g $cr s)
        ≡⟨ cong (λ a → a + (g $cr s)) (extendToIdeal r r∈I) ⟩
      0r + (g $cr s)
        ≡⟨ cong (λ a → 0r + a) (extendToIdeal s s∈I) ⟩
      0r + 0r
        ≡⟨ +IdL 0r ⟩
      0r ∎
    extendToIdeal .(r · s) (mul {r} {s} s∈I) =
      (g $cr (r · s))
        ≡⟨ pres· r s ⟩
      (g $cr r) · (g $cr s)
        ≡⟨ cong (λ a → (g $cr r) · a) (extendToIdeal s s∈I) ⟩
      (g $cr r) · 0r
        ≡⟨ 0RightAnnihilates (CommRing→Ring S) (g $cr r) ⟩
      0r ∎
    extendToIdeal r (squash r∈I0 r∈I1 i) =
      is-set (g $cr r) 0r (extendToIdeal r r∈I0) (extendToIdeal r r∈I1) i

    inducedMap : ⟨ _/Im_ ⟩ → ⟨ S ⟩
    inducedMap = SQ.elim (λ x → is-set) (fst g)
      λ { a b r → equalByDifference (CommRing→Ring S) _ _
      (
      (g $cr a - g $cr b)
        ≡⟨ cong (λ b → g $cr a + b) (sym (pres- b)) ⟩
      (g $cr a + g $cr (- b))
        ≡⟨ sym (pres+ a (- b)) ⟩
      g $cr (a - b)
        ≡⟨ extendToIdeal _ r ⟩
      (0r ∎)
      )
      }

    open IsCommRingHom

    inducedMapPreservesRing : IsCommRingHom (str _/Im_) inducedMap (str S)
    pres0 inducedMapPreservesRing =
      inducedMap 0r
      ≡⟨ cong inducedMap (pres0 (snd quotientImageHom)) ⟩
      inducedMap (quotientImageHom $cr 0r)
      ≡⟨⟩
      g $cr 0r
      ≡⟨ pres0 (snd g) ⟩
      0r ∎
    pres1 inducedMapPreservesRing =
      inducedMap 1r
        ≡⟨ cong inducedMap (pres1 (snd quotientImageHom)) ⟩
      inducedMap (quotientImageHom $cr 1r)
        ≡⟨⟩
      g $cr 1r
        ≡⟨ pres1 (snd g) ⟩
      1r ∎
    pres+ inducedMapPreservesRing =
      SQ.elimProp2 (λ x y → is-set _ _ ) (pres+ (snd g))
    pres· inducedMapPreservesRing =
      SQ.elimProp2 (λ x y → is-set _ _ ) (pres· (snd g))
    pres- inducedMapPreservesRing =
      SQ.elimProp  (λ x   → is-set _ _ ) (pres- (snd g))

    inducedHom : CommRingHom _/Im_ S
    inducedHom = inducedMap , inducedMapPreservesRing

    inducedMapUnique : (h : ⟨ _/Im_ ⟩ → ⟨ S ⟩) →
                       fst g ≡ h ∘ (fst quotientImageHom)  →
                       inducedMap ≡ h
    inducedMapUnique _ = funExt ∘ SQ.elimProp (λ { x → is-set _ _ }) ∘ funExt⁻

    inducedHomUnique : (h : CommRingHom (_/Im_) S) →
                       (p : g ≡ (h ∘cr quotientImageHom)) →
                       inducedHom ≡ h
    inducedHomUnique h p = Σ≡Prop
                           (λ { x → isPropIsCommRingHom (str _/Im_) x (str S) })
                           (inducedMapUnique (fst h) (cong fst p))

