{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring

open import Cubical.Categories.Category

open Precategory

module _ {ℓ} where

  -- Lemmas about RingHom. TODO: upstream
  idRingHom : (x : Ring ℓ) → RingHom x x
  fst (idRingHom x) = idfun (fst x)
  snd (idRingHom x) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  open IsRingHom

  compRingHom : {x y z : Ring ℓ} → RingHom x y → RingHom y z → RingHom x z
  fst (compRingHom f g) x = g .fst (f .fst x)
  snd (compRingHom f g) = makeIsRingHom (cong (g .fst) (pres1 (snd f)) ∙ pres1 (snd g))
                                        (λ x y → cong (g .fst) (pres+ (snd f) _ _) ∙ pres+ (snd g) _ _)
                                        (λ x y → cong (g .fst) (pres· (snd f) _ _) ∙ pres· (snd g) _ _)

  -- TODO: change the name and implicit arguments ofRingHom≡f
  compIdRingHom : {x y : Ring ℓ} (f : RingHom x y) → compRingHom (idRingHom x) f ≡ f
  compIdRingHom f = RingHom≡f _ _ refl

  idCompRingHom : {x y : Ring ℓ} (f : RingHom x y) → compRingHom f (idRingHom y) ≡ f
  idCompRingHom f = RingHom≡f _ _ refl

  compAssocRingHom : {x y z w : Ring ℓ} (f : RingHom x y) (g : RingHom y z) (h : RingHom z w) →
                     compRingHom (compRingHom f g) h ≡ compRingHom f (compRingHom g h)
  compAssocRingHom f g h = RingHom≡f _ _ refl

  RingPrecategory : Precategory (ℓ-suc ℓ) ℓ
  ob RingPrecategory       = Ring ℓ
  Hom[_,_] RingPrecategory = RingHom
  id RingPrecategory       = idRingHom
  _⋆_ RingPrecategory      = compRingHom
  ⋆IdL RingPrecategory     = compIdRingHom
  ⋆IdR RingPrecategory     = idCompRingHom
  ⋆Assoc RingPrecategory   = compAssocRingHom
