{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Exact where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)
open import Cubical.Algebra.Group.GroupPath

open import Cubical.Algebra.Group.Instances.Unit

-- TODO : Define exact sequences
-- (perhaps short, finite, ℕ-indexed and ℤ-indexed)

SES→isEquiv : ∀ {ℓ ℓ'} {L R : Group ℓ-zero}
  → {G : Group ℓ} {H : Group ℓ'}
  → Unit ≡ L
  → Unit ≡ R
  → (lhom : GroupHom L G) (midhom : GroupHom G H) (rhom : GroupHom H R)
  → ((x : _) → isInKer midhom x → isInIm lhom x)
  → ((x : _) → isInKer rhom x → isInIm midhom x)
  → isEquiv (fst midhom)
SES→isEquiv {R = R} {G = G} {H = H} =
  J (λ L _ → Unit ≡ R →
      (lhom : GroupHom L G) (midhom : GroupHom G H)
      (rhom : GroupHom H R) →
      ((x : fst G) → isInKer midhom x → isInIm lhom x) →
      ((x : fst H) → isInKer rhom x → isInIm midhom x) →
      isEquiv (fst midhom))
      ((J (λ R _ → (lhom : GroupHom Unit G) (midhom : GroupHom G H)
                   (rhom : GroupHom H R) →
                   ((x : fst G) → isInKer midhom x → isInIm lhom x) →
                   ((x : _) → isInKer rhom x → isInIm midhom x) →
                   isEquiv (fst midhom))
         main))
  where
  main : (lhom : GroupHom Unit G) (midhom : GroupHom G H)
         (rhom : GroupHom H Unit) →
         ((x : fst G) → isInKer midhom x → isInIm lhom x) →
         ((x : fst H) → isInKer rhom x → isInIm midhom x) →
         isEquiv (fst midhom)
  main lhom midhom rhom lexact rexact =
    BijectionIsoToGroupEquiv {G = G} {H = H}
      bijIso' .fst .snd
    where
    bijIso' : BijectionIso G H
    BijectionIso.fun bijIso' = midhom
    BijectionIso.inj bijIso' x inker =
      pRec (GroupStr.is-set (snd G) _ _)
           (λ s → sym (snd s) ∙ IsGroupHom.pres1 (snd lhom))
           (lexact _ inker)
    BijectionIso.surj bijIso' x = rexact x refl
