{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification.ElimProp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf

open import Cubical.Categories.Site.Sheafification.Base


module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C
  open Coverage J
  open Sheafification J P

  module ElimPropAssumptions
    {ℓB : Level}
    (B : {c : ob} → ⟨F⟅ c ⟆⟩ → Type ℓB)
    where

    isPropValued =
      {c : ob} →
      {x : ⟨F⟅ c ⟆⟩} →
      isProp (B x)

    Onη =
      {c : ob} →
      (x : ⟨ P ⟅ c ⟆ ⟩) →
      B (η⟦⟧ x)

    isLocal =
      {c : ob} →
      (x : ⟨F⟅ c ⟆⟩) →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      ((patch : ⟨ cov ⟩) → B (restrict (patchArr cov patch) x)) →
      B x

    -- This assumption will turn out to be unnecessary.
    isMonotonous =
      {c d : ob} →
      (f : Hom[ d , c ]) →
      (x : ⟨F⟅ c ⟆⟩) →
      B x → B (restrict f x)

  open ElimPropAssumptions

  module ElimPropWithMonotonous
    {ℓB : Level}
    {B : {c : ob} → ⟨F⟅ c ⟆⟩ → Type ℓB}
    (isPropValuedB : isPropValued B)
    (onηB : Onη B)
    (isLocalB : isLocal B)
    (isMonotonousB : isMonotonous B)
    where

    amalgamatePreservesB :
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (fam : CompatibleFamily F cov) →
      ((patch : ⟨ cov ⟩) → B (fst fam patch)) →
      B (amalgamate cover fam)
    amalgamatePreservesB cover fam famB =
      isLocalB
        (amalgamate cover fam)
        cover
        λ patch → subst B (sym (restrictAmalgamate cover fam patch)) (famB patch)

    mkPathP :
      {c : ob} →
      {x0 x1 : ⟨F⟅ c ⟆⟩} →
      (p : x0 ≡ x1) →
      (b0 : B (x0)) →
      (b1 : B (x1)) →
      PathP (λ i → B (p i)) b0 b1
    mkPathP p = isProp→PathP (λ i → isPropValuedB)

    elimProp : {c : ob} → (x : ⟨F⟅ c ⟆⟩) → B x
    elimProp (trunc x y p q i j) =
      isOfHLevel→isOfHLevelDep 2 (λ _ → isProp→isSet isPropValuedB)
        (elimProp x)
        (elimProp y)
        (cong elimProp p)
        (cong elimProp q)
        (trunc x y p q)
        i
        j
    elimProp (restrict f x) =
      isMonotonousB f x (elimProp x)
    elimProp (restrictId x i) =
      mkPathP
        (restrictId x)
        (isMonotonousB id x (elimProp x))
        (elimProp x)
        i
    elimProp (restrictRestrict f g x i) =
      mkPathP (restrictRestrict f g x)
        (isMonotonousB (g ⋆ f) x (elimProp x))
        (isMonotonousB g (restrict f x) (isMonotonousB f x (elimProp x)))
        i
    elimProp (η⟦⟧ x) =
      onηB x
    elimProp (ηNatural f x i) =
      mkPathP (ηNatural f x)
        (onηB ((P ⟪ f ⟫) x))
        (isMonotonousB f (η⟦⟧ x) (onηB x))
        i
    elimProp (sep cover x y x~y i) =
      mkPathP (sep cover x y x~y)
        (elimProp x)
        (elimProp y)
        i
    elimProp (amalgamate cover fam) =
      amalgamatePreservesB cover fam λ patch → elimProp (fst fam patch)
    elimProp (restrictAmalgamate cover fam patch i) =
      let cov = str (covers _) cover in
      mkPathP (restrictAmalgamate cover fam patch)
        (isMonotonousB (patchArr cov patch) (amalgamate cover fam)
          (amalgamatePreservesB cover fam (λ patch' → elimProp (fst fam patch'))))
        (elimProp (fst fam patch))
        i

  module _
    {ℓB : Level}
    {B : {c : ob} → ⟨F⟅ c ⟆⟩ → Type ℓB}
    (isPropValuedB : isPropValued B)
    (onηB : Onη B)
    (isLocalB : isLocal B)
    where

    -- Idea: strengthen the inductive hypothesis to "every restriction of x satisfies B"
    private
      B' : {c : ob} → ⟨F⟅ c ⟆⟩ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓB)
      B' x = {d : ob} → (f : Hom[ d , _ ]) → B (restrict f x)

      isPropValuedB' : isPropValued B'
      isPropValuedB' = isPropImplicitΠ λ _ → isPropΠ λ _ → isPropValuedB

      onηB' : Onη B'
      onηB' x f = subst B (ηNatural f x) (onηB ((P ⟪ f ⟫) x))

      isLocalB' : isLocal B'
      isLocalB' x cover B'fam f =
        PT.rec
          isPropValuedB
          (λ (cover' , refines) →
            isLocalB (restrict f x) cover' λ patch' →
              PT.rec
                isPropValuedB
                (λ (patch , g , p'⋆f≡g⋆p) →
                  let
                    p = patchArr (str (covers _) cover) patch
                    p' = patchArr (str (covers _) cover') patch'
                  in
                  subst B
                    ( restrict g (restrict p x)   ≡⟨ sym (restrictRestrict _ _ _) ⟩
                      restrict (g ⋆ p) x          ≡⟨ cong (λ f → restrict f x) (sym p'⋆f≡g⋆p) ⟩
                      restrict (p' ⋆ f) x         ≡⟨ restrictRestrict _ _ _ ⟩
                      restrict p' (restrict f x)  ∎ )
                    (B'fam patch g))
                (refines patch'))
          (pullbackStability _ cover _ f)

      isMonotonousB' : isMonotonous B'
      isMonotonousB' f x B'x g = subst B (restrictRestrict _ _ _) (B'x (g ⋆ f))

      elimPropInduction :
        {c : ob} →
        (x : ⟨F⟅ c ⟆⟩) →
        B' x
      elimPropInduction =
        ElimPropWithMonotonous.elimProp {B = B'}
          isPropValuedB'
          onηB'
          isLocalB'
          isMonotonousB'

    elimProp : {c : ob} → (x : ⟨F⟅ c ⟆⟩) → B x
    elimProp x = subst B (restrictId _) (elimPropInduction x id)
