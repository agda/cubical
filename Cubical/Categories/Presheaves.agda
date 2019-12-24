{-# OPTIONS --cubical --postfix-projections #-}

module Cubical.Categories.Presheaves where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Sets

module _ (ℓ : Level) where
  PSH : Precategory ℓ → Precategory (ℓ-suc ℓ)
  PSH 𝒞 = FUNCTOR (𝒞 ^op) (SET ℓ)

private
  variable
    ℓ : Level

module Yoneda (𝒞 : Precategory ℓ) ⦃ 𝒞-cat : isCategory 𝒞 ⦄ where
  open Functor
  open NatTrans

  yo : 𝒞 .ob → Functor (𝒞 ^op) (SET ℓ)
  yo x .F-ob y .fst = 𝒞 .hom y x
  yo x .F-ob y .snd = 𝒞-cat .homIsSet
  yo x .F-hom f .lower g = 𝒞 .seq f g
  yo x .F-idn i .lower f = 𝒞 .seq-λ f i
  yo x .F-seq f g i .lower h = 𝒞 .seq-α g f h i

  YO : Functor 𝒞 (PSH ℓ 𝒞)
  YO .F-ob = yo
  YO .F-hom f .N-ob z .lower g = 𝒞 .seq g f
  YO .F-hom f .N-hom g i .lower h = 𝒞 .seq-α g h f i
  YO .F-idn = make-nat-trans-path λ i _ → lift λ f → 𝒞 .seq-ρ f i
  YO .F-seq f g = make-nat-trans-path λ i _ → lift λ h → 𝒞 .seq-α h f g (~ i)


  module _ {x} (F : Functor (𝒞 ^op) (SET ℓ)) where
    yo-yo-yo : NatTrans (yo x) F → F .F-ob x .fst
    yo-yo-yo α = α .N-ob _ .lower (𝒞 .idn _)

    no-no-no : F .F-ob x .fst → NatTrans (yo x) F
    no-no-no a .N-ob y .lower f = F .F-hom f .lower a
    no-no-no a .N-hom f = liftExt (funExt λ g i → F .F-seq g f i .lower a)

  module YonedaLemma {x} (F : Functor (𝒞 ^op) (SET ℓ)) where

    yo-iso : Iso (NatTrans (yo x) F) (F .F-ob x .fst)
    yo-iso .Iso.fun = yo-yo-yo F
    yo-iso .Iso.inv = no-no-no F
    yo-iso .Iso.rightInv b i = F .F-idn i .lower b
    yo-iso .Iso.leftInv a = make-nat-trans-path (funExt λ _ → liftExt (funExt rem))
      where
        rem : ∀ {z} (x₁ : 𝒞 .hom z x) → F .F-hom x₁ .lower (yo-yo-yo _ a) ≡ lower (a .N-ob z) x₁
        rem g =
          F .F-hom g .lower (yo-yo-yo _ a)
            ≡[ i ]⟨ a .N-hom g (~ i) .lower (𝒞 .idn x) ⟩
          a .N-hom g i0 .lower (𝒞 .idn x)
            ≡[ i ]⟨ a .N-ob _ .lower (𝒞 .seq-ρ g i) ⟩
          lower (a .N-ob _) g
            ∎


  YO-full : is-full YO
  YO-full x y F[f] = ∣ yo-yo-yo _ F[f] , YonedaLemma.yo-iso {x} (yo y) .Iso.leftInv F[f] ∣

  YO-faithful : is-faithful YO
  YO-faithful x y f g p i =
    hcomp
      (λ j → λ{ (i = i0) → 𝒞 .seq-λ f j; (i = i1) → 𝒞 .seq-λ g j})
      (yo-yo-yo _ (p i))
