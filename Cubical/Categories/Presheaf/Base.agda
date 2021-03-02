{-# OPTIONS --cubical --no-import-sorts --postfix-projections --safe #-}

module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

module _ {ℓ ℓ' : Level} where
  PreShv : Precategory ℓ ℓ' → Precategory _ _ -- (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-max (ℓ-suc ℓ) ℓ')
  PreShv C = FUNCTOR (C ^op) (SET ℓ)

  instance
    isCatPreShv : {C : Precategory ℓ ℓ'}
                → isCategory (PreShv C)
    isCatPreShv {C} = isCatFUNCTOR (C ^op) (SET ℓ)

private
  variable
    ℓ : Level

module Yoneda (C : Precategory ℓ ℓ) ⦃ C-cat : isCategory C ⦄ where
  open Functor
  open NatTrans
  open Precategory C

  yo : ob → Functor (C ^op) (SET ℓ)
  yo x .F-ob y .fst = C [ y , x ]
  yo x .F-ob y .snd = C-cat .isSetHom
  yo x .F-hom f g = f ⋆⟨ C ⟩ g
  yo x .F-id i f = ⋆IdL f i
  yo x .F-seq f g i h = ⋆Assoc g f h i

  YO : Functor C (PreShv C)
  YO .F-ob = yo
  YO .F-hom f .N-ob z g = g ⋆⟨ C ⟩ f
  YO .F-hom f .N-hom g i h = ⋆Assoc g h f i
  YO .F-id = makeNatTransPath λ i _ → λ f → ⋆IdR f i
  YO .F-seq f g = makeNatTransPath λ i _ → λ h → ⋆Assoc h f g (~ i)


  module _ {x} (F : Functor (C ^op) (SET ℓ)) where
    yo-yo-yo : NatTrans (yo x) F → F .F-ob x .fst
    yo-yo-yo α = α .N-ob _ (id _)

    no-no-no : F .F-ob x .fst → NatTrans (yo x) F
    no-no-no a .N-ob y f = F .F-hom f a
    no-no-no a .N-hom f = funExt λ g i → F .F-seq g f i a

    yoIso : Iso (NatTrans (yo x) F) (F .F-ob x .fst)
    yoIso .Iso.fun = yo-yo-yo
    yoIso .Iso.inv = no-no-no
    yoIso .Iso.rightInv b i = F .F-id i b
    yoIso .Iso.leftInv a = makeNatTransPath (funExt λ _ → funExt rem)
      where
        rem : ∀ {z} (x₁ : C [ z , x ]) → F .F-hom x₁ (yo-yo-yo a) ≡ (a .N-ob z) x₁
        rem g =
          F .F-hom g (yo-yo-yo a)
            ≡[ i ]⟨ a .N-hom g (~ i) (id x) ⟩
          a .N-hom g i0 (id x)
            ≡[ i ]⟨ a .N-ob _ (⋆IdR g i) ⟩
          (a .N-ob _) g
            ∎

    yoEquiv : NatTrans (yo x) F ≃ F .F-ob x .fst
    yoEquiv = isoToEquiv yoIso


  isFullYO : isFull YO
  isFullYO x y F[f] = ∣ yo-yo-yo _ F[f] , yoIso {x} (yo y) .Iso.leftInv F[f] ∣

  isFaithfulYO : isFaithful YO
  isFaithfulYO x y f g p i =
    hcomp
      (λ j → λ{ (i = i0) → ⋆IdL f j; (i = i1) → ⋆IdL g j})
      (yo-yo-yo _ (p i))
