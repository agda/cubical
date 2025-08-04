-- Product of type-many categories

module Cubical.Categories.Constructions.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

private
  variable
    ℓA ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

module _ (A : Type ℓA) (catC : A → Category ℓC ℓC') where
  ΠC : Category (ℓ-max ℓA ℓC) (ℓ-max ℓA ℓC')
  ΠC .ob = (a : A) → ob (catC a)
  ΠC .Hom[_,_] c c' = (a : A) → catC a [ c a , c' a ]
  ΠC .id a = id (catC a)
  ΠC ._⋆_ g f a = g a ⋆⟨ catC a ⟩ f a
  ΠC .⋆IdL f = funExt λ a → ⋆IdL (catC a) (f a)
  ΠC .⋆IdR f = funExt λ a → ⋆IdR (catC a) (f a)
  ΠC .⋆Assoc h g f = funExt λ a → ⋆Assoc (catC a) (h a) (g a) (f a)
  ΠC .isSetHom = isSetΠ (λ a → isSetHom (catC a))

  Π-intro : {D : Category ℓD ℓD'} → (∀ (a : A) → Functor D (catC a)) → Functor D ΠC
  Π-intro Fs .Functor.F-ob d a = Fs a ⟅ d ⟆
  Π-intro Fs .Functor.F-hom f a = Fs a ⟪ f ⟫
  Π-intro Fs .Functor.F-id = funExt (λ a → Fs a .F-id)
  Π-intro Fs .Functor.F-seq f g = funExt (λ a → Fs a .F-seq f g)

  πC : (a : A) → Functor ΠC (catC a)
  πC a .Functor.F-ob = λ xs → xs a
  πC a .Functor.F-hom = λ fs → fs a
  πC a .Functor.F-id = refl
  πC a .Functor.F-seq fs gs = refl
