{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.AdjointToReindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  open Category
  open Functor F
  private
    module Cᴰ = Categoryᴰ Cᴰ

    hom-path : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') → (D [ A , B ]) ≡ (D [ A' , B' ])
    hom-path p q = cong₂ (λ a b → D [ a , b ]) p q

    hom-pathP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                Type ℓD'
    hom-pathP p q f f' = PathP (λ i → hom-path p q i) f f'

  ∃F : Categoryᴰ D (ℓ-max (ℓ-max ℓC ℓD) ℓDᴰ) (ℓ-max (ℓ-max ℓC' ℓD') ℓDᴰ')
  ∃F .ob[_] d = Σ[ c ∈ C .ob ] (F-ob c ≡ d) × Cᴰ.ob[ c ]
  ∃F .Hom[_][_,_] f (c , p , x) (c' , p' , x') =
    Σ[ g ∈ C [ c , c' ] ] hom-pathP p p' (F-hom g) f × Cᴰ.Hom[ g ][ x , x' ]
  ∃F .idᴰ {d} {c , p , x} =
    (C .id) ,
    (F-id ◁ (cong (λ v → D .id {v}) p)) ,
    Cᴰ .idᴰ
  ∃F ._⋆ᴰ_ (g , p , gᴰ) (h , q , hᴰ) =
      g ⋆⟨ C ⟩ h ,
      F-seq g h ◁ (λ i → p i ⋆⟨ D ⟩ q i) ,
      (Cᴰ._⋆ᴰ_ gᴰ hᴰ)
  ⋆IdLᴰ ∃F {d}{d'}{g}{c , pc , xc}{c' , pc' , xc'} (f , p , x) =
    λ i →
      C .⋆IdL f i ,
      {!!} ,
      Cᴰ .⋆IdLᴰ x i
  ⋆IdRᴰ ∃F {d}{d'}{g}{c , pc , xc}{c' , pc' , xc'} (f , p , x) =
    λ i →
      C .⋆IdR f i ,
      {!!} ,
      Cᴰ .⋆IdRᴰ x i
  ⋆Assocᴰ ∃F = {!!}
  isSetHomᴰ ∃F {d}{d'}{f}{u}{v} =
    isSetΣ (C .isSetHom)
      λ g → isSet×
        (λ x y p q → isProp→isPropPathP
          (λ i → {!D .isSetHom {x = u .snd .fst i} {y = v .snd .fst i} (x i) (y i)!})
          x y p q)
        (Cᴰ .isSetHomᴰ)
