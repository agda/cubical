{-
  Definition of a functor displayed over another functor.
  Some definitions were guided by those at https://1lab.dev
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

record Functorᴰ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
  no-eta-equality

  open Category
  open Functor F
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  field
    F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F-ob x ]
    F-homᴰ : {x y : C .ob} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
    F-idᴰ : {x : C .ob} {xᴰ : Cᴰ.ob[ x ]}
      → F-homᴰ (Cᴰ.idᴰ {p = xᴰ}) Dᴰ.≡[ F-id {x} ] (Dᴰ.idᴰ {p = F-obᴰ xᴰ})
    F-seqᴰ : {x y z : C .ob} {f : C [ x , y ]} {g : C [ y , z ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
      (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ])
      → F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ) Dᴰ.≡[ F-seq f g ] F-homᴰ fᴰ Dᴰ.⋆ᴰ F-homᴰ gᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D} {H : F ≡ G}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  where

  open Category
  open Functor
  open Functorᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module Fᴰ = Functorᴰ Fᴰ
    module Gᴰ = Functorᴰ Gᴰ

  Functorᴰ≡ :
    (Hᴰ : {x : C .ob} (xᴰ : Cᴰ.ob[ x ]) → PathP (λ i → Dᴰ.ob[ H i ⟅ x ⟆ ]) (Fᴰ.F-obᴰ xᴰ) (Gᴰ.F-obᴰ xᴰ))
    → ({x y : C .ob} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
        → PathP (λ i → Dᴰ [ H i ⟪ f ⟫ ][ Hᴰ xᴰ i , Hᴰ yᴰ i ]) (Fᴰ.F-homᴰ fᴰ) (Gᴰ.F-homᴰ fᴰ))
    → PathP (λ i → Functorᴰ (H i) Cᴰ Dᴰ) Fᴰ Gᴰ
  Functorᴰ≡ Hᴰ α i .F-obᴰ xᴰ = Hᴰ xᴰ i
  Functorᴰ≡ Hᴰ α i .F-homᴰ fᴰ = α fᴰ i
  Functorᴰ≡ Hᴰ α i .F-idᴰ {xᴰ = xᴰ} =
    isProp→PathP
      {B = λ i → PathP (λ j → Dᴰ [ H i .F-id j ][ Hᴰ xᴰ i , Hᴰ xᴰ i ]) (α (Cᴰ.idᴰ) i) Dᴰ.idᴰ}
      (λ i → isOfHLevelPathP' 1 Dᴰ.isSetHomᴰ _ _)
      Fᴰ.F-idᴰ
      Gᴰ.F-idᴰ
      i
  Functorᴰ≡ Hᴰ α i .F-seqᴰ {f = f} {g = g} {xᴰ = xᴰ} {zᴰ = zᴰ} fᴰ gᴰ =
    isProp→PathP
      {B = λ i →
        PathP (λ j → Dᴰ [ H i .F-seq f g j ][ Hᴰ xᴰ i , Hᴰ zᴰ i ])
          (α (fᴰ Cᴰ.⋆ᴰ gᴰ) i) (α fᴰ i Dᴰ.⋆ᴰ α gᴰ i)}
      (λ i → isOfHLevelPathP' 1 Dᴰ.isSetHomᴰ _ _)
      (Fᴰ.F-seqᴰ fᴰ gᴰ)
      (Gᴰ.F-seqᴰ fᴰ gᴰ)
      i

-- Displayed identity functor

module _ where
  open Functorᴰ

  𝟙ᴰ⟨_⟩ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') → Functorᴰ 𝟙⟨ C ⟩ Cᴰ Cᴰ
  𝟙ᴰ⟨ Cᴰ ⟩ .F-obᴰ x    = x
  𝟙ᴰ⟨ Cᴰ ⟩ .F-homᴰ f   = f
  𝟙ᴰ⟨ Cᴰ ⟩ .F-idᴰ      = refl
  𝟙ᴰ⟨ Cᴰ ⟩ .F-seqᴰ _ _ = refl

-- Displayed functor composition

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : Functor C D} {G : Functor D E}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  open Functorᴰ
  private
    module Fᴰ = Functorᴰ Fᴰ
    module Gᴰ = Functorᴰ Gᴰ

  funcCompᴰ : Functorᴰ (funcComp G F) Cᴰ Eᴰ
  funcCompᴰ .F-obᴰ = Gᴰ.F-obᴰ ∘ Fᴰ.F-obᴰ
  funcCompᴰ .F-homᴰ = Gᴰ.F-homᴰ ∘ Fᴰ.F-homᴰ
  funcCompᴰ .F-idᴰ = compPathP' {B = Eᴰ [_][ _ , _ ]} (congP (λ _ → Gᴰ.F-homᴰ) Fᴰ.F-idᴰ) Gᴰ.F-idᴰ
  funcCompᴰ .F-seqᴰ _ _ =
    compPathP' {B = Eᴰ [_][ _ , _ ]} (congP (λ _ → Gᴰ.F-homᴰ) (Fᴰ.F-seqᴰ _ _) ) (Gᴰ.F-seqᴰ _ _)

_∘Fᴰ_ = funcCompᴰ

-- Displayed functor associativity

F-assocᴰ : {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : Functor B C} {G : Functor C D} {H : Functor D E}
  {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {Fᴰ : Functorᴰ F Bᴰ Cᴰ} {Gᴰ : Functorᴰ G Cᴰ Dᴰ} {Hᴰ : Functorᴰ H Dᴰ Eᴰ}
  → PathP (λ i → Functorᴰ (F-assoc {F = F} {G = G} {H = H} i) Bᴰ Eᴰ) (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ)) ((Hᴰ ∘Fᴰ Gᴰ) ∘Fᴰ Fᴰ)
F-assocᴰ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)

-- Displayed functor unit laws

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Fᴰ : Functorᴰ F Cᴰ Dᴰ} where

  open Functorᴰ
  private
    module Fᴰ = Functorᴰ Fᴰ

  F-lUnitᴰ : PathP (λ i → Functorᴰ (F-lUnit {F = F} i) Cᴰ Dᴰ) (Fᴰ ∘Fᴰ 𝟙ᴰ⟨ Cᴰ ⟩) Fᴰ
  F-lUnitᴰ i .F-obᴰ x = Fᴰ.F-obᴰ x
  F-lUnitᴰ i .F-homᴰ f = Fᴰ.F-homᴰ f
  F-lUnitᴰ i .F-idᴰ {x} =  lUnitP' (Dᴰ [_][ _ , _ ]) Fᴰ.F-idᴰ (~ i)
  F-lUnitᴰ i .F-seqᴰ f g = lUnitP' (Dᴰ [_][ _ , _ ]) (Fᴰ.F-seqᴰ _ _) (~ i)

  F-rUnitᴰ : PathP (λ i → Functorᴰ (F-rUnit {F = F} i) Cᴰ Dᴰ) (𝟙ᴰ⟨ Dᴰ ⟩ ∘Fᴰ Fᴰ) Fᴰ
  F-rUnitᴰ i .F-obᴰ x = Fᴰ.F-obᴰ x
  F-rUnitᴰ i .F-homᴰ f = Fᴰ.F-homᴰ f
  F-rUnitᴰ i .F-idᴰ {x} = rUnitP' (Dᴰ [_][ _ , _ ]) Fᴰ.F-idᴰ (~ i)
  F-rUnitᴰ i .F-seqᴰ _ _ = rUnitP' (Dᴰ [_][ _ , _ ]) (Fᴰ.F-seqᴰ _ _) (~ i)

-- Displayed opposite functor
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFᴰ : Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFᴰ .F-obᴰ = Fᴰ .F-obᴰ
  _^opFᴰ .F-homᴰ = Fᴰ .F-homᴰ
  _^opFᴰ .F-idᴰ = Fᴰ .F-idᴰ
  _^opFᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ


-- Total functor of a displayed functor
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  open Functor
  private
    module Fᴰ = Functorᴰ Fᴰ

  ∫F : Functor (∫C Cᴰ) (∫C Dᴰ)
  ∫F .F-ob (x , xᴰ) = _ , Fᴰ.F-obᴰ xᴰ
  ∫F .F-hom (_ , fᴰ) = _ , Fᴰ.F-homᴰ fᴰ
  ∫F .F-id = ΣPathP (_ , Fᴰ.F-idᴰ)
  ∫F .F-seq _ _ = ΣPathP (_ , (Fᴰ.F-seqᴰ _ _))

-- Projections out of the total category
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  -- Functor into the total category
  module _ {D : Category ℓD ℓD'}
           (F : Functor D C)
           (Fᴰ : Functorᴰ F (Unitᴰ D) Cᴰ)
           where
    mk∫Functor : Functor D (∫C Cᴰ)
    mk∫Functor .F-ob d = F ⟅ d ⟆ , Fᴰ .F-obᴰ _
    mk∫Functor .F-hom f = (F ⟪ f ⟫) , (Fᴰ .F-homᴰ _)
    mk∫Functor .F-id = ΣPathP (F .F-id , Fᴰ .F-idᴰ)
    mk∫Functor .F-seq f g = ΣPathP (F .F-seq f g , Fᴰ .F-seqᴰ _ _)

-- Projection out of the displayed total category
module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Functorᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  -- Functor into the displayed total category
  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
           (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
           (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Dᴰ)
           where

    mk∫ᴰFunctorᴰ : Functorᴰ F Eᴰ (∫Cᴰ Cᴰ Dᴰ)
    mk∫ᴰFunctorᴰ .F-obᴰ xᴰ = Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ _
    mk∫ᴰFunctorᴰ .F-homᴰ fᴰ = (Fᴰ .F-homᴰ fᴰ) , (Gᴰ .F-homᴰ _)
    mk∫ᴰFunctorᴰ .F-idᴰ = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    mk∫ᴰFunctorᴰ .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ .F-seqᴰ fᴰ gᴰ , Gᴰ .F-seqᴰ _ _)
