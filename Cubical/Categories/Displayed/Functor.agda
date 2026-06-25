{-
  Definition of a functor displayed over another functor.
  Some definitions were guided by those at https://1lab.dev
-}
module Cubical.Categories.Displayed.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties

open import Cubical.Categories.Displayed.Base

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

Functorⱽ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
  → Type _
Functorⱽ = Functorᴰ Id

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
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open Functorᴰ

  -- TODO: move to Displayed.Constructions.Opposite
  introOpᴰ : ∀ {F} → Functorᴰ F (Cᴰ ^opᴰ) Dᴰ → Functorᴰ (introOp F) Cᴰ (Dᴰ ^opᴰ)
  introOpᴰ Fᴰ .F-obᴰ = Fᴰ .F-obᴰ
  introOpᴰ Fᴰ .F-homᴰ = Fᴰ .F-homᴰ
  introOpᴰ Fᴰ .F-idᴰ = Fᴰ .F-idᴰ
  introOpᴰ Fᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ

  recOpᴰ : ∀ {F} → Functorᴰ F Cᴰ (Dᴰ ^opᴰ) → Functorᴰ (recOp F) (Cᴰ ^opᴰ) Dᴰ
  recOpᴰ Fᴰ .F-obᴰ = Fᴰ .F-obᴰ
  recOpᴰ Fᴰ .F-homᴰ = Fᴰ .F-homᴰ
  recOpᴰ Fᴰ .F-idᴰ = Fᴰ .F-idᴰ
  recOpᴰ Fᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  toOpOpᴰ : Functorᴰ toOpOp Cᴰ ((Cᴰ ^opᴰ) ^opᴰ)
  toOpOpᴰ = introOpᴰ 𝟙ᴰ⟨ _ ⟩

  fromOpOpᴰ : Functorᴰ fromOpOp ((Cᴰ ^opᴰ) ^opᴰ) Cᴰ
  fromOpOpᴰ = recOpᴰ 𝟙ᴰ⟨ _ ⟩
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  _^opFᴰ : ∀ {F} → Functorᴰ F Cᴰ Dᴰ
                 → Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  Fᴰ ^opFᴰ = recOpᴰ (toOpOpᴰ ∘Fᴰ Fᴰ)

  _^opF⁻ᴰ : ∀ {F} → Functorᴰ F (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
                 → Functorᴰ (F ^opF⁻) Cᴰ Dᴰ
  Fᴰ ^opF⁻ᴰ = fromOpOpᴰ ∘Fᴰ introOpᴰ Fᴰ
