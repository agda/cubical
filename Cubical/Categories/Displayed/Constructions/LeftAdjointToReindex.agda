--
module Cubical.Categories.Displayed.Constructions.LeftAdjointToReindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Weaken.Base
open import Cubical.Categories.Constructions.TotalCategory

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
    open Iso

    hom-path : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
      (D [ A , B ]) ≡ (D [ A' , B' ])
    hom-path p q = cong₂ (λ a b → D [ a , b ]) p q

    hom-pathP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                Type ℓD'
    hom-pathP p q f f' = PathP (λ i → hom-path p q i) f f'

    isPropHomP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                isProp (hom-pathP p q f f')
    isPropHomP pdom pcod f f'' x y =
      isoFunInjective (PathPIsoPath _ _ _) x y fromPathPeq
      where
      fromPathPeq : fromPathP x ≡ fromPathP y
      fromPathPeq = D .isSetHom _ _ (fromPathP x) (fromPathP y)

  -- Reindexing a displayed category Dᴰ over D along a functor F : C → D
  -- gives a displayed category over C
  -- Fiberwise pullback the objects over D along F to display them over C
  --
  --    reindex Dᴰ F                Dᴰ
  --         _                      _
  --         |                      |
  --         v           F          v
  --         C -------------------> D
  --
  -- Which may be read as a 2-functor from displayed categories over D to
  -- displayed categories over C. This operation has a left 2-adjoint, which
  -- we call ∃F, that maps displays over C to displays over D
  --
  --         Cᴰ                  ∃F Cᴰ F
  --         _                      _
  --         |                      |
  --         v           F          v
  --         C -------------------> D
  --
  ∃F : Categoryᴰ D (ℓ-max (ℓ-max ℓC ℓD) ℓDᴰ) (ℓ-max (ℓ-max ℓC' ℓD') ℓDᴰ')
  ∃F .ob[_] d = Σ[ c ∈ C .ob ]  Cᴰ.ob[ c ] × (F-ob c ≡ d)
  ∃F .Hom[_][_,_] f (c , x , p) (c' , x' , p') =
    Σ[ g ∈ C [ c , c' ] ] Cᴰ.Hom[ g ][ x , x' ] × hom-pathP p p' (F-hom g) f
  ∃F .idᴰ {d} {c , x , p} =
    C .id ,
    Cᴰ .idᴰ ,
    (F-id ◁ (cong (λ v → D .id {v}) p))
  ∃F ._⋆ᴰ_ (g , gᴰ , p) (h , hᴰ , q) =
      g ⋆⟨ C ⟩ h ,
      (Cᴰ._⋆ᴰ_ gᴰ hᴰ) ,
      (F-seq g h ◁ congP₂ (λ _ a b → a ⋆⟨ D ⟩ b) p q)
  ⋆IdLᴰ ∃F (f , x , p) =
    ΣPathP (C .⋆IdL f , ΣPathPProp (λ _ → isPropHomP _ _ _ _) (Cᴰ .⋆IdLᴰ x))
  ⋆IdRᴰ ∃F (f , x , p) =
    ΣPathP (C .⋆IdR f , ΣPathPProp (λ _ → isPropHomP _ _ _ _) (Cᴰ .⋆IdRᴰ x))
  ⋆Assocᴰ ∃F
    (f , pf , fᴰ)
    (g , pg , gᴰ)
    (h , ph , hᴰ) =
    ΣPathP (C .⋆Assoc _ _ _ ,
      ΣPathPProp (λ _ → isPropHomP _ _ _ _) (Cᴰ .⋆Assocᴰ _ _ _))
  isSetHomᴰ ∃F {d}{d'}{f}{u}{v} =
    isSetΣ (C .isSetHom)
      (λ g → isSet× (Cᴰ .isSetHomᴰ) (isProp→isSet (isPropHomP _ _ _ _)))

-- Examples of ∃F instantiated
private
  module _ where
    -- Can define the displayed total category via ∃F
    module _
      {C : Category ℓC ℓC'}
      {ℓ : Level}
      (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
      (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
      where
      ∫Cᴰ' : Categoryᴰ C
        (ℓ-max (ℓ-max (ℓ-max ℓC ℓCᴰ) ℓC) ℓDᴰ)
        (ℓ-max (ℓ-max (ℓ-max ℓC' ℓCᴰ') ℓC') ℓDᴰ')
      ∫Cᴰ' = ∃F Dᴰ (Fst {C = C} {Cᴰ = Cᴰ})

    module _
      {C : Category ℓC ℓC'}
      {D : Category ℓD ℓD'}
      {ℓ : Level}
      (F : Functor (TerminalCategory {ℓ-zero}) C)
      (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
      (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
      where

      weaken' : Categoryᴰ C (ℓ-max (ℓ-max ℓ-zero ℓC) ℓD)
                 (ℓ-max (ℓ-max ℓ-zero ℓC') ℓD')
      weaken' = ∃F (weaken _ D) F
