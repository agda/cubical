{-
   Local and Global Sections of a displayed category.

   A local section of a displayed category Cᴰ over a functor F : D → C
   is visualized as follows:

          Cᴰ
        ↗ |
       /  |
    s /   |
     /    |
    /     ↓
   D ---→ C
       F

   We call this a *global* section if F is the identity functor.

   Every Section can be implemented as a Functorᴰ out of Unitᴰ (see
   Displayed.Instances.Terminal):

       Fᴰ
   D ----→ Cᴰ
   ∥       |
   ∥       |
   ∥       |
   ∥       |
   ∥       ↓
   D ----→ C
       F

   And vice-versa any Functorᴰ

       Fᴰ
   Dᴰ ----→ Cᴰ
   |        |
   |        |
   |        |
   |        |
   ↓        ↓
   D -----→ C
       F

   Can be implemented as a Section (see
   Displayed.Constructions.TotalCategory)

            Cᴰ
          ↗ |
         /  |
      s /   |
       /    |
      /     ↓
   ∫Dᴰ ---→ C
        F

   Both options are sometimes more ergonomic. One of the main
   cosmetic differences is

   1. When defining a Functorᴰ, the object of the base category is
      implicit
   2. When defining a Section, the object of the base category is
      explicit

   Definitionally, there is basically no difference as these are
   definitional isomorphisms.

   Elimination rules are naturally stated in terms of local sections
   (and often global sections, see below). Intro rules can be
   formulated as either constructing a Section or a Functorᴰ. Good
   style is to offer both introS for Section and introF for Functorᴰ.

-}
module Cubical.Categories.Displayed.Section.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Equality
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor D C)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Categoryᴰ Cᴰ
    module F = Functor F

  -- Section without a qualifier means *local* section.
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC')
                        (ℓ-max (ℓ-max ℓD ℓD')
                        (ℓ-max ℓCᴰ ℓCᴰ')))
    where
    field
      F-obᴰ  : ∀ d → Cᴰ.ob[ F ⟅ d ⟆ ]
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F ⟪ f ⟫ ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.≡[ F .F-seq f g ] F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g

{-
   A Global Section is a local section over the identity functor.

          Cᴰ
        ↗ |
       /  |
    s /   |
     /    |
    /     ↓
   C ==== C


   So global sections are by definition local sections

   All local sections can be implemented as global sections into the
   reindexed displayed category. See Reindex.agda for details.

   But this isomorphism is not definitional (i.e. the equations are
   not provable by refl). Constructing a local section is preferable
   as they are more flexible, but often elimination principles are
   naturally proven first about global sections and then generalized
   to local sections using reindexing.

   It is good style is to offer both: elimLocal to construct a local
   section and elimGlobal to construct a global section.
-}

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  GlobalSection : Type _
  GlobalSection = Section Id Cᴰ

-- Reindexing a section.
module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  open Section
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ

  -- the following reindexes a section to be over a different functor
  -- that is equal to it, analogous to reind in Displayed.Reasoning.

  -- This version is easily defined by subst, but its action on
  -- objects and morphisms involves a transport, which is often
  -- undesirable.
  reindS : ∀ {F G}(H : Path (Functor D C) F G) → Section F Cᴰ → Section G Cᴰ
  reindS H = subst (λ F → Section F Cᴰ) H

  -- This version works by taking in a FunctorEq rather than a Path,
  -- meaning we can define the section by J. If the FunctorEq is given
  -- by (refl , refl) then this definition will not involve any
  -- transport and is preferable to reindS.
  reindS' : ∀ {F G : Functor D C} (H : FunctorEq F G)
          → Section F Cᴰ
          → Section G Cᴰ
  reindS' {F}{G} (H-ob , H-hom) Fᴰ = record
    { F-obᴰ = Gᴰ-obᴰ (F-singl .fst)
    ; F-homᴰ = Gᴰ-homᴰ F-singl
    ; F-idᴰ = Gᴰ-idᴰ F-singl (G .F-id)
    ; F-seqᴰ = Gᴰ-seqᴰ F-singl (G .F-seq)
    } where
      F-singl : FunctorSingl F
      F-singl = (_ , H-ob) , (_ , H-hom)

      Gᴰ-obᴰ : (G : Eq.singl (F .F-ob)) → (d : D .ob) → Cᴰ.ob[ G .fst d ]
      Gᴰ-obᴰ (_ , Eq.refl) = Fᴰ .F-obᴰ

      Gᴰ-homᴰ : (G : FunctorSingl F) → ∀ {d d'} (f : D [ d , d' ])
              → Cᴰ.Hom[ G .snd .fst f
                     ][ Gᴰ-obᴰ (G .fst) d
                      , Gᴰ-obᴰ (G .fst) d' ]
      Gᴰ-homᴰ ((_ , Eq.refl), (_ , Eq.refl)) = Fᴰ .F-homᴰ

      Gᴰ-idᴰ : (G : FunctorSingl F)
               (G-id : ∀ {x} → G .snd .fst (D .id {x}) ≡ C .id)
             →  ∀ {d} → Gᴰ-homᴰ G (D .id {d}) Cᴰ.≡[ G-id ] Cᴰ.idᴰ
      Gᴰ-idᴰ ((_ , Eq.refl), (_ , Eq.refl)) G-id = R.rectify (Fᴰ .F-idᴰ)

      Gᴰ-seqᴰ : (G : FunctorSingl F)
                (G-seq : ∀ {d d' d''}(f : D [ d , d' ])(g : D [ d' , d'' ])
                       → G .snd .fst (f ⋆⟨ D ⟩ g)
                       ≡ G .snd .fst f ⋆⟨ C ⟩ G .snd .fst g)
              → ∀ {d d' d'' : D .ob} (f : D [ d , d' ]) (g : D [ d' , d'' ])
              → Gᴰ-homᴰ G (f ⋆⟨ D ⟩ g)
                Cᴰ.≡[ G-seq f g ] (Gᴰ-homᴰ G f Cᴰ.⋆ᴰ Gᴰ-homᴰ G g)
      Gᴰ-seqᴰ ((_ , Eq.refl), (_ , Eq.refl)) G-seq f g =
        R.rectify (Fᴰ .F-seqᴰ f g)
{-

   Composition of a Section and a Functor

                 Cᴰ
               ↗ |
              /  |
           s /   |
            /    |
           /     ↓
   E ---→ D ---→ C
              F

-}
module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module R = HomᴰReasoning Dᴰ
  compSectionFunctor : Section F Dᴰ → (G : Functor B C) → Section (F ∘F G) Dᴰ
  compSectionFunctor Fᴰ G .F-obᴰ d     = Fᴰ .F-obᴰ (G .F-ob d)
  compSectionFunctor Fᴰ G .F-homᴰ f    = Fᴰ .F-homᴰ (G .F-hom f)
  compSectionFunctor Fᴰ G .F-idᴰ       = R.rectify $ R.≡out $
      R.≡in (cong (Fᴰ .F-homᴰ) (G .F-id))
    ∙ R.≡in (Fᴰ .F-idᴰ)
  compSectionFunctor Fᴰ G .F-seqᴰ f g = R.rectify $ R.≡out $
      R.≡in (cong (Fᴰ .F-homᴰ) (G .F-seq f g))
    ∙ R.≡in (Fᴰ .F-seqᴰ (G .F-hom f) (G .F-hom g))

module _ {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module R = HomᴰReasoning Dᴰ

  compGSectionFunctor : {C : Category ℓC ℓC'}
    → GlobalSection Dᴰ
    → (G : Functor C D)
    → Section G Dᴰ
  compGSectionFunctor s G = reindS' (Eq.refl , Eq.refl) (compSectionFunctor s G)
{-

  Composition of a Section and a Functorᴰ

              Fᴰ'
          Cᴰ ---→ Cᴰ'
        ↗ |       |
       /  |       |
    s /   |       |
     /    |       |
    /     ↓       ↓
   D ---→ C ----→ C'
       F     F'

-}
module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {G : Functor B C}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Functorᴰ
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Dᴰ
  compFunctorᴰSection : Functorᴰ F Cᴰ Dᴰ → Section G Cᴰ → Section (F ∘F G) Dᴰ
  compFunctorᴰSection Fᴰ Gᴰ .F-obᴰ d    = Fᴰ .F-obᴰ (Gᴰ .F-obᴰ d)
  compFunctorᴰSection Fᴰ Gᴰ .F-homᴰ f   = Fᴰ .F-homᴰ (Gᴰ .F-homᴰ f)
  compFunctorᴰSection Fᴰ Gᴰ .F-idᴰ      = R.rectify $ R.≡out $
      R.≡in (congP (λ _ → Fᴰ .F-homᴰ) (Gᴰ .F-idᴰ))
    ∙ R.≡in (Fᴰ .F-idᴰ)
  compFunctorᴰSection Fᴰ Gᴰ .F-seqᴰ f g = R.rectify $ R.≡out $
      R.≡in (congP (λ _ → Fᴰ .F-homᴰ) (Gᴰ .F-seqᴰ f g))
    ∙ R.≡in (Fᴰ .F-seqᴰ (Gᴰ .F-homᴰ f) (Gᴰ .F-homᴰ g))

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Functorᴰ
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Dᴰ

  compFunctorᴰGlobalSection : Functorᴰ F Cᴰ Dᴰ → GlobalSection Cᴰ → Section F Dᴰ
  compFunctorᴰGlobalSection Fᴰ Gᴰ = reindS' (Eq.refl , Eq.refl)
    (compFunctorᴰSection Fᴰ Gᴰ)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
          where

  open Section
  introOpS : ∀ {F : Functor (C ^op) _}
    → Section F Dᴰ
    → Section (introOp F) (Dᴰ ^opᴰ)
  introOpS S .F-obᴰ = S .F-obᴰ
  introOpS S .F-homᴰ = S .F-homᴰ
  introOpS S .F-idᴰ = S .F-idᴰ
  introOpS S .F-seqᴰ f g = S .F-seqᴰ g f

  recOpS : ∀ {F : Functor C _}
    → Section F (Dᴰ ^opᴰ)
    → Section (recOp F) Dᴰ
  recOpS S .F-obᴰ = S .F-obᴰ
  recOpS S .F-homᴰ = S .F-homᴰ
  recOpS S .F-idᴰ = S .F-idᴰ
  recOpS S .F-seqᴰ f g = S .F-seqᴰ g f

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
          where

  _^opS : ∀ {F : Functor C _} → Section F Dᴰ → Section (F ^opF) (Dᴰ ^opᴰ)
  S ^opS = recOpS (compFunctorᴰSection toOpOpᴰ S)

  _^opS⁻ : ∀ {F : Functor (C ^op) _}
    → Section F (Dᴰ ^opᴰ)
    → Section (F ^opF⁻) Dᴰ
  S ^opS⁻ = compFunctorᴰSection fromOpOpᴰ (introOpS S)
