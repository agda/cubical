{-# OPTIONS --safe --lossy-unification #-}
{--
 -- Functor Comprehension
 -- ======================
 -- This module provides a method for constructing functors without
 -- providing the full functorial structure up front.
 --
 -- The idea is that if you wish to define a functor F : C → D, via
 -- some universal property P. Instead of doing this process entirely
 -- manually, you can prove the functoriality of the universal property P
 -- and give for each c ∈ C some object F c ∈ D satisfying the property
 -- P c.
 --
 -- Conveniently, we need only provide an explicit action on objects. The
 -- functoriality of P induces a unique action on morphisms.
 --
 -- Putting all of this together, the action on objects can then
 -- uniquely be extended functorially to a functor F : C → D.
 --
 -- Constructing a functor in this method saves a lot of work in
 -- repeatedly demonstrating functoriality
 --
 --}
module Cubical.Categories.Functor.Comprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.DisplayOverProjections
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open NatIso
open NatTrans

module _ (D : Category ℓD ℓD') (ℓS : Level) where
  private
    𝓟 = PresheafCategory D ℓS
    𝓟' = PresheafCategory D (ℓ-max ℓS ℓD')

  -- Presheaves that have a universal element viewed as property
  -- (morphisms ignore it).
  --
  -- A functor C → 𝓟up is equivalent to a functor R : C → 𝓟 and a
  -- universal element for each R ⟅ c ⟆
  --
  -- An object over P is a universal element
  -- Morphisms over nat trans. are trivial
  𝓟up : Categoryᴰ 𝓟 (ℓ-max (ℓ-max ℓD ℓD') ℓS) ℓ-zero
  𝓟up = FullSubcategoryᴰ 𝓟 (UniversalElement D)

  hasContrHoms𝓟up : hasContrHoms 𝓟up
  hasContrHoms𝓟up = hasContrHomsFullSubcategory _ _

  App : D o-[ ℓS ]-* 𝓟
  App = Profunctor→Relator Id

  𝓟elt : Categoryᴰ 𝓟 _ _
  𝓟elt = ∫Cᴰsl (Graph App)

  𝓟usᴰ : Categoryᴰ (∫C 𝓟elt) _ _
  𝓟usᴰ = FullSubcategoryᴰ _
     (λ elt → isUniversal D (elt .fst)
                            (elt .snd .fst)
                            (elt .snd .snd))

  -- Presheaves equipped with a universal element as structure
  -- (morphisms preserve it)
  --
  -- A functor C → 𝓟us is the data of
  -- 1. A functor R : C → 𝓟
  -- 2. A functor F : C → D

  -- 3. A *natural* choice of elements for R c (F c) with F c as
  --    vertex
  --
  -- An object over P is a universal element η
  --
  -- Morphisms over nat trans α : P , η → Q , η' are morphisms
  -- f : η .vertex → η' .vertex
  -- That that "represent" α.
  -- Since η, η' are universal, this type is contractible.
  𝓟us : Categoryᴰ 𝓟 _ _
  𝓟us = ∫Cᴰ 𝓟elt 𝓟usᴰ

  -- | TODO: this should be definable as some composition of
  -- | reassociativity and projection but need to implement those
  -- | functors
  ForgetUniversal : Functor (∫C 𝓟us) (∫C (Graph App))
  ForgetUniversal .F-ob x =
    ((x .snd .fst .fst) , (x .fst)) , (x .snd .fst .snd)
  ForgetUniversal .F-hom α =
    ((α .snd .fst .fst) , (α .fst)) , (α .snd .fst .snd)
  ForgetUniversal .F-id = refl
  ForgetUniversal .F-seq _ _ = refl

  𝓟us→D : Functor (∫C 𝓟us) D
  𝓟us→D = π₁ App ∘F ForgetUniversal

  hasContrHoms𝓟us : hasContrHoms 𝓟us
  hasContrHoms𝓟us {c' = Q} α ((d , η) , univ) ((d' , η') , univ') =
    (((ue'.intro ((α ⟦ _ ⟧) η)) , ue'.β) , _)
    , λ ((g , sq) , tt) → Σ≡Prop (λ _ → isPropUnit)
      (Σ≡Prop (λ _ → (Q ⟅ _ ⟆) .snd _ _)
      (sym (ue'.η ∙ cong ue'.intro sq)))
    where
      module ue  = UniversalElementNotation
        (record { vertex = d ; element = η ; universal = univ })
      module ue' = UniversalElementNotation
        (record { vertex = d' ; element = η' ; universal = univ' })

  coherence : Functorᴰ Id 𝓟up 𝓟us
  coherence = mkFunctorᴰContrHoms hasContrHoms𝓟us
    (λ ue → (ue .vertex , (ue .element)) , (ue .universal))

  -- Presheaves equipped with a representation viewed as
  -- structure
  --
  -- A functor C → 𝓟rs is the data of
  -- 1. A functor R : C → 𝓟
  -- 2. A functor F : C → D
  -- 3. A natural iso LiftF ∘F R ≅ LiftF ∘F Yo ∘F F
  --
  -- An object over P is an iso P ≅ Yo c
  --
  -- Morphisms over nat trans α : P , iso → Q , iso' are morphisms
  -- f : iso .cod → iso' .cod
  -- That that commute: iso' ∘ Yo f ≡ α ∘ iso
  -- because Yo is fully faithful, this is contractible.
  private
    LiftPsh = (postcomposeF (D ^op) (LiftF {ℓS}{ℓD'}))
    YO* = (postcomposeF (D ^op) (LiftF {ℓD'}{ℓS}) ∘F YO)

  𝓟r : Categoryᴰ 𝓟 _ _
  𝓟r = IsoCommaᴰ₁ LiftPsh YO*

  open Functorᴰ

  𝓟us→𝓟r : Functorᴰ Id 𝓟us 𝓟r
  𝓟us→𝓟r =
    mk∫ᴰsrFunctorᴰ
      _
      Id
      𝓟us→Weaken𝓟D
      Unitᴰ∫C𝓟us→IsoCommaᴰ
    where
    𝓟us→Weaken𝓟D : Functorᴰ Id 𝓟us (weaken 𝓟 D)
    𝓟us→Weaken𝓟D .F-obᴰ xᴰ = xᴰ .fst .fst
    𝓟us→Weaken𝓟D .F-homᴰ fᴰ = fᴰ .fst .fst
    𝓟us→Weaken𝓟D .F-idᴰ = refl
    𝓟us→Weaken𝓟D .F-seqᴰ _ _ = refl

    Unitᴰ∫C𝓟us→IsoCommaᴰ :
      Functorᴰ (∫F 𝓟us→Weaken𝓟D) _ _
    Unitᴰ∫C𝓟us→IsoCommaᴰ = mkFunctorᴰPropHoms (hasPropHomsIsoCommaᴰ _ _)
      (λ {(P , ((vert , elt) , isUniversal))} tt →
        let open UniversalElementNotation (record { vertex = vert ;
                                                    element = elt ;
                                                    universal = isUniversal })
        in NatIso→FUNCTORIso _ _ introNI)
      λ {(P , ((vertP , eltP) , isUniversalP))
        ((Q , ((vertQ , eltQ) , isUniversalQ))) (α , ((f , sq) , tt)) _ _} tt →
        let module ueP = UniversalElementNotation (record {
                                                    vertex = vertP ;
                                                    element = eltP ;
                                                    universal = isUniversalP })
            module ueQ = UniversalElementNotation (record {
                                                    vertex = vertQ ;
                                                    element = eltQ ;
                                                    universal = isUniversalQ })
        in
        -- The goal is
        -- α ⋆ ueQ.introNI .trans ≡ ueP.introNI .trans ⋆ Yo* ⟪ f ⟫
        -- It is easier to prove in the equivalent form
        -- inv ueP.introNI ⋆ α ≡ Yo* ⟪ f ⟫ ⋆ inv ueQ.introNI
        sym (⋆InvsFlipSq⁻ {C = 𝓟'} (NatIso→FUNCTORIso _ _ ueP.introNI)
          {LiftPsh ⟪ α ⟫}{YO* ⟪ f ⟫} (NatIso→FUNCTORIso _ _ ueQ.introNI)
          (makeNatTransPath (funExt λ d → funExt λ (lift g) → cong lift
            (funExt⁻ (Q .F-seq _ _) eltQ
            ∙ cong (Q .F-hom g) sq
            ∙ sym (funExt⁻ (α .N-hom _) _)))))
        , tt

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {P : Profunctor C D ℓS}
         (ues : UniversalElements P)
         where
  private
    Pup : Functor C (∫C (𝓟up D ℓS))
    Pup = mk∫Functor P (mkFullSubcategoryᴰFunctorᴰ _ _ _ (λ _ → ues _))

    Pus : Functor C (∫C (𝓟us D ℓS))
    Pus = ∫F (coherence D ℓS) ∘F Pup

    Pr : Functor C (∫C (𝓟r D ℓS))
    Pr = ∫F (𝓟us→𝓟r D ℓS) ∘F Pus

    P-elt : Functor C (∫C (Graph (App D ℓS)))
    P-elt = ForgetUniversal D ℓS ∘F Pus

    -- We define R (d , c) := P c d
    R = Profunctor→Relator P

  FunctorComprehension : Functor C D
  FunctorComprehension = π₁ (App D ℓS) ∘F P-elt

  -- The profunctor here is definitionally iso to R(F -, =), as we see below
  counit-elt' : NatElt ((App D ℓS) ∘Flr ((π₁ (App D ℓS) ^opF) ,
                        π₂ (App D ℓS)) ∘Flr ((P-elt ^opF) , P-elt))
  counit-elt' = whisker (πElt (App D ℓS)) P-elt

  open NatElt
  -- ∀ c . R (F ⟅ c ⟆) c, naturally
  counit-elt : NatElt (R ∘Fl (FunctorComprehension ^opF))
  counit-elt .N-ob = counit-elt' .N-ob
  counit-elt .N-hom× = counit-elt' .N-hom×
  counit-elt .N-ob-hom×-agree = counit-elt' .N-ob-hom×-agree
  counit-elt .N-natL = counit-elt' .N-natL
  counit-elt .N-natR = counit-elt' .N-natR

  private
    -- Test to show that counit-elt matches the original universal element

    -- This demonstrates that the selection of universal elements is
    -- natural with respect to the functorial action constructed from
    -- universality
    test-counit-elt-def : ∀ c → counit-elt .N-ob c ≡ ues c .element
    test-counit-elt-def c = refl

    LiftPsh = (postcomposeF (D ^op) (LiftF {ℓS}{ℓD'}))
    YO* = (postcomposeF (D ^op) (LiftF {ℓD'}{ℓS}) ∘F YO)

    ReAssoc : Functor (∫C (𝓟r D ℓS)) (IsoComma LiftPsh YO*)
    ReAssoc = Assoc-sr⁻ (IsoCommaᴰ LiftPsh YO*)

    P-iso : Functor C (∫C (IsoCommaᴰ LiftPsh YO*))
    P-iso =
      Assoc-sr⁻ (IsoCommaᴰ LiftPsh YO*)
      ∘F ∫F (𝓟us→𝓟r D ℓS)
      ∘F Pus

  ProfIso' : NatIso _ _
  ProfIso' = π≅ LiftPsh YO* ∘ˡⁱ P-iso

  ProfIso : NatIso (LiftPsh ∘F P) (YO* ∘F FunctorComprehension)
  ProfIso .trans .N-ob = ProfIso' .trans .N-ob
  ProfIso .trans .N-hom = ProfIso' .trans .N-hom
  ProfIso .nIso = ProfIso' .nIso
