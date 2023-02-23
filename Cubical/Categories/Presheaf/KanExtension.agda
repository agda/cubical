{-# OPTIONS --safe --lossy-unification #-}

{-
  Kan extension of a functor C → D to a functor PresheafCategory C ℓ → PresheafCategory D ℓ
  left or right adjoint to precomposition.
-}

module Cubical.Categories.Presheaf.KanExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SetQuotients

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

{-
  Left Kan extension of a functor C → D to a functor PresheafCategory C ℓ → PresheafCategory D ℓ
  left adjoint to precomposition.
-}

module Lan {ℓC ℓC' ℓD ℓD'} ℓS
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  private
    module C = Category C
    module D = Category D

    {-
      We want the category SET ℓ we're mapping into to be large enough that the coend will take presheaves
      Cᵒᵖ → Set ℓ to presheaves Dᵒᵖ → Set ℓ, otherwise we get no adjunction with precomposition.
      So we must have ℓC,ℓC',ℓD' ≤ ℓ; the parameter ℓS allows ℓ to be larger than their maximum.
    -}
    ℓ = ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS

  module _ (G : Functor (C ^op) (SET ℓ)) where

    -- Definition of the coend

    module _ (d : D.ob) where

      Raw : Type ℓ
      Raw = Σ[ c ∈ C.ob ] Σ[ g ∈ D.Hom[ d , F ⟅ c ⟆ ] ] G .F-ob c .fst

      data _≈_ : (u v : Raw) → Type ℓ where
        shift : {c c' : C.ob} (g : D.Hom[ d , F ⟅ c ⟆ ]) (f : C.Hom[ c , c' ]) (a : (G ⟅ c' ⟆) .fst)
          → (c' , (g D.⋆ F ⟪ f ⟫) , a) ≈ (c , g , (G ⟪ f ⟫) a)

      Quo = Raw / _≈_

    pattern shift/ g f a i = eq/ _ _ (shift g f a) i

    -- Action of Quo on arrows in D

    mapR : {d d' : D.ob} (h : D.Hom[ d' , d ]) → Quo d → Quo d'
    mapR h [ c , g , a ] = [ c , h D.⋆ g , a ]
    mapR h (shift/ g f a i) =
      hcomp
        (λ j → λ
          { (i = i0) → [ _ , D.⋆Assoc h g (F ⟪ f ⟫) j , a ]
          ; (i = i1) → [ _ , h D.⋆ g , (G ⟪ f ⟫) a ]
          })
        (shift/ (h D.⋆ g) f a i)
    mapR h (squash/ t u p q i j) =
      squash/ (mapR h t) (mapR h u) (cong (mapR h) p) (cong (mapR h) q) i j

    mapRId : (d : D.ob) → mapR (D.id {x = d}) ≡ idfun (Quo d)
    mapRId d =
      funExt (elimProp (λ _ → squash/ _ _) (λ (c , g , a) i → [ c , D.⋆IdL g i , a ]))

    mapR∘ : {d d' d'' : D.ob}
      (h' : D.Hom[ d'' , d' ]) (h : D.Hom[ d' , d ])
      → mapR (h' D.⋆ h) ≡ mapR h' ∘ mapR h
    mapR∘ h' h =
      funExt (elimProp (λ _ → squash/ _ _) (λ (c , g , a) i → [ c , D.⋆Assoc h' h g i , a ]))

  LanOb : Functor (C ^op) (SET ℓ) → Functor (D ^op) (SET _)
  LanOb G .F-ob d .fst = Quo G d
  LanOb G .F-ob d .snd = squash/
  LanOb G .F-hom = mapR G
  LanOb G .F-id {d} = mapRId G d
  LanOb G .F-seq h h' = mapR∘ G h' h

  -- Action of Quo on arrows in Cᵒᵖ → Set

  module _ {G G' : Functor (C ^op) (SET ℓ)} (α : NatTrans G G') where

    mapL : (d : D.ob) → Quo G d → Quo G' d
    mapL d [ c , g , a ] = [ c , g , α .N-ob c a ]
    mapL d (shift/ g f a i) =
      hcomp
        (λ j → λ
          { (i = i0) → [ _ , (g D.⋆ F ⟪ f ⟫) , α .N-ob _ a ]
          ; (i = i1) → [ _ , g , funExt⁻ (α .N-hom f) a (~ j) ]
          })
        (shift/ g f ((α ⟦ _ ⟧) a) i)
    mapL d (squash/ t u p q i j) =
      squash/ (mapL d t) (mapL d u) (cong (mapL d) p) (cong (mapL d) q) i j

    mapLR : {d d' : D.ob} (h : D.Hom[ d' , d ])
      → mapL d' ∘ mapR G h ≡ mapR G' h ∘ mapL d
    mapLR h = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  mapLId : (G : Functor (C ^op) (SET ℓ))
    (d : D.ob) → mapL (idTrans G) d ≡ idfun (Quo G d)
  mapLId G d = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  mapL∘ : {G G' G'' : Functor (C ^op) (SET ℓ)}
    (β : NatTrans G' G'') (α : NatTrans G G')
    (d : D.ob) → mapL (seqTrans α β) d ≡ mapL β d ∘ mapL α d
  mapL∘ β α d = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  LanHom : {G G' : Functor (C ^op) (SET ℓ)}
    → NatTrans G G' → NatTrans (LanOb G) (LanOb G')
  LanHom α .N-ob = mapL α
  LanHom α .N-hom = mapLR α

  -- Definition of the left Kan extension functor

  Lan : Functor (FUNCTOR (C ^op) (SET ℓ)) (FUNCTOR (D ^op) (SET ℓ))
  Lan .F-ob = LanOb
  Lan .F-hom = LanHom
  Lan .F-id {G} = makeNatTransPath (funExt (mapLId G))
  Lan .F-seq α β = makeNatTransPath (funExt (mapL∘ β α))

  -- Adjunction between the left Kan extension and precomposition

  private
    F* = precomposeF (SET ℓ) (F ^opF)

  open UnitCounit

  η : 𝟙⟨ FUNCTOR (C ^op) (SET ℓ) ⟩ ⇒ funcComp F* Lan
  η .N-ob G .N-ob c a = [ c , D.id , a ]
  η .N-ob G .N-hom {c'} {c} f =
    funExt λ a →
    [ c , D.id , (G ⟪ f ⟫) a ]
      ≡⟨ sym (shift/ D.id f a) ⟩
    [ c' , (D.id D.⋆ F ⟪ f ⟫) , a ]
      ≡[ i ]⟨ [ c' , lem i , a ] ⟩
    [ c' , (F ⟪ f ⟫ D.⋆ D.id) , a ]
    ∎
    where
    lem : D.id D.⋆ F ⟪ f ⟫ ≡ F ⟪ f ⟫ D.⋆ D.id
    lem = D.⋆IdL (F ⟪ f ⟫) ∙ sym (D.⋆IdR (F ⟪ f ⟫))
  η .N-hom f = makeNatTransPath refl

  ε : funcComp Lan F* ⇒ 𝟙⟨ FUNCTOR (D ^op) (SET ℓ) ⟩
  ε .N-ob H .N-ob d =
    elim
      (λ _ → (H ⟅ d ⟆) .snd)
      (λ (c , g , a) → (H ⟪ g ⟫) a)
      (λ {_ _ (shift g f a) i → H .F-seq (F ⟪ f ⟫) g i a})
  ε .N-ob H .N-hom g' =
    funExt (elimProp (λ _ → (H ⟅ _ ⟆) .snd _ _) (λ (c , g , a) → funExt⁻ (H .F-seq g g') a))
  ε .N-hom {H} {H'} α =
    makeNatTransPath
      (funExt₂ λ d →
         elimProp (λ _ → (H' ⟅ _ ⟆) .snd _ _)
          (λ (c , g , a) → sym (funExt⁻ (α .N-hom g) a)))

  Δ₁ : ∀ G → seqTrans (Lan ⟪ η ⟦ G ⟧ ⟫) (ε ⟦ Lan ⟅ G ⟆ ⟧) ≡ idTrans _
  Δ₁ G =
    makeNatTransPath
      (funExt₂ λ d →
        elimProp (λ _ → squash/ _ _)
          (λ (c , g , a) →
            [ c , g D.⋆ D.id , a ]
              ≡[ i ]⟨ [ c , (g D.⋆ F .F-id (~ i)) , a ] ⟩
            [ c , g D.⋆ (F ⟪ C.id ⟫) , a ]
              ≡⟨ shift/ g C.id a ⟩
            [ c , g , (G ⟪ C.id ⟫) a ]
              ≡[ i ]⟨ [ c , g , G .F-id i a ] ⟩
            [ c , g , a ]
            ∎))

  Δ₂ : ∀ H → seqTrans (η ⟦ F* ⟅ H ⟆ ⟧) (F* ⟪ ε ⟦ H ⟧ ⟫) ≡ idTrans _
  Δ₂ H = makeNatTransPath (funExt λ c → H .F-id)

  adj : Lan ⊣ F*
  adj ._⊣_.η = η
  adj ._⊣_.ε = ε
  adj ._⊣_.Δ₁ = Δ₁
  adj ._⊣_.Δ₂ = Δ₂

{-
  Right Kan extension of a functor C → D to a functor PresheafCategory C ℓ → PresheafCategory D ℓ
  right adjoint to precomposition.
-}

module Ran {ℓC ℓC' ℓD ℓD'} ℓS
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  private
    module C = Category C
    module D = Category D

    {-
      We want the category SET ℓ we're mapping into to be large enough that the coend will take presheaves
      Cᵒᵖ → Set ℓ to presheaves Dᵒᵖ → Set ℓ, otherwise we get no adjunction with precomposition.
      So we must have ℓC,ℓC',ℓD' ≤ ℓ; the parameter ℓS allows ℓ to be larger than their maximum.
    -}
    ℓ = ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS

  module _ (G : Functor (C ^op) (SET ℓ)) where

    -- Definition of the end

    record End (d : D.ob) : Type ℓ where
      field
        fun : (c : C.ob) (g : D.Hom[ F ⟅ c ⟆ , d ]) → G .F-ob c .fst
        coh : {c c' : C.ob} (f : C.Hom[ c , c' ]) (g : D.Hom[ F ⟅ c' ⟆ , d ])
          → fun c (F ⟪ f ⟫ ⋆⟨ D ⟩ g) ≡ (G ⟪ f ⟫) (fun c' g)

    open End

    end≡ : {d : D.ob} {x x' : End d} → (∀ c g → x .fun c g ≡ x' .fun c g) → x ≡ x'
    end≡ h i .fun c g = h c g i
    end≡ {_} {x} {x'} h i .coh f g =
      isSet→isSet' (G .F-ob _ .snd)
        (x .coh f g)
        (x' .coh f g)
        (h _ (F ⟪ f ⟫ ⋆⟨ D ⟩ g))
        (cong (G ⟪ f ⟫) (h _ g))
        i

    -- Action of End on arrows in D

    mapR : {d d' : D.ob} (h : D.Hom[ d' , d ]) → End d → End d'
    mapR h x .fun c g = x .fun c (g ⋆⟨ D ⟩ h)
    mapR h x .coh f g = cong (x .fun _) (D.⋆Assoc (F ⟪ f ⟫) g h) ∙ x .coh f (g ⋆⟨ D ⟩ h)

    mapRId : (d : D.ob) → mapR (D.id {x = d}) ≡ idfun (End d)
    mapRId h = funExt λ x → end≡ λ c g → cong (x .fun c) (D.⋆IdR g)

    mapR∘ : {d d' d'' : D.ob}
      (h' : D.Hom[ d'' , d' ]) (h : D.Hom[ d' , d ])
      → mapR (h' D.⋆ h) ≡ mapR h' ∘ mapR h
    mapR∘ h' h = funExt λ x → end≡ λ c g → cong (x .fun c) (sym (D.⋆Assoc g h' h))

  open End

  RanOb : Functor (C ^op) (SET ℓ) → Functor (D ^op) (SET _)
  RanOb G .F-ob d .fst = End G d
  RanOb G .F-ob d .snd =
    -- We use that End is equivalent to a Σ-type to prove its HLevel more easily
    isOfHLevelRetract 2
      {B =
        Σ[ z ∈ ((c : C.ob) (g : D.Hom[ F ⟅ c ⟆ , d ]) → G .F-ob c .fst) ]
        ({c c' : C.ob} (f : C.Hom[ c , c' ]) (g : D.Hom[ F ⟅ c' ⟆ , d ])
          → z c (F ⟪ f ⟫ ⋆⟨ D ⟩ g) ≡ (G ⟪ f ⟫) (z c' g))
      }
      (λ x → λ where .fst → x .fun; .snd → x .coh)
      (λ σ → λ where .fun → σ .fst; .coh → σ .snd)
      (λ _ → refl)
      (isSetΣ
        (isSetΠ2 λ _ _ → G .F-ob _ .snd)
        (λ _ → isProp→isSet
          (isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ2 λ _ _ → G .F-ob _ .snd _ _)))
  RanOb G .F-hom = mapR G
  RanOb G .F-id {d} = mapRId G d
  RanOb G .F-seq h h' = mapR∘ G h' h

  -- Action of End on arrows in Cᵒᵖ → Set

  module _ {G G' : Functor (C ^op) (SET ℓ)} (α : NatTrans G G') where

    mapL : (d : D.ob) → End G d → End G' d
    mapL d x .fun c g = (α ⟦ c ⟧) (x .fun c g)
    mapL d x .coh f g =
      cong (α ⟦ _ ⟧) (x .coh f g)
      ∙ funExt⁻ (α .N-hom f) (x .fun _ g)

    mapLR : {d d' : D.ob} (h : D.Hom[ d' , d ])
      → mapL d' ∘ mapR G h ≡ mapR G' h ∘ mapL d
    mapLR h = funExt λ _ → end≡ _ λ _ _ → refl

  mapLId : (G : Functor (C ^op) (SET ℓ))
    (d : D.ob) → mapL (idTrans G) d ≡ idfun (End G d)
  mapLId G d = funExt λ _ → end≡ _ λ _ _ → refl

  mapL∘ : {G G' G'' : Functor (C ^op) (SET ℓ)}
    (β : NatTrans G' G'') (α : NatTrans G G')
    (d : D.ob) → mapL (seqTrans α β) d ≡ mapL β d ∘ mapL α d
  mapL∘ β α d = funExt λ _ → end≡ _ λ _ _ → refl

  RanHom : {G G' : Functor (C ^op) (SET ℓ)}
    → NatTrans G G' → NatTrans (RanOb G) (RanOb G')
  RanHom α .N-ob = mapL α
  RanHom α .N-hom = mapLR α

  -- Definition of the right Kan extension functor

  Ran : Functor (FUNCTOR (C ^op) (SET ℓ)) (FUNCTOR (D ^op) (SET ℓ))
  Ran .F-ob = RanOb
  Ran .F-hom = RanHom
  Ran .F-id {G} = makeNatTransPath (funExt (mapLId G))
  Ran .F-seq α β = makeNatTransPath (funExt (mapL∘ β α))

  -- Adjunction between precomposition and right Kan extension

  private
    F* = precomposeF (SET ℓ) (F ^opF)

  open UnitCounit

  η : 𝟙⟨ FUNCTOR (D ^op) (SET ℓ) ⟩ ⇒ (funcComp Ran F*)
  η .N-ob G .N-ob d a .fun c g = (G ⟪ g ⟫) a
  η .N-ob G .N-ob d a .coh f g = funExt⁻ (G .F-seq g (F ⟪ f ⟫)) a
  η .N-ob G .N-hom h = funExt λ a → end≡ _ λ c g → sym (funExt⁻ (G .F-seq h g) a)
  η .N-hom {G} {G'} α =
    makeNatTransPath (funExt₂ λ d a → end≡ _ λ c g → sym (funExt⁻ (α .N-hom g) a))

  ε : funcComp F* Ran ⇒ 𝟙⟨ FUNCTOR (C ^op) (SET ℓ) ⟩
  ε .N-ob H .N-ob c x = x .fun c D.id
  ε .N-ob H .N-hom {c} {c'} g =
    funExt λ x →
    cong (x .fun c') (D.⋆IdL _ ∙ sym (D.⋆IdR _)) ∙ x .coh g D.id
  ε .N-hom {H} {H'} α = makeNatTransPath refl

  Δ₁ : ∀ G → seqTrans (F* ⟪ η ⟦ G ⟧ ⟫) (ε ⟦ F* ⟅ G ⟆ ⟧) ≡ idTrans _
  Δ₁ G = makeNatTransPath (funExt₂ λ c a → funExt⁻ (G .F-id) a)

  Δ₂ : ∀ H → seqTrans (η ⟦ Ran ⟅ H ⟆ ⟧) (Ran ⟪ ε ⟦ H ⟧ ⟫) ≡ idTrans _
  Δ₂ H = makeNatTransPath (funExt₂ λ c x → end≡ _ λ c' g → cong (x .fun c') (D.⋆IdL g))

  adj : F* ⊣ Ran
  adj ._⊣_.η = η
  adj ._⊣_.ε = ε
  adj ._⊣_.Δ₁ = Δ₁
  adj ._⊣_.Δ₂ = Δ₂
