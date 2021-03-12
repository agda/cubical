{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Presheaf.KanExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SetQuotients

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

module Lan {ℓC ℓC' ℓD ℓD' ℓS}
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  private
    module C = Precategory C
    module D = Precategory D
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
        (eq/ _ _ (shift (h D.⋆ g) f a) i)
    mapR h (squash/ t u p q i j) =
      squash/ (mapR h t) (mapR h u) (cong (mapR h) p) (cong (mapR h) q) i j

    abstract
      mapRId : (d : D.ob) → mapR (D.id d) ≡ (idfun _)
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

  -- Action of Quo on arrows in C ^op → Set

  module _ {G G' : Functor (C ^op) (SET ℓ)} (α : NatTrans G G') where
  
    mapL : (d : D.ob) → Quo G d → Quo G' d
    mapL d [ c , g , a ] = [ c , g , α .N-ob c a ]
    mapL d (shift/ g f a i) =
      hcomp
        (λ j → λ
          { (i = i0) → [ _ , (g D.⋆ F ⟪ f ⟫) , α .N-ob _ a ]
          ; (i = i1) → [ _ , g , funExt⁻ (α .N-hom f) a (~ j) ]
          })
        (shift/ g f (α . N-ob _ a) i)
    mapL d (squash/ t u p q i j) =
      squash/ (mapL d t) (mapL d u) (cong (mapL d) p) (cong (mapL d) q) i j

    abstract
      mapLR : {d d' : D.ob} (h : D.Hom[ d' , d ]) 
        → mapL d' ∘ mapR G h ≡ mapR G' h ∘ mapL d
      mapLR h = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  abstract
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

  Lan : Functor (FUNCTOR (C ^op) (SET ℓ)) (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
  Lan .F-ob = LanOb
  Lan .F-hom = LanHom
  Lan .F-id {G} = makeNatTransPath (funExt (mapLId G))
  Lan .F-seq α β = makeNatTransPath (funExt (mapL∘ β α))

  -- Adjunction between the left Kan extension and precomposition

  private
    F* = ∘Functor (SET ℓ) (F ^opF)

  open UnitCounit

  η : 𝟙⟨ FUNCTOR (C ^op) (SET ℓ) ⟩ ⇒ (funcComp F* Lan)
  η .N-ob G .N-ob c a = [ c , D.id _ , a ]
  η .N-ob G .N-hom {c'} {c} f =
    funExt λ a →
    [ c , D.id _ , (G ⟪ f ⟫) a ]
      ≡⟨ sym (shift/ (D.id _) f a) ⟩
    [ c' , ((D.id _) D.⋆ F ⟪ f ⟫) , a ]
      ≡[ i ]⟨ [ c' , lem i , a ] ⟩
    [ c' , (F ⟪ f ⟫ D.⋆ (D.id _)) , a ]
    ∎
    where
    lem : (D.id _) D.⋆ F ⟪ f ⟫ ≡ F ⟪ f ⟫ D.⋆ (D.id _)
    lem = D.⋆IdL (F ⟪ f ⟫) ∙ sym (D.⋆IdR (F ⟪ f ⟫))
  η .N-hom f = makeNatTransPath refl

  εOb : (H : Functor (D ^op) (SET _))
    → (d : D.ob) → Quo (F* ⟅ H ⟆) d → (H ⟅ d ⟆) .fst
  εOb H d =
    elim
      (λ _ → (H ⟅ d ⟆) .snd)
      (λ (c , g , a) → (H ⟪ g ⟫) a)
      (λ {_ _ (shift g f a) i → H .F-seq (F ⟪ f ⟫) g i a})

  ε : funcComp Lan F* ⇒ 𝟙⟨ FUNCTOR (D ^op) (SET ℓ) ⟩
  ε .N-ob H .N-ob = εOb H
  ε .N-ob H .N-hom g' =
    funExt (elimProp (λ _ → (H ⟅ _ ⟆) .snd _ _) (λ (c , g , a) → funExt⁻ (H .F-seq g g') a))
  ε .N-hom {H} {H'} α =
    makeNatTransPath
      (funExt₂ λ d →
         elimProp (λ _ → (H' ⟅ _ ⟆) .snd _ _)
          (λ (c , g , a) → sym (funExt⁻ (α .N-hom g) a)))

  abstract
    Δ₁ : ∀ G → seqTrans (Lan ⟪ η ⟦ G ⟧ ⟫) (ε ⟦ Lan ⟅ G ⟆ ⟧) ≡ idTrans _
    Δ₁ G =
      makeNatTransPath
        (funExt₂ λ d →
          elimProp (λ _ → squash/ _ _)
            (λ (c , g , a) →
              [ c , g D.⋆ D.id _ , a ]
                ≡[ i ]⟨ [ c , (g D.⋆ F .F-id (~ i)) , a ] ⟩
              [ c , g D.⋆ (F ⟪ C.id _ ⟫) , a ]
                ≡⟨ shift/ g (C.id _) a ⟩
              [ c , g , (G ⟪ C.id _ ⟫) a ]
                ≡[ i ]⟨ [ c , g , G .F-id i a ] ⟩
              [ c , g , a ]
              ∎))

    Δ₂ : ∀ H → seqTrans (η ⟦ F* ⟅ H ⟆ ⟧) (F* ⟪ ε ⟦ H ⟧ ⟫) ≡ idTrans _
    Δ₂ H = makeNatTransPath (funExt λ c → H .F-id)

  adj : Lan ⊣ F*
  adj = make⊣ η ε Δ₁ Δ₂
