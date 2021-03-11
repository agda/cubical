{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Presheaf.KanExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.SetQuotients

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

module _ {ℓC ℓC' ℓD ℓD'} ℓS
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
  (F : Functor C D)
  where

  open Functor
  open NatTrans

  private
    module C = Precategory C
    module D = Precategory D

  module _ (G : Functor (C ^op) (SET ℓS)) where

    module _ (d : D.ob) where

      LanField : Type (ℓ-max (ℓ-max ℓC ℓD') ℓS)
      LanField = Σ[ c ∈ C.ob ] Σ[ g ∈ D.Hom[ d , F ⟅ c ⟆ ] ] G .F-ob c .fst

      data LanRel : (u v : LanField) → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS) where
        shift : {c c' : C.ob} (g : D.Hom[ d , F ⟅ c ⟆ ]) (f : C.Hom[ c , c' ]) (a : (G ⟅ c' ⟆) .fst)
          → LanRel (c' , (g D.⋆ F ⟪ f ⟫) , a) (c , g , (G ⟪ f ⟫) a)

      LanOb = LanField / LanRel

    mapLanR : {d d' : D.ob} (h : D.Hom[ d' , d ]) → LanOb d → LanOb d'
    mapLanR h [ c , g , a ] = [ c , h D.⋆ g , a ]
    mapLanR h (eq/ _ _ (shift g f a) i) =
      hcomp
        (λ j → λ
          { (i = i0) → [ _ , D.⋆Assoc h g (F ⟪ f ⟫) j , a ]
          ; (i = i1) → [ _ , h D.⋆ g , (G ⟪ f ⟫) a ]
          })
        (eq/ _ _ (shift (h D.⋆ g) f a) i)
    mapLanR h (squash/ t u p q i j) =
      squash/ (mapLanR h t) (mapLanR h u) (cong (mapLanR h) p) (cong (mapLanR h) q) i j

    mapLanRId : (d : D.ob) → mapLanR (D.id d) ≡ (idfun _)
    mapLanRId d =
      funExt (elimProp (λ _ → squash/ _ _) (λ (c , g , a) i → [ c , D.⋆IdL g i , a ]))

    mapLanR∘ : {d d' d'' : D.ob}
      (h' : D.Hom[ d'' , d' ]) (h : D.Hom[ d' , d ])
      → mapLanR (h' D.⋆ h) ≡ mapLanR h' ∘ mapLanR h
    mapLanR∘ h' h =
      funExt (elimProp (λ _ → squash/ _ _) (λ (c , g , a) i → [ c , D.⋆Assoc h' h g i , a ]))

  module _ {G G' : Functor (C ^op) (SET ℓS)} (α : NatTrans G G') where
  
    mapLanL : (d : D.ob) → LanOb G d → LanOb G' d
    mapLanL d [ c , g , a ] = [ c , g , α .N-ob c a ]
    mapLanL d (eq/ _ _ (shift {c = c} {c' = c'} g f a) i) =
      hcomp
        (λ j → λ
          { (i = i0) → [ c' , (g D.⋆ F ⟪ f ⟫) , α .N-ob c' a ]
          ; (i = i1) → [ c , g , funExt⁻ (α .N-hom f) a (~ j) ]
          })
        (eq/ _ _ (shift g f (α . N-ob c' a)) i)
    mapLanL d (squash/ t u p q i j) =
      squash/ (mapLanL d t) (mapLanL d u) (cong (mapLanL d) p) (cong (mapLanL d) q) i j

    mapLanLR : {d d' : D.ob} (h : D.Hom[ d' , d ]) 
      → mapLanL d' ∘ mapLanR G h ≡ mapLanR G' h ∘ mapLanL d
    mapLanLR h = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  mapLanLId : (G : Functor (C ^op) (SET ℓS))
    (d : D.ob) → mapLanL (idTrans G) d ≡ idfun (LanOb G d)
  mapLanLId G d = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))

  mapLanL∘ : {G G' G'' : Functor (C ^op) (SET ℓS)}
    (β : NatTrans G' G'') (α : NatTrans G G')
    (d : D.ob) → mapLanL (seqTrans α β) d ≡ mapLanL β d ∘ mapLanL α d
  mapLanL∘ β α d = funExt (elimProp (λ _ → squash/ _ _) (λ _ → refl))
    
  Lan : Functor (FUNCTOR (C ^op) (SET ℓS)) (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
  Lan .F-ob G .F-ob d .fst = LanOb G d
  Lan .F-ob G .F-ob d .snd = squash/
  Lan .F-ob G .F-hom = mapLanR G
  Lan .F-ob G .F-id = mapLanRId G _
  Lan .F-ob G .F-seq h h' = mapLanR∘ G h' h
  Lan .F-hom α .N-ob = mapLanL α
  Lan .F-hom α .N-hom = mapLanLR α
  Lan .F-id = makeNatTransPath (funExt (mapLanLId _))
  Lan .F-seq α β = makeNatTransPath (funExt (mapLanL∘ β α))

module _ {ℓC ℓC' ℓD ℓD'} ℓS
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
  (F : Functor C D)
  where

  private
    ℓ = ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS

  open Functor
  open NatTrans
  open UnitCounit

  private
    module C = Precategory C
    module D = Precategory D

  counitOb : (G : Functor (D ^op) (SET _))
    → (d : D.ob) → LanOb ℓ F (funcComp G (F ^opF)) d → (G ⟅ d ⟆) .fst
  counitOb G d =
    elim
      (λ _ → (G ⟅ d ⟆) .snd)
      (λ (c , g , a) → (G ⟪ g ⟫) a)
      (λ {_ _ (shift g f a) i → G .F-seq (F ⟪ f ⟫) g i a})

  isAdjointLan : Lan ℓ F ⊣ ∘Functor (SET ℓ) (F ^opF)
  isAdjointLan ._⊣_.η .N-ob G .N-ob c a = [ c , D.id _ , a ]
  isAdjointLan ._⊣_.η .N-ob G .N-hom {c'} {c} f =
    funExt λ a →
    [ c , D.id _ , (G ⟪ f ⟫) a ]
      ≡⟨ sym (eq/ _ _ (shift (D.id _) f a)) ⟩
    [ c' , ((D.id _) D.⋆ F ⟪ f ⟫) , a ]
      ≡[ i ]⟨ [ c' , lem i , a ] ⟩
    [ c' , (F ⟪ f ⟫ D.⋆ (D.id _)) , a ]
    ∎
    where
    lem : (D.id _) D.⋆ F ⟪ f ⟫ ≡ F ⟪ f ⟫ D.⋆ (D.id _)
    lem = D.⋆IdL (F ⟪ f ⟫) ∙ sym (D.⋆IdR (F ⟪ f ⟫))
  isAdjointLan ._⊣_.η .N-hom f = makeNatTransPath refl
  isAdjointLan ._⊣_.ε .N-ob G .N-ob = counitOb G
  isAdjointLan ._⊣_.ε .N-ob G .N-hom g' =
    funExt (elimProp (λ _ → (G ⟅ _ ⟆) .snd _ _) (λ (c , g , a) → funExt⁻ (G .F-seq g g') a))
  isAdjointLan ._⊣_.ε .N-hom {G} {G'} α =
    makeNatTransPath
      (funExt λ d →
        funExt
          (elimProp (λ _ → (G' ⟅ _ ⟆) .snd _ _)
            (λ (c , g , a) → sym (funExt⁻ (α .N-hom g) a))))
  isAdjointLan ._⊣_.Δ₁ = {!!}
  isAdjointLan ._⊣_.Δ₂ = {!!}
