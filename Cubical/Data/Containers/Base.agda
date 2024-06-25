{- Basic container definitions:

- Definition of generalised container parameterised by category C

- Category Cont whose objects are generalised containers

- Functor ⟦_⟧ : Cont → Functor C Set

- Example of List as a generalised container

-}

{-# OPTIONS --safe #-}

module Cubical.Data.Containers.Base where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_◁_)

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans

-- Definition of generalised container
record GenContainer (C : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _◁_&_
  field
    S : Type ℓ'
    P : S → C .ob
    isSetS : isSet S

open GenContainer

module Conts (C : Category ℓ ℓ') where

  -- Category Cont with objects of type GenContainer C
  record _⇒c_ (C₁ C₂ : GenContainer C) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    constructor _◁_
    field
      shape : S C₁ → S C₂
      pos : (s : S C₁) → C [ P C₂ (shape s) , P C₁ s ]

  open _⇒c_

  id-c : {Con : GenContainer C} → Con ⇒c Con
  id-c = (λ s → s) ◁ λ _ → C .id

  _⋆c_ : {C₁ C₂ C₃ : GenContainer C} → C₁ ⇒c C₂ → C₂ ⇒c C₃ → C₁ ⇒c C₃
  _⋆c_ (u ◁ f) (v ◁ g) = (λ a → v (u a)) ◁ λ a → (g (u a)) ⋆⟨ C ⟩ (f a)

  assoc-c : {C₁ C₂ C₃ C₄ : GenContainer C} (f : C₁ ⇒c C₂) (g : C₂ ⇒c C₃) (h : C₃ ⇒c C₄) →
            (f ⋆c g) ⋆c h ≡ f ⋆c (g ⋆c h)
  assoc-c (u ◁ f) (v ◁ g) (w ◁ h) i = (λ a → w (v (u a))) ◁ λ a → C .⋆Assoc (h (v (u a))) (g (u a)) (f a) (~ i)

  isSet⇒c : {C₁ C₂ : GenContainer C} → isSet (C₁ ⇒c C₂)
  shape (isSet⇒c {A ◁ B & set-A} {E ◁ F & set-C} m n p q i j) a =
    set-C (shape m a) (shape n a) (λ k → shape (p k) a) (λ k → shape (q k) a) i j
  pos (isSet⇒c {A ◁ B & set-A} {E ◁ F & set-C} m n p q i j) a =
    isSet→SquareP
      {A = λ i j → C [ (F (set-C (shape m a) (shape n a) (λ k → shape (p k) a) (λ k → shape (q k) a) i j)) ,  B a ]}
      (λ i j → C .isSetHom {F (set-C (shape m a) (shape n a) (λ k → shape (p k) a) (λ k → shape (q k) a) i j)} {B a})
      (λ k → pos (p k) a)
      (λ k → pos (q k) a)
      (λ _ → pos m a)
      (λ _ → pos n a)
      i j

  Cont : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-suc (ℓ-max ℓ ℓ'))
  ob Cont = GenContainer C
  Hom[_,_] Cont = _⇒c_
  id Cont = id-c
  _⋆_ Cont = _⋆c_
  ⋆IdL Cont m i = (shape m) ◁ (λ a → C .⋆IdR (pos m a) i)
  ⋆IdR Cont m i = (shape m) ◁ (λ a → C .⋆IdL (pos m a) i)
  ⋆Assoc Cont = assoc-c
  isSetHom Cont = isSet⇒c

  -- Definition of functor ⟦_⟧ : Cont → Functor C Set

  -- Type alias for (S : Type) (P : S → C .ob) (X : C .ob) ↦ Σ S (λ s → C [ P s , X ])
  cont-func : (S : Type ℓ') (P : S → C .ob) (X : C .ob) → Type ℓ'
  cont-func S P X = Σ S (λ s → C [ P s , X ])

  isSetContFunc : (A : Type ℓ') (B : A → C .ob) (X : C .ob) (isSetA : isSet A) → isSet (cont-func A B X)
  isSetContFunc A B X setA = isSetΣ setA (λ _ → C .isSetHom)

  cont-mor : {A : Type ℓ'} {B : A → C .ob} {X Y : C .ob} (f : C [ X , Y ]) →
             cont-func A B X → cont-func A B Y
  cont-mor f (s , g) = s , (g ⋆⟨ C ⟩ f)

  ⟦_⟧-obj : GenContainer C → Functor C (SET ℓ')
  F-ob ⟦ A ◁ B & set-A ⟧-obj X = cont-func A B X , isSetContFunc A B X set-A
  F-hom ⟦ A ◁ B & set-A ⟧-obj = cont-mor
  F-id ⟦ A ◁ B & set-A ⟧-obj = funExt λ {(a , b) i → a , C .⋆IdR b i}
  F-seq ⟦ A ◁ B & set-A ⟧-obj f g i (a , b) = a , C .⋆Assoc b f g (~ i)

  ⟦_⟧-mor : {C₁ C₂ : GenContainer C} → C₁ ⇒c C₂ → NatTrans ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj
  N-ob (⟦_⟧-mor (u ◁ f)) X (s , p) = u s , ((f s) ⋆⟨ C ⟩ p)
  N-hom (⟦_⟧-mor (u ◁ f)) xy i (a , b) = u a , C .⋆Assoc (f a) b xy (~ i)

  ⟦_⟧-id : {C₁ : GenContainer C} → ⟦_⟧-mor {C₁} {C₁} (id-c {C₁}) ≡ idTrans ⟦ C₁ ⟧-obj
  ⟦_⟧-id = makeNatTransPath λ i X (s , p) → s , C .⋆IdL p i

  ⟦_⟧-comp : {U V W : GenContainer C} (g : U ⇒c V) (h : V ⇒c W) →
             ⟦ g ⋆c h ⟧-mor ≡ ⟦ g ⟧-mor ⋆⟨ FUNCTOR C (SET ℓ') ⟩ ⟦ h ⟧-mor
  ⟦_⟧-comp (ug ◁ fg) (uh ◁ fh) =
    makeNatTransPath λ i A (s , p) → uh (ug s) , C .⋆Assoc (fh (ug s)) (fg s) p i

  ⟦_⟧ : Functor Cont (FUNCTOR C (SET ℓ'))
  F-ob ⟦_⟧ = ⟦_⟧-obj
  F-hom ⟦_⟧ = ⟦_⟧-mor
  F-id ⟦_⟧ = ⟦_⟧-id
  F-seq ⟦_⟧ = ⟦_⟧-comp

module Example where
  open Conts (SET ℓ-zero)

  open import Cubical.Data.Fin
  open import Cubical.Data.Nat

  ListC : GenContainer (SET ℓ-zero)
  ListC = ℕ ◁ (λ n → Fin n , isSetFin) & isSetℕ

  ListF : Functor (SET ℓ-zero) (SET ℓ-zero)
  ListF = ⟦ ListC ⟧-obj
