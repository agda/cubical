{- Basic container definitions:

- Definition of generalised container parameterised by category C

- Category Cont whose objects are generalised containers

- Functor ⟦_⟧ : Cont → Functor C Set

- Example of List as a generalised container

-}


{-# OPTIONS --safe #-}

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_◁_)

module Cubical.Data.Containers.Base where

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
    P : S → ob C
    isSetS : isSet S

open GenContainer

module Conts {C : Category ℓ ℓ'} where

  -- Category Cont with objects of type GenContainer C
  record _⇒c_ (C₁ C₂ : GenContainer C) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    constructor _◁_
    field
      u : S C₁ → S C₂
      f : (s : S C₁) → C [ P C₂ (u s) , P C₁ s ]

  open _⇒c_

  id-c : {Con : GenContainer C} → Con ⇒c Con
  id-c = (λ s → s) ◁ λ _ → C .id

  _⋆c_ : {C₁ C₂ C₃ : GenContainer C} → C₁ ⇒c C₂ → C₂ ⇒c C₃ → C₁ ⇒c C₃
  _⋆c_ (u ◁ f) (v ◁ g) = (λ a → v (u a)) ◁ λ a → (g (u a)) ⋆⟨ C ⟩ (f a)

  assoc-c : {C₁ C₂ C₃ C₄ : GenContainer C} (f : C₁ ⇒c C₂) (g : C₂ ⇒c C₃) (h : C₃ ⇒c C₄) →
            (f ⋆c g) ⋆c h ≡ f ⋆c (g ⋆c h)
  assoc-c (u ◁ f) (v ◁ g) (w ◁ h) i = (λ a → w (v (u a))) ◁ λ a → C .⋆Assoc (h (v (u a))) (g (u a)) (f a) (~ i)

  isSet⇒c : {C₁ C₂ : GenContainer C} → isSet (C₁ ⇒c C₂)
  u (isSet⇒c {A ◁ B & set-A} {E ◁ F & set-C} m n p q i j) a =
    set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j
  f (isSet⇒c {A ◁ B & set-A} {E ◁ F & set-C} m n p q i j) a =
    isSet→SquareP
      {A = λ i j → C [ (F (set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j)) ,  B a ]} 
      (λ i j → C .isSetHom {F (set-C (u m a) (u n a) (λ k → u (p k) a) (λ k → u (q k) a) i j)} {B a})
      (λ k → f (p k) a)
      (λ k → f (q k) a)
      (λ _ → f m a)
      (λ _ → f n a)
      i j

  Cont : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-suc (ℓ-max ℓ ℓ'))
  Cont = record
           { ob = GenContainer C
           ; Hom[_,_] = _⇒c_
           ; id = id-c
           ; _⋆_ = _⋆c_
           ; ⋆IdL = λ m i → (u m) ◁ (λ a → C .⋆IdR (f m a) i)
           ; ⋆IdR = λ m i → (u m) ◁ (λ a → C .⋆IdL (f m a) i)
           ; ⋆Assoc = assoc-c
           ; isSetHom = isSet⇒c
           }

  -- Definition of functor ⟦_⟧ : Cont → Functor C Set

  -- Type alias for (S : Type) (P : S → C .ob) (X : C .ob) ↦ Σ S (λ s → C [ P s , X ]) 
  cont-func : (S : Type ℓ') (P : S → C .ob) (X : C .ob) → Type ℓ'
  cont-func S P X = Σ S (λ s → C [ P s , X ])

  isSetContFunc : (A : Type ℓ') (B : A → ob C) (X : ob C) (isSetA : isSet A) → isSet (cont-func A B X)
  fst (isSetContFunc A B X setA s₁ s₂ p q i j) =
    setA (fst s₁) (fst s₂) (λ k → fst (p k)) (λ k → fst (q k)) i j
  snd (isSetContFunc A B X setA s₁ s₂ p q i j) = 
      isSet→SquareP
      {A = λ i j → C [ (B (setA (fst s₁) (fst s₂) (λ k → fst (p k)) (λ k → fst (q k)) i j)) , X ]}
      (λ i j → C .isSetHom {B (setA (fst s₁) (fst s₂) (λ k → fst (p k)) (λ k → fst (q k)) i j)} {X})
      (λ k → snd (p k))
      (λ k → snd (q k))
      (λ _ → snd s₁)
      (λ _ → snd s₂)
      i j

  cont-mor : {A : Type ℓ'} {B : A → ob C} {X Y : ob C} (f : C [ X , Y ]) →
             cont-func A B X → cont-func A B Y
  cont-mor f (s , g) = s , (g ⋆⟨ C ⟩ f)

  ⟦_⟧-obj : GenContainer C → Functor C (SET ℓ')
  ⟦ (A ◁ B & set-A) ⟧-obj = record {
                                    F-ob = λ X → cont-func A B X , isSetContFunc A B X set-A ;
                                    F-hom = cont-mor ;
                                    F-id = funExt λ {(a , b) i → a , C .⋆IdR b i} ;
                                    F-seq = λ f g i (a , b) → a , C .⋆Assoc b f g (~ i) 
                                   }

  ⟦_⟧-mor : {C₁ C₂ : GenContainer C} → C₁ ⇒c C₂ → NatTrans ⟦ C₁ ⟧-obj ⟦ C₂ ⟧-obj
  N-ob (⟦_⟧-mor (u ◁ f)) X (s , p) = u s , ((f s) ⋆⟨ C ⟩ p)
  N-hom (⟦_⟧-mor (u ◁ f)) xy i (a , b) = u a , C .⋆Assoc (f a) b xy (~ i)

  ⟦_⟧-id : {C₁ : GenContainer C} → ⟦_⟧-mor {C₁} {C₁} (id-c {C₁}) ≡ idTrans ⟦ C₁ ⟧-obj
  N-ob (⟦_⟧-id {S ◁ P & set-S} i) X (s , p) = s , C .⋆IdL p i
  N-hom (⟦_⟧-id {S ◁ P & set-S} i) {X} {Y} xy j (s , p) = square i j
    where
      square : Square
                 (λ j → N-hom (⟦_⟧-mor {S ◁ P & set-S} {S ◁ P & set-S} id-c) xy j (s , p))
                 (λ j → N-hom (idTrans ⟦ S ◁ P & set-S ⟧-obj) xy j (s , p))
                 (λ i → s , C .⋆IdL ((C ⋆ p) xy) i)
                 (λ i → s , (C ⋆ C .⋆IdL p i) xy)
      square = isSet→SquareP (λ i j → isSetContFunc S P Y set-S) _ _ _ _

  ⟦_⟧-comp : {U V W : GenContainer C} (g : U ⇒c V) (h : V ⇒c W) →
             ⟦ g ⋆c h ⟧-mor ≡ ⟦ g ⟧-mor ⋆⟨ FUNCTOR C (SET ℓ') ⟩ ⟦ h ⟧-mor
  N-ob (⟦_⟧-comp {U} {V} {W} (ug ◁ fg) (uh ◁ fh) i) A (s , p) = uh (ug s) , C .⋆Assoc (fh (ug s)) (fg s) p i
  N-hom (⟦_⟧-comp {U} {V} {W} (ug ◁ fg) (uh ◁ fh) i) {X} {Y} xy j (s , p) = square i j 
    where
      square : Square
                (λ j → N-hom (⟦_⟧-mor {U} {W} (_⋆c_ {U} {V} {W} (ug ◁ fg) (uh ◁ fh))) {X} {Y} xy j (s , p))
                (λ j → N-hom (seq' (FUNCTOR C (SET ℓ')) {⟦ U ⟧-obj} {⟦ V ⟧-obj} {⟦ W ⟧-obj}
                       (⟦_⟧-mor {U} {V} (ug ◁ fg)) (⟦_⟧-mor {V} {W} (uh ◁ fh))) xy j (s , p)) 
                (λ i → uh (ug s) , C .⋆Assoc (fh (ug s)) (fg s) ((C ⋆ p) xy) i)
                (λ i → uh (ug s) , (C ⋆ C .⋆Assoc (fh (ug s)) (fg s) p i) xy)
      square = isSet→SquareP (λ i j → isSetContFunc (S W) (P W) Y (isSetS W)) _ _ _ _

  ⟦_⟧ : Functor Cont (FUNCTOR C (SET ℓ'))
  ⟦_⟧ = record {
                F-ob = ⟦_⟧-obj ;
                F-hom = ⟦_⟧-mor ;
                F-id = λ {A} → ⟦_⟧-id {A} ;
                F-seq = ⟦_⟧-comp
               }
              
-- Example

open Conts {C = SET (ℓ-zero)}

open import Cubical.Data.Fin
open import Cubical.Data.Nat

ListC : GenContainer (SET (ℓ-zero))
ListC = ℕ ◁ (λ n → Fin n , isSetFin) & isSetℕ

ListF : Functor (SET (ℓ-zero)) (SET (ℓ-zero))
ListF = ⟦ ListC ⟧-obj
