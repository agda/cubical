{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Graph.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

private variable ℓv ℓv' ℓv'' ℓe ℓe' ℓe'' ℓd ℓd' : Level

-- The type of directed multigraphs (with loops)

record Graph ℓv ℓe : Type (ℓ-suc (ℓ-max ℓv ℓe)) where
  field
    Obj : Type ℓv
    Hom : Obj → Obj → Type ℓe

open Graph public

_ᵒᵖ : Graph ℓv ℓe → Graph ℓv ℓe
Obj (G ᵒᵖ) = Obj G
Hom (G ᵒᵖ) x y = Hom G y x

TypeGr : ∀ ℓ → Graph (ℓ-suc ℓ) ℓ
Obj (TypeGr ℓ) = Type ℓ
Hom (TypeGr ℓ) A B = A → B

-- Graph functors/homomorphisms

record GraphHom (G  : Graph ℓv  ℓe ) (G' : Graph ℓv' ℓe')
                : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-max ℓv' ℓe'))) where
  field
    _$_ : Obj G → Obj G'
    _<$>_ : ∀ {x y : Obj G} → Hom G x y → Hom G' (_$_ x) (_$_ y)

open GraphHom public

GraphGr : ∀ ℓv ℓe → Graph _ _
Obj (GraphGr ℓv ℓe) = Graph ℓv ℓe
Hom (GraphGr ℓv ℓe) G G' = GraphHom G G'

-- Diagrams are (graph) functors with codomain Type

Diag : ∀ ℓd (G : Graph ℓv ℓe) → Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))
Diag ℓd G = GraphHom G (TypeGr ℓd)

record DiagMor {G : Graph ℓv ℓe} (F : Diag ℓd G) (F' : Diag ℓd' G)
               : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc (ℓ-max ℓd ℓd')))) where
  field
    nat : ∀ (x : Obj G) → F $ x → F' $ x
    comSq : ∀ {x y : Obj G} (f : Hom G x y) → nat y ∘ F <$> f ≡ F' <$> f ∘ nat x

open DiagMor public

DiagGr : ∀ ℓd (G : Graph ℓv ℓe) → Graph _ _
Obj (DiagGr ℓd G) = Diag ℓd G
Hom (DiagGr ℓd G) = DiagMor
