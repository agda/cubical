{-# OPTIONS --safe #-}
module Cubical.Data.Graph.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

private variable ℓv ℓv' ℓv'' ℓe ℓe' ℓe'' ℓd ℓd' : Level

-- The type of directed multigraphs (with loops)

record Graph ℓv ℓe : Type (ℓ-suc (ℓ-max ℓv ℓe)) where
  field
    Node : Type ℓv
    Edge : Node → Node → Type ℓe

open Graph public

_ᵒᵖ : Graph ℓv ℓe → Graph ℓv ℓe
Node (G ᵒᵖ) = Node G
Edge (G ᵒᵖ) x y = Edge G y x

TypeGr : ∀ ℓ → Graph (ℓ-suc ℓ) ℓ
Node (TypeGr ℓ) = Type ℓ
Edge (TypeGr ℓ) A B = A → B

-- Graph functors/homomorphisms

record GraphHom (G  : Graph ℓv  ℓe ) (G' : Graph ℓv' ℓe')
                : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-max ℓv' ℓe'))) where
  field
    _$g_ : Node G → Node G'
    _<$g>_ : ∀ {x y : Node G} → Edge G x y → Edge G' (_$g_ x) (_$g_ y)

open GraphHom public

GraphGr : ∀ ℓv ℓe → Graph _ _
Node (GraphGr ℓv ℓe) = Graph ℓv ℓe
Edge (GraphGr ℓv ℓe) G G' = GraphHom G G'

-- Diagrams are (graph) functors with codomain Type

Diag : ∀ ℓd (G : Graph ℓv ℓe) → Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))
Diag ℓd G = GraphHom G (TypeGr ℓd)

record DiagMor {G : Graph ℓv ℓe} (F : Diag ℓd G) (F' : Diag ℓd' G)
               : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc (ℓ-max ℓd ℓd')))) where
  field
    nat : ∀ (x : Node G) → F $g x → F' $g x
    comSq : ∀ {x y : Node G} (f : Edge G x y) → nat y ∘ F <$g> f ≡ F' <$g> f ∘ nat x

open DiagMor public

DiagGr : ∀ ℓd (G : Graph ℓv ℓe) → Graph _ _
Node (DiagGr ℓd G) = Diag ℓd G
Edge (DiagGr ℓd G) = DiagMor
