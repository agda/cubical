{--
Defines the structure group of a heap,
proves that a group is equivalently a pointed heap.
TODO: A heap is equivalently a group equipped with a torsor
--}

module Cubical.Algebra.Heap.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath

open import Cubical.Algebra.Heap.Base

private variable
  ℓ : Level

module _ (G : Group ℓ) where
  open HeapStr
  open IsHeap
  open GroupStr (snd G) renaming (is-set to G-is-set)

  GroupHasHeapStr : HeapStr ⟨ G ⟩
  GroupHasHeapStr .[_,_,_] a b c = a · inv b · c
  GroupHasHeapStr .isHeap .is-set = G-is-set
  GroupHasHeapStr .isHeap .assoc a b c d e = ·Assoc a (inv b) (c · inv d · e) ∙∙  ·Assoc (a · inv b) c (inv d · e)  ∙∙ congL _·_ (sym (·Assoc a (inv b) c))
  GroupHasHeapStr .isHeap .idl a b = ·GroupAutomorphismL G a .Iso.rightInv b
  GroupHasHeapStr .isHeap .idr a b = congR _·_ (·InvL b) ∙ ·IdR a
  GroupHasHeapStr .isHeap .inhab = ∣ 1g ∣₁

  GroupHeap : Heap ℓ
  GroupHeap = ⟨ G ⟩ , GroupHasHeapStr

module HeapTheory (H : Heap ℓ) where
  open HeapStr (snd H) public

  wriggle : ∀ a b c d → [ [ a , b , c ] , d , [ d , c , b ] ] ≡ a
  wriggle a b c d =
    [ [ a , b , c ] , d , [ d , c , b ] ] ≡⟨ assoc [ a , b , c ] d d c b ⟩
    [ [ [ a , b , c ] , d , d ] , c , b ] ≡⟨ cong [_, c , b ] (idr [ a , b , c ] d) ⟩
    [ [ a , b , c ] , c , b ]             ≡⟨ sym (assoc a b c c b) ⟩
    [ a , b , [ c , c , b ] ]             ≡⟨ cong [ a , b ,_] (idl c b) ⟩
    [ a , b , b ]                         ≡⟨ idr a b ⟩
    a                                     ∎

  -- Wagner's theory of generalized heaps, theorem 8.2.13
  assocl : ∀ a b c d e → [ a , [ d , c , b ] , e ] ≡ [ [ a , b , c ] , d , e ]
  assocl a b c d e =
    [ a , [ d , c , b ] , e ]                                     ≡⟨ cong [_, [ d , c , b ] , e ] (sym (wriggle a b c d)) ⟩
    [ [ [ a , b , c ] , d , [ d , c , b ] ] , [ d , c , b ] , e ] ≡⟨ sym (assoc [ a , b , c ] d [ d , c , b ] [ d , c , b ] e) ⟩
    [ [ a , b , c ] , d , [ [ d , c , b ] , [ d , c , b ] , e ] ] ≡⟨ cong [ [ a , b , c ] , d ,_] (idl [ d , c , b ] e) ⟩
    [ [ a , b , c ] , d , e ]                                     ∎

  assocr : ∀ a b c d e → [ a , [ d , c , b ] , e ] ≡ [ a , b , [ c , d , e ] ]
  assocr a b c d e =
    [ a , [ d , c , b ] , e ] ≡⟨ assocl a b c d e ⟩
    [ [ a , b , c ] , d , e ] ≡⟨ sym (assoc a b c d e) ⟩
    [ a , b , [ c , d , e ] ] ∎

  idlr : ∀ a b c → [ a , [ b , c , a ] , b ] ≡ c
  idlr a b c =
    [ a , [ b , c , a ] , b ] ≡⟨ assocr a a c b b ⟩
    [ a , a , [ c , b , b ] ] ≡⟨ idl a [ c , b , b ] ⟩
    [ c , b , b ]             ≡⟨ idr c b ⟩
    c                         ∎

StructureGroup : Heap ℓ → Group ℓ
StructureGroup H = toldYaSo inhab module StructureGroup where
  open GroupStr hiding (is-set)
  open HeapTheory H

  fromPoint : ⟨ H ⟩ → Group _
  fromPoint e .fst = ⟨ H ⟩
  fromPoint e .snd .1g = e
  fromPoint e .snd ._·_ a b = [ a , e , b ]
  fromPoint e .snd .inv a = [ e , a , e ]
  fromPoint e .snd .isGroup = makeIsGroup is-set
    (λ x y z → assoc x e y e z)
    (λ x → idr x e) -- is that a maybeJosiah reference
    (λ x → idl e x)
    (λ x → assoc x e e x e ∙∙ cong [_, x , e ] (idr x e) ∙∙ idl x e)
    (λ x → sym (assoc e x e e x) ∙∙ cong [ e , x ,_] (idl e x) ∙∙ idr e x)

  φ : ∀ e e' → GroupHom (fromPoint e) (fromPoint e')
  φ e e' .fst x = [ e' , e , x ]
  φ e e' .snd = makeIsGroupHom λ x y →
    [ e' , e , [ x , e , y ] ]               ≡⟨ assoc e' e x e y ⟩
    [ [ e' , e , x ] , e , y ]               ≡⟨ cong [ [ e' , e , x ] ,_, y ] (sym (idr e e')) ⟩
    [ [ e' , e , x ] , [ e , e' , e' ] , y ] ≡⟨ assocr [ e' , e , x ] e' e' e y ⟩
    [ [ e' , e , x ] , e' , [ e' , e , y ] ] ∎

  φ-coh : ∀ e e' e'' x → φ e' e'' .fst (φ e e' .fst x) ≡ φ e e'' .fst x
  φ-coh e e' e'' x =
    [ e'' , e' , [ e' , e , x ] ] ≡⟨ sym (assocr e'' e' e' e x) ⟩
    [ e'' , [ e , e' , e' ] , x ] ≡⟨ cong [ e'' ,_, x ] (idr e e') ⟩
    [ e'' , e , x ]               ∎

  φ-eqv : ∀ e e' → isEquiv (φ e e' .fst)
  φ-eqv e e' = isoToIsEquiv (iso (φ e e' .fst) (φ e' e .fst) (lemma e e') (lemma e' e)) where

    lemma : ∀ e e' x → φ e e' .fst (φ e' e .fst x) ≡ x
    lemma e e' x = φ-coh e' e e' x ∙ idl e' x

  toldYaSo : ∥ ⟨ H ⟩ ∥₁ → Group _
  toldYaSo = PropTrunc→Group fromPoint (λ e e' → (φ e e' .fst , φ-eqv e e') , φ e e' .snd) φ-coh

StructureGroupOfGroupHeap : (G : Group ℓ) → GroupEquiv (StructureGroup (GroupHeap G)) G
StructureGroupOfGroupHeap G = idEquiv _ , makeIsGroupHom λ x y → congR _·_ $ congL _·_ inv1g ∙ ·IdL y
  where open GroupStr (G .snd); open GroupTheory G

GroupHeapOfStructureGroup : (H : Heap ℓ) → ∥ HeapEquiv (GroupHeap (StructureGroup H)) H ∥₁ -- unnatural isomorphism
GroupHeapOfStructureGroup H = go inhab module GroupHeapOfStructureGroup where
  open HeapTheory H

  fromPoint : (e : ⟨ H ⟩) → HeapEquiv (GroupHeap (StructureGroup.fromPoint H e)) H
  fromPoint e = idEquiv _ , makeIsHeapHom λ a b c →
    [ a , e , [ [ e , b , e ] , e , c ] ] ≡⟨ cong [ a , e ,_] (sym (assoc e b e e c)) ⟩
    [ a , e , [ e , b , [ e , e , c ] ] ] ≡⟨ cong [ a , e ,_] (cong [ e , b ,_] (idl e c)) ⟩
    [ a , e , [ e , b , c ] ]             ≡⟨ assoc a e e b c ⟩
    [ [ a , e , e ] , b , c ]             ≡⟨ cong [_, b , c ] (idr a e) ⟩
    [ a , b , c ]                         ∎

  go : (p : ∥ ⟨ H ⟩ ∥₁) → ∥ HeapEquiv (GroupHeap (StructureGroup.toldYaSo H p)) H ∥₁
  go = PT.elim (λ _ → isPropPropTrunc) λ e → ∣ fromPoint e ∣₁

PointedHeap : ∀ ℓ → Type (ℓ-suc ℓ)
PointedHeap ℓ = Σ[ H ∈ Heap ℓ ] ⟨ H ⟩

PointedHeap≡ : {(H , e) (H' , e') : PointedHeap ℓ} (eqv : HeapEquiv H H') (p : eqv .fst .fst e ≡ e') → (H , e) ≡ (H' , e')
PointedHeap≡ eqv p = cong₂ _,_ (uaHeap eqv) (ua-gluePath _ p)

GroupsArePointedHeaps : Group ℓ ≃ PointedHeap ℓ
GroupsArePointedHeaps {ℓ} = isoToEquiv asIso module GroupsArePointedHeaps where
  open Iso

  asIso : Iso (Group ℓ) (PointedHeap ℓ)
  asIso .fun G = GroupHeap G , G .snd .GroupStr.1g
  asIso .inv (H , e) = StructureGroup.fromPoint H e
  asIso .rightInv (H , e) = PointedHeap≡ (GroupHeapOfStructureGroup.fromPoint H e) refl
  asIso .leftInv G = uaGroup (StructureGroupOfGroupHeap G)
