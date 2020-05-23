{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Base where

open import Cubical.Foundations.Prelude hiding ( comp )

import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Foundations.Equiv.HalfAdjoint as HAE

record isGroup {ℓ} (A : Type ℓ) : Type ℓ where
  constructor group-struct
  field
    id  : A
    inv  : A → A
    comp  : A → A → A
    lUnit : ∀ a → comp id a ≡ a
    rUnit : ∀ a → comp a id ≡ a
    assoc  : ∀ a b c → comp (comp a b) c ≡ comp a (comp b c)
    lCancel  : ∀ a → comp (inv a) a ≡ id
    rCancel : ∀ a → comp a (inv a) ≡ id

record Group ℓ : Type (ℓ-suc ℓ) where
  constructor group
  field
    type : Type ℓ
    setStruc : isSet type
    groupStruc : isGroup type

isMorph : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H)) → Type (ℓ-max ℓ ℓ')
isMorph (group G Gset (group-struct _ _ _⊙_ _ _ _ _ _))
        (group H Hset (group-struct _ _ _∘_ _ _ _ _ _)) f
        = (g0 g1 : G) → f (g0 ⊙ g1) ≡ (f g0) ∘ (f g1)

morph : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
morph G H = Σ (Group.type G →  Group.type H) (isMorph G H)

rightist-group-struct : ∀ {ℓ} {A : Type ℓ}
  → (id : A) (inv : A → A) (comp : A → A → A)
  → (rUnit : ∀ a → comp a id ≡ a)
  → (assoc : ∀ a b c → comp (comp a b) c ≡ comp a (comp b c))
  → (rCancel : ∀ a → comp a (inv a) ≡ id)
  → isGroup A
rightist-group-struct id inv comp rUnit assoc rCancel =
  group-struct id inv comp lUnit rUnit assoc lCancel rCancel
  where
    abstract
      lCancel : ∀ a → comp (inv a) a ≡ id
      lCancel a =
        comp (inv a) a
          ≡⟨ sym (rUnit (comp (inv a) a))  ⟩
        comp (comp (inv a) a) id
          ≡⟨ cong (comp (comp (inv a) a)) (sym (rCancel (inv a))) ⟩
        comp (comp (inv a) a) (comp (inv a) (inv (inv a)))
          ≡⟨ sym (assoc (comp (inv a) a) (inv a) (inv (inv a))) ⟩
        comp (comp (comp (inv a) a) (inv a)) (inv (inv a))
          ≡⟨ cong (λ b → comp b (inv (inv a))) (assoc (inv a) a (inv a)) ⟩
        comp (comp (inv a) (comp a (inv a))) (inv (inv a))
          ≡⟨ cong (λ b → comp (comp (inv a) b) (inv (inv a))) (rCancel a) ⟩
        comp (comp (inv a) id) (inv (inv a))
          ≡⟨ cong (λ b → comp b (inv (inv a))) (rUnit (inv a)) ⟩
        comp (inv a) (inv (inv a))
          ≡⟨ rCancel (inv a) ⟩
        id
          ∎

      lUnit : ∀ a → comp id a ≡ a
      lUnit a =
        comp id a
          ≡⟨ cong (λ b → comp b a) (sym (rCancel a)) ⟩
        comp (comp a (inv a)) a
          ≡⟨ assoc a (inv a) a ⟩
        comp a (comp (inv a) a)
          ≡⟨ cong (comp a) (lCancel a) ⟩
        comp a id
          ≡⟨ rUnit a ⟩
        a
          ∎

rightist-group : ∀ {ℓ} {A : Type ℓ} (Aset : isSet A)
  → (id : A) (inv : A → A) (comp : A → A → A)
  → (rUnit : ∀ a → comp a id ≡ a)
  → (assoc : ∀ a b c → comp (comp a b) c ≡ comp a (comp b c))
  → (rCancel : ∀ a → comp a (inv a) ≡ id)
  → Group ℓ
rightist-group Aset id inv comp rUnit assoc rCancel =
  group _ Aset (rightist-group-struct id inv comp rUnit assoc rCancel)

leftist-group-struct : ∀ {ℓ} {A : Type ℓ}
  → (id : A) (inv : A → A) (comp : A → A → A)
  → (lUnit : ∀ a → comp id a ≡ a)
  → (assoc : ∀ a b c → comp (comp a b) c ≡ comp a (comp b c))
  → (lCancel : ∀ a → comp (inv a) a ≡ id)
  → isGroup A
leftist-group-struct id inv comp lUnit assoc lCancel =
  group-struct id inv comp lUnit rUnit assoc lCancel rCancel
  where
    abstract
      rCancel : ∀ a → comp a (inv a) ≡ id
      rCancel a =
        comp a (inv a)
          ≡⟨ sym (lUnit (comp a (inv a)))  ⟩
        comp id (comp a (inv a))
          ≡⟨ cong (λ b → comp b (comp a (inv a))) (sym (lCancel (inv a))) ⟩
        comp (comp (inv (inv a)) (inv a)) (comp a (inv a))
          ≡⟨ assoc (inv (inv a)) (inv a) (comp a (inv a)) ⟩
        comp (inv (inv a)) (comp (inv a) (comp a (inv a)))
          ≡⟨ cong (comp (inv (inv a))) (sym (assoc (inv a) a (inv a))) ⟩
        comp (inv (inv a)) (comp (comp (inv a) a) (inv a))
          ≡⟨ cong (λ b → comp (inv (inv a)) (comp b (inv a))) (lCancel a) ⟩
        comp (inv (inv a)) (comp id (inv a))
          ≡⟨ cong (comp (inv (inv a))) (lUnit (inv a)) ⟩
        comp (inv (inv a)) (inv a)
          ≡⟨ lCancel (inv a) ⟩
        id
          ∎

      rUnit : ∀ a → comp a id ≡ a
      rUnit a =
        comp a id
          ≡⟨ cong (comp a) (sym (lCancel a)) ⟩
        comp a (comp (inv a) a)
          ≡⟨ sym (assoc a (inv a) a) ⟩
        comp (comp a (inv a)) a
          ≡⟨ cong (λ b → comp b a) (rCancel a) ⟩
        comp id a
          ≡⟨ lUnit a ⟩
        a
          ∎

leftist-group : ∀ {ℓ} {A : Type ℓ} (Aset : isSet A)
  → (id : A) (inv : A → A) (comp : A → A → A)
  → (lUnit : ∀ a → comp id a ≡ a)
  → (assoc : ∀ a b c → comp (comp a b) c ≡ comp a (comp b c))
  → (lCancel : ∀ a → comp (inv a) a ≡ id)
  → Group ℓ
leftist-group Aset id inv comp lUnit assoc lCancel =
  group _ Aset (leftist-group-struct id inv comp lUnit assoc lCancel)

record Iso {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso
  field
    fun : morph G H
    inv : morph H G
    rightInv : I.section (fun .fst) (inv .fst)
    leftInv : I.retract (fun .fst) (inv .fst)

record Iso' {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso'
  field
    isoSet : I.Iso (Group.type G) (Group.type H)
    isoSetMorph : isMorph G H (I.Iso.fun isoSet)

_≃_ : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (morph A B) \ f → (E.isEquiv (f .fst))

Iso'→Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso' G  H → Iso G H
Iso'→Iso {G = group G Gset Ggroup} {H = group H Hset Hgroup} i = iso (fun , funMorph) (inv , invMorph) rightInv leftInv
  where
    G_ : Group _
    G_ = (group G Gset Ggroup)

    H_ : Group _
    H_ = (group H Hset Hgroup)

    open Iso'

    fun : G → H
    fun = I.Iso.fun (isoSet i)

    inv : H → G
    inv = I.Iso.inv (isoSet i)

    rightInv : I.section fun inv
    rightInv = I.Iso.rightInv (isoSet i)

    leftInv : I.retract fun inv
    leftInv = I.Iso.leftInv (isoSet i)

    e' : G E.≃ H
    e' = I.isoToEquiv (I.iso fun inv rightInv leftInv)

    funMorph : isMorph G_ H_ fun
    funMorph = isoSetMorph i

    _∘_ : H → H → H
    _∘_ = isGroup.comp Hgroup

    _⊙_ : G → G → G
    _⊙_ = isGroup.comp Ggroup

    invMorph : isMorph H_ G_ inv
    invMorph h0 h1 = E.invEq (HAE.congEquiv e')
          (fun (inv (h0 ∘ h1)) ≡⟨ rightInv (h0 ∘ h1) ⟩
           h0 ∘ h1 ≡⟨ cong (λ x → x ∘ h1) (sym (rightInv h0)) ⟩
           (fun (inv h0)) ∘ h1 ≡⟨ cong (λ x → fun (inv h0) ∘ x) (sym (rightInv h1)) ⟩
           (fun (inv h0)) ∘ (fun (inv h1)) ≡⟨ sym (funMorph (inv h0) (inv h1)) ⟩
           fun ((inv h0) ⊙ (inv h1)) ∎ )


Equiv→Iso' : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → G ≃ H → Iso' G H
Equiv→Iso' {G = group G Gset Ggroup}
           {H = group H Hset Hgroup}
           e = iso' i' (e .fst .snd)
  where
    e' : G E.≃ H
    e' = (e .fst .fst) , (e .snd)

    i' : I.Iso G H
    i' = E.equivToIso e'

compMorph : ∀ {ℓ} {F G H : Group ℓ} (I : morph F G) (J : morph G H) → morph F H
compMorph {ℓ} {group F Fset (group-struct _ _ _⊙_ _ _ _ _ _)}
              {group G Gset (group-struct _ _ _∙_ _ _ _ _ _)}
              {group H Hset (group-struct _ _ _∘_ _ _ _ _ _)}
              (i , ic) (j , jc) = k , kc
  where
    k : F → H
    k f = j (i f)

    kc : (g0 g1 : F) → k (g0 ⊙ g1) ≡ (k g0) ∘ (k g1)
    kc g0 g1 = j (i (g0 ⊙ g1)) ≡⟨ cong j (ic _ _) ⟩
                j (i g0 ∙ i g1) ≡⟨ jc _ _ ⟩
                j (i g0) ∘ j (i g1) ∎

compIso : ∀ {ℓ} {F G H : Group ℓ} (I : Iso F G) (J : Iso G H) → Iso F H
compIso {ℓ} {F} {G} {H}
        (iso F→G G→F fg gf) (iso G→H H→G gh hg ) = iso F→H H→F sec ret
  where
    F→H : morph F H
    F→H = compMorph {ℓ} {F} {G} {H} F→G G→H

    H→F : morph H F
    H→F = compMorph {ℓ} {H} {G} {F} H→G G→F

    open Group

    f→h : F .type → H .type
    f→h = F→H .fst

    f→g : F .type → G .type
    f→g = F→G .fst

    g→h : G .type → H .type
    g→h = G→H .fst

    h→f : H .type → F .type
    h→f = H→F .fst

    h→g : H .type → G .type
    h→g = H→G .fst

    g→f : G .type → F .type
    g→f = G→F .fst

    sec : I.section f→h h→f
    sec h = f→h (h→f h) ≡⟨ cong g→h (fg (h→g h)) ⟩
             g→h (h→g h) ≡⟨ gh _ ⟩
             h ∎

    ret : I.retract f→h h→f
    ret f = h→f (f→h f) ≡⟨ cong g→f (hg (f→g f)) ⟩
             g→f (f→g f) ≡⟨ gf _ ⟩
             f ∎
