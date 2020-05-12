{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Base where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.HITs.PropositionalTruncation hiding (map)

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

morph0→0 : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H))
           → isMorph G H f
           → f (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc H)
morph0→0 (group G strucG (group-struct idG invG compG lUnitG rUnitG assocG lCancelG rCancelG))
          (group H strucH (group-struct idH invH compH lUnitH rUnitH assocH lCancelH rCancelH)) f morph =
  f idG                                               ≡⟨ sym (rUnitH (f idG)) ⟩
  compH (f idG) idH                                   ≡⟨ (λ i → compH (f idG) (rCancelH (f idG) (~ i))) ⟩
  compH (f idG) (compH (f idG) (invH (f idG)))        ≡⟨ sym (assocH (f idG) (f idG) (invH (f idG))) ⟩
  compH (compH (f idG) (f idG)) (invH (f idG))        ≡⟨ sym (cong (λ x → compH x (invH (f idG))) (sym (cong f (lUnitG idG)) ∙ morph idG idG)) ⟩
  compH (f idG) (invH (f idG))                        ≡⟨ rCancelH (f idG) ⟩
  idH ∎

morphMinus : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H))
           → isMorph G H f
           → (g : Group.type G) → f (isGroup.inv (Group.groupStruc G) g) ≡ isGroup.inv (Group.groupStruc H) (f g)
morphMinus G H f morph g =
  let idG = isGroup.id (Group.groupStruc G)
      idH = isGroup.id (Group.groupStruc H)
      invG = isGroup.inv (Group.groupStruc G)
      invH = isGroup.inv (Group.groupStruc H)
      lCancelG = isGroup.lCancel (Group.groupStruc G)
      rCancelH = isGroup.rCancel (Group.groupStruc H)
      lUnitH = isGroup.lUnit (Group.groupStruc H)
      rUnitH = isGroup.rUnit (Group.groupStruc H)
      assocH = isGroup.assoc (Group.groupStruc H)
      compG = isGroup.comp (Group.groupStruc G)
      compH = isGroup.comp (Group.groupStruc H)
      helper : compH (f (invG g)) (f g) ≡ idH
      helper = sym (morph (invG g) g) ∙ (λ i → f (lCancelG g i)) ∙ morph0→0 G H f morph
  in f (invG g)                                                   ≡⟨ sym (rUnitH (f (invG g))) ⟩
     compH (f (invG g)) idH                                       ≡⟨ (λ i → compH (f (invG g)) (rCancelH (f g) (~ i))) ⟩
     compH (f (invG g)) (compH (f g) (invH (f g)))                ≡⟨ sym (assocH (f (invG g)) (f g) (invH (f g))) ⟩
     compH (compH (f (invG g)) (f g)) (invH (f g))                ≡⟨ cong (λ x → compH x (invH (f g))) helper ⟩
     compH idH (invH (f g))                                       ≡⟨ lUnitH (invH (f g)) ⟩
     invH (f g) ∎



-- sym (rUnitH (f (invG g))) ∙ (λ i → compH (f (invG g)) (rCancelH (f g) (~ i))) ∙ sym (assocH (f (invG g)) (f g) (invH (f g))) ∙ cong (λ x → compH x (invH (f g))) helper ∙ lUnitH (invH (f g))

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


isInIm : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H)
       → Group.type H → Type _
isInIm G H ϕ h = ∃[ g ∈ Group.type G ] ϕ g ≡ h

isInKer : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H)
       → Group.type G → Type _
isInKer G H ϕ g = ϕ g ≡ isGroup.id (Group.groupStruc H)



{- direct products of groups -}
dirProd : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Group (ℓ-max ℓ ℓ')
Group.type (dirProd (group A setA strucA) (group B setB strucB)) = A × B
Group.setStruc (dirProd (group A setA strucA) (group B setB strucB)) = isOfHLevelProd 2 setA setB
isGroup.id (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) =
  (isGroup.id strucA) , (isGroup.id strucB)
isGroup.inv (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) =
  map (isGroup.inv strucA) (isGroup.inv strucB)
isGroup.comp (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a1 , b1) (a2 , b2) =
  (isGroup.comp strucA a1 a2) , isGroup.comp strucB b1 b2
isGroup.lUnit (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a , b) i =
  (isGroup.lUnit strucA a i) , (isGroup.lUnit strucB b i)
isGroup.rUnit (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a , b) i =
  (isGroup.rUnit strucA a i) , (isGroup.rUnit strucB b i)
isGroup.assoc (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a1 , b1) (a2 , b2) (a3 , b3) i =
  (isGroup.assoc strucA a1 a2 a3 i) , (isGroup.assoc strucB b1 b2 b3 i)
isGroup.lCancel (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a , b) i =
  (isGroup.lCancel strucA a i) , (isGroup.lCancel strucB b i)
isGroup.rCancel (Group.groupStruc (dirProd (group A setA strucA) (group B setB strucB))) (a , b) i =
  (isGroup.rCancel strucA a i) , (isGroup.rCancel strucB b i)
