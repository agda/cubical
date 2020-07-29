{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Group.Base where

open import Cubical.Foundations.Prelude hiding ( comp )
import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Foundations.Equiv.HalfAdjoint as HAE
open import Cubical.Data.Sigma hiding (comp)
open import Cubical.Functions.Subtype
open import Cubical.Data.NatPlusOne

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



{- Proof that inv (g h) ≡ (inv h) (inv g) -}
invComp : {ℓ : Level} {(group type _ (group-struct _ inv _∘_ _ _ _ _ _)) : Group ℓ} (g g' : type) → inv (g ∘ g') ≡ inv g' ∘ inv g
invComp {_} {group type _ (group-struct _ inv _∘_ lUnit rUnit assoc lCancel rCancel)} g g' =
  sym (rUnit (inv (g ∘ g'))) ∙∙
  cong (inv (g ∘ g') ∘_) ((sym (rCancel g)) ∙∙
      cong (_∘ (inv g)) (sym (rUnit g)) ∙∙
      cong (λ z → (g ∘ z) ∘ (inv g)) (sym (rCancel g')) ∙∙
      cong (_∘ (inv g)) (sym (assoc g g' (inv g'))) ∙∙
      assoc (g ∘ g') (inv g') (inv g)) ∙∙
  sym (assoc (inv (g ∘ g')) (g ∘ g') ((inv g') ∘ (inv g))) ∙∙
  cong (_∘ ((inv g') ∘ (inv g))) (lCancel (g ∘ g')) ∙∙
  lUnit ((inv g') ∘ (inv g))

{- Proof that inv id ≡ id -}
invId : {ℓ : Level} ((group type _ (group-struct id inv _ _ _ _ _  _)) : Group ℓ) → inv id ≡ id
invId {_} (group _ _ (group-struct id inv _ _ rUnit _ lCancel _)) = sym (rUnit (inv id)) ∙ (lCancel id)

isMorph : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H)) → Type (ℓ-max ℓ ℓ')
isMorph (group G Gset (group-struct _ _ _⊙_ _ _ _ _ _))
        (group H Hset (group-struct _ _ _∘_ _ _ _ _ _)) f
        = (g0 g1 : G) → f (g0 ⊙ g1) ≡ (f g0) ∘ (f g1)

morph : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
morph G H = Σ (Group.type G → Group.type H) (isMorph G H)


{- proof that group homomorphisms satisfy f id ≡ id via
f id ≡ comp (f id) id ≡ comp (f id) (comp (f id) (inv (f id))) ≡ comp (comp (f id) (f id)) (inv (f id)) ≡ comp (f id) (inv (f id)) ≡ id -}
morphId : {ℓ ℓ' : Level} {G : Group ℓ} {H : Group ℓ'} (f : morph G H)
  → f .fst (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc H)
morphId {G = group _ _ (group-struct idG _ _ lUnitG _ _ _ _)}
        {H = group _ _ (group-struct _ invH compH _ rUnitH assocH _ rCancelH )} (f , morphf) =
        sym (rUnitH (f idG)) ∙∙ sym (cong (compH (f idG)) (rCancelH (f idG))) ∙∙ sym (assocH (f idG) (f idG) (invH (f idG)) )
        ∙∙ cong (λ x → compH x (invH (f idG))) ((sym (morphf idG idG)) ∙ (cong f (lUnitG idG))) ∙∙ (rCancelH (f idG))

{- proof that group homomorphisms satisfy f (inv g) ≡ inv (f g) via
f (inv g) ≡ comp (f (inv g)) id ≡ comp (f (inv g)) (comp (f g) (inv (f g))) ≡ comp (f (inv g) (f g)) (inv (f g)) ≡ id (inv (f g)) ≡ inv (f g) -}
morphInv : {ℓ ℓ' : Level} {G : Group ℓ} {H : Group ℓ'} (f : morph G H) (g : Group.type G) → f .fst (isGroup.inv (Group.groupStruc G) g) ≡ isGroup.inv (Group.groupStruc H) (f .fst g)
morphInv {G = group typeG setG (group-struct idG invG compG lUnitG rUnitG assocG lCancelG rCancelG)}
         {H = group typeH setH (group-struct idH invH compH lUnitH rUnitH assocH lCancelH rCancelH)} (f , morphf) g =
         sym (rUnitH (f (invG g))) ∙∙ cong (compH (f (invG g))) (sym (rCancelH (f g))) ∙∙ (sym (assocH (f (invG g)) (f g) (invH (f g))))
         ∙∙ cong (λ x → compH x (invH (f g))) ((sym (morphf (invG g) g)) ∙ (cong f (lCancelG g) ∙ (morphId {G = G} {H = H} (f , morphf)))) ∙∙ lUnitH (invH (f g))
         where
           -- no better way to define those implicit arguments?
           G = group typeG setG (group-struct idG invG compG lUnitG rUnitG assocG lCancelG rCancelG)
           H = group typeH setH (group-struct idH invH compH lUnitH rUnitH assocH lCancelH rCancelH)



{-- minimal axioms for subgroup --}
record Subgroup {ℓ} (ℓ' : Level) (G : Group ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor subgroup
  field
    typeProp : Subtype ℓ' (Group.type G)
  type = Subtype→Type typeProp
  _∘_ = isGroup.comp (Group.groupStruc G)
  inv = isGroup.inv (Group.groupStruc G)
  id = isGroup.id (Group.groupStruc G)

  field
    subId : typeProp id .fst
    compClosed : (g g' : type) → typeProp ((fst g) ∘ (fst g')) .fst
    invClosed : (g : type) → typeProp (inv (fst g)) .fst

{-- Proves the other group axioms of a subgroup --}
Subgroup→Group : {ℓ ℓ' : Level} {G : Group ℓ} (H : Subgroup ℓ' G) → Group (ℓ-max ℓ ℓ')
Subgroup→Group {ℓ = ℓ} {G = group type setStruc (group-struct id inv comp lUnit rUnit assoc lCancel rCancel)} (subgroup typeProp subId compClosed invClosed) =
  group
    typ
    (subtypePreservesHLevel {n = (1+ 1)} setStruc typeProp) -- subtypes of sets are sets
    (group-struct
      (id , subId)
      (λ hp → inv (fst hp) , invClosed hp)
      (λ hp hp' → (comp (fst hp) (fst hp')) , compClosed hp hp')
      (λ hp → ΣPathP (lUnit (fst hp) , isProp→PathP (λ i → snd (typeProp (lUnit (fst hp) i))) (compClosed (id , subId) hp) (snd hp)))
      (λ hp → ΣPathP (rUnit (fst hp) , isProp→PathP (λ i → snd (typeProp (rUnit (fst hp) i))) (compClosed hp (id , subId)) (snd hp)))
      (λ ap bp cp → ΣPathP (assoc (fst ap) (fst bp) (fst cp) , isProp→PathP (λ i → snd (typeProp (assoc (fst ap) (fst bp) (fst cp) i))) (compClosed (comp (fst ap) (fst bp) , compClosed ap bp) cp) (compClosed ap (comp (fst bp) (fst cp) , compClosed bp cp))))
      (λ hp → ΣPathP (lCancel (fst hp) , isProp→PathP (λ i → snd (typeProp (lCancel (fst hp) i))) (compClosed (inv (fst hp) , invClosed hp) hp) subId))
      λ hp → ΣPathP (rCancel (fst hp) , isProp→PathP (λ i → snd (typeProp (rCancel (fst hp) i))) (compClosed hp (inv (fst hp) , invClosed hp)) subId))
  where
    typ = Subtype→Type typeProp

{- property of a subgroup being normal -}
isNormalSubgroup : {ℓ ℓ' : Level} (G : Group ℓ) (N : Subgroup ℓ' G) → Type (ℓ-max ℓ ℓ')
isNormalSubgroup G N
  =  (g : Group.type G) → (n : NType) → fst (P ((g ∘ (fst n)) ∘ (inv g))) 
  where
    P = Subgroup.typeProp N
    NType = Subtype→Type P
    _∘_ = isGroup.comp (Group.groupStruc G)
    inv = isGroup.inv (Group.groupStruc G)

{- proof that the kernel is a subgroup -}
ker : {ℓ ℓ' : Level} {G : Group ℓ} {H : Group ℓ'} (f : morph G H) → Subgroup ℓ' G
ker {G = group typeG setG (group-struct idG invG compG lUnitG rUnitG assocG lCancelG rCancelG )}
  {H = group typeH setH (group-struct idH invH compH lUnitH rUnitH assocH lCancelH rCancelH )} (f , morphf)
  = subgroup
    (λ g → (f g ≡ idH) , setH (f g) idH) -- typeProp
    (morphId {G = G} {H = H} (f , morphf)) -- subId
     (λ gp gp' → (morphf (fst gp) (fst gp')) ∙∙ (cong (λ x → compH x (f (fst gp'))) (snd gp)) ∙∙ cong (compH idH) (snd gp') ∙ lUnitH idH) -- compClosed, split on left is ugly
    λ gp → (morphInv {G = G} {H = H} (f , morphf) (fst gp)) ∙∙ (cong invH (snd gp)) ∙∙ sym (rUnitH (invH idH)) ∙ lCancelH idH -- invClosed, split on left is ugly
    where
      G = group typeG setG (group-struct idG invG compG lUnitG rUnitG assocG lCancelG rCancelG)
      H = group typeH setH (group-struct idH invH compH lUnitH rUnitH assocH lCancelH rCancelH)

{- Proof that Kernel is a normal subgroup -}
kerIsNormal : {ℓ ℓ' : Level} {G : Group ℓ} {H : Group ℓ'} (f : morph G H) → isNormalSubgroup G (ker {H = H} f)
kerIsNormal {G = G} {H = H} (f , f*) g (n , n*) =
  f* (g ∘G n) (invG g) ∙∙
  cong (_∘H (f (invG g))) (f* g n) ∙∙
  cong (λ z → ((f g) ∘H z) ∘H (f (invG g))) n* ∙∙
  cong (_∘H (f (invG g))) (rUnitH (f g)) ∙∙
  cong ((f g) ∘H_) (morphInv {G = G} {H = H} ((f , f*)) g) ∙
  rCancelH (f g)
  where
    _∘G_ = isGroup.comp (Group.groupStruc G)
    invG = isGroup.inv (Group.groupStruc G)
    _∘H_ = isGroup.comp (Group.groupStruc H)
    invH = isGroup.inv (Group.groupStruc H)
    rUnitH = isGroup.rUnit (Group.groupStruc H)
    rCancelH = isGroup.rCancel (Group.groupStruc H)

{-- computes the restriction of a morphism of groups to a subgroup --}
restrictGroupMorph : {ℓG ℓG' ℓH : Level} {G : Group ℓG} {H : Group ℓH} (f : morph G H) (S : Subgroup ℓG' G) → morph (Subgroup→Group S) H
restrictGroupMorph (f , f*) S = (restrictFun f {subA = Subgroup.typeProp S}) , λ g₀ g₁ → f* (fst g₀) (fst g₁)

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
