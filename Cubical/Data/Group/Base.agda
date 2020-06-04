{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Base where

open import Cubical.Foundations.Prelude renaming (comp to comp')
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.HITs.PropositionalTruncation hiding (map)

import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Foundations.Equiv.HalfAdjoint as HAE

open import Cubical.HITs.SetQuotients as sq

record isGroup {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
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
  no-eta-equality
  constructor group
  field
    type : Type ℓ
    setStruc : isSet type
    groupStruc : isGroup type

isMorph : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H)) → Type (ℓ-max ℓ ℓ')
isMorph G H f = (g0 g1 : Group.type G) → f (isGroup.comp (Group.groupStruc G) g0 g1) ≡ isGroup.comp (Group.groupStruc H) (f g0) (f g1)

record morph {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor mph
  field
    fun : Group.type G → Group.type H
    ismorph : isMorph G H fun
  

open import Cubical.Data.Sigma hiding (_×_ ; comp)


isInIm : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H)
       → Group.type H → Type _
isInIm G H ϕ h = ∃[ g ∈ Group.type G ] ϕ g ≡ h

isInKer : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H)
       → Group.type G → Type _
isInKer G H ϕ g = ϕ g ≡ isGroup.id (Group.groupStruc H)


isSurjective : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H → Type _
isSurjective G H ϕ = (x : Group.type H) → isInIm G H (morph.fun ϕ) x 

isInjective : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H → Type _
isInjective G H ϕ = (x : Group.type G) → isInKer G H (morph.fun ϕ) x → x ≡ isGroup.id (Group.groupStruc G)


-0≡0 : ∀ {ℓ} {G : Group ℓ} → isGroup.inv (Group.groupStruc G) (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc G)
-0≡0 {G = G} = sym (isGroup.lUnit (Group.groupStruc G) _) ∙ isGroup.rCancel (Group.groupStruc G) _

{- morphisms takes id to id -}
morph0→0 : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H))
           → isMorph G H f
           → f (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc H)
morph0→0 G' H' f ismorph = 0→0
  where
  open Group
  open isGroup
  G = Group.groupStruc G'
  H = Group.groupStruc H'

  0→0 : f (id G) ≡ id H
  0→0 =
    f (id G)                                               ≡⟨ sym (rUnit H (f (id G))) ⟩
    comp H (f (id G)) (id H)                                   ≡⟨ (λ i → comp H (f (id G)) (rCancel H (f (id G)) (~ i))) ⟩
    comp H (f (id G)) (comp H (f (id G)) (inv H (f (id G))))        ≡⟨ sym (assoc H (f (id G)) (f (id G)) (inv H (f (id G)))) ⟩
    comp H (comp H (f (id G)) (f (id G))) (inv H (f (id G)))        ≡⟨ sym (cong (λ x → comp H x (inv H (f (id G)))) (sym (cong f (lUnit G (id G))) ∙ ismorph (id G) (id G))) ⟩
    comp H (f (id G)) (inv H (f (id G)))                        ≡⟨ rCancel H (f (id G)) ⟩
    id H ∎
  


{- a morphism ϕ satisfies ϕ(- a) = - ϕ(a)  -}
morphMinus : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (f : (Group.type G → Group.type H))
           → isMorph G H f
           → (g : Group.type G) → f (isGroup.inv (Group.groupStruc G) g) ≡ isGroup.inv (Group.groupStruc H) (f g)
morphMinus G H f mf g =
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
      helper = sym (mf (invG g) g) ∙ (λ i → f (lCancelG g i)) ∙ morph0→0 G H f mf -- sym (morph (invG g) g) ∙ (λ i → f (lCancelG g i)) ∙ morph0→0 G H f morph
  in f (invG g)                                                   ≡⟨ sym (rUnitH (f (invG g))) ⟩
     compH (f (invG g)) idH                                       ≡⟨ (λ i → compH (f (invG g)) (rCancelH (f g) (~ i))) ⟩
     compH (f (invG g)) (compH (f g) (invH (f g)))                ≡⟨ sym (assocH (f (invG g)) (f g) (invH (f g))) ⟩
     compH (compH (f (invG g)) (f g)) (invH (f g))                ≡⟨ cong (λ x → compH x (invH (f g))) helper ⟩
     compH idH (invH (f g))                                       ≡⟨ lUnitH (invH (f g)) ⟩
     invH (f g) ∎

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
    rightInv : I.section (morph.fun fun) (morph.fun inv)
    leftInv : I.retract (morph.fun fun) (morph.fun inv)

record Iso' {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso'
  field
    isoSet : I.Iso (Group.type G) (Group.type H)
    isoSetMorph : isMorph G H (I.Iso.fun isoSet)

record Iso'' {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso''
  field
    ϕ : morph A B
    inj : isInjective A B ϕ
    surj : isSurjective A B ϕ

_≃_ : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (morph A B) \ f → (E.isEquiv (morph.fun f))

Iso'→Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso' G H → Iso G H
morph.fun (Iso.fun (Iso'→Iso {G = G} {H = H} iso1)) = I.Iso.fun (Iso'.isoSet iso1)
morph.ismorph (Iso.fun (Iso'→Iso {G = G} {H = H} iso1)) = Iso'.isoSetMorph iso1
morph.fun (Iso.inv (Iso'→Iso {G = G} {H = H} iso1)) = I.Iso.inv (Iso'.isoSet iso1)
morph.ismorph (Iso.inv (Iso'→Iso {G = G} {H = H} iso1)) a b =
    cong₂ (λ x y → ψ (comp H' x y))
          (sym (I.Iso.rightInv (Iso'.isoSet iso1) _))
          (sym (I.Iso.rightInv (Iso'.isoSet iso1) _))
  ∙ cong ψ (sym (Iso'.isoSetMorph iso1 _ _))
  ∙ I.Iso.leftInv (Iso'.isoSet iso1) _
  where
  open Iso'
  open isGroup
  H' = Group.groupStruc H
  ψ = I.Iso.inv (Iso'.isoSet iso1)

Iso.rightInv (Iso'→Iso {G = G} {H = H} iso1) = I.Iso.rightInv (Iso'.isoSet iso1)
Iso.leftInv (Iso'→Iso {G = G} {H = H} iso1) = I.Iso.leftInv (Iso'.isoSet iso1)

Equiv→Iso' : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → G ≃ H → Iso' G H
Equiv→Iso' {G = group G Gset Ggroup}
           {H = group H Hset Hgroup}
           e = iso' i' (morph.ismorph (e .fst))
  where
    e' : G E.≃ H
    e' = (morph.fun (e .fst)) , (e .snd)

    i' : I.Iso G H
    i' = E.equivToIso e'

compMorph : ∀ {ℓ ℓ' ℓ''} {F : Group ℓ} {G : Group ℓ'} {H : Group ℓ''} (I : morph F G) (J : morph G H) → morph F H
morph.fun (compMorph I J) x = morph.fun J (morph.fun I x)
morph.ismorph (compMorph {F = F} {G = G} {H = H} I J) g0 g1 =
    cong (morph.fun J) (morph.ismorph I g0 g1)
  ∙ morph.ismorph J (morph.fun I g0) (morph.fun I g1)

compIso : ∀ {ℓ} {F G H : Group ℓ} (I : Iso F G) (J : Iso G H) → Iso F H
Iso.fun (compIso {ℓ} {F} {G} {H} iso1 iso2) = compMorph (Iso.fun iso1) (Iso.fun iso2)
Iso.inv (compIso {ℓ} {F} {G} {H} iso1 iso2) = compMorph (Iso.inv iso2) (Iso.inv iso1)
Iso.rightInv (compIso {ℓ} {F} {G} {H} iso1 iso2) b =
  cong (morph.fun (Iso.fun iso2)) (Iso.rightInv iso1 _) ∙ Iso.rightInv iso2 _
Iso.leftInv (compIso {ℓ} {F} {G} {H} iso1 iso2) b =
  cong (morph.fun (Iso.inv iso1)) (Iso.leftInv iso2 _) ∙ Iso.leftInv iso1 _

idIso : ∀ {ℓ} (G : Group ℓ) → Iso G G
Iso.fun (idIso G) = mph (λ x → x) (λ _ _ → refl)
Iso.inv (idIso G) = mph (λ x → x) (λ _ _ → refl)
Iso.rightInv (idIso G) _ = refl
Iso.leftInv (idIso G) _ = refl

invIso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso G H → Iso H G
Iso.fun (invIso is) = Iso.inv is
Iso.inv (invIso is) = Iso.fun is
Iso.rightInv (invIso is) = Iso.leftInv is
Iso.leftInv (invIso is) = Iso.rightInv is


Iso''→Iso : ∀ {ℓ ℓ'} {A : Group ℓ} {B : Group ℓ'} → Iso'' A B → Iso A B
Iso''→Iso {A = A} {B = B} is =
  Iso'→Iso
    (iso' (I.iso (morph.fun (Iso''.ϕ is))
                 (λ b → rec (helper b) (λ a → a) (Iso''.surj is b) .fst)
                 (λ b → rec (helper b) (λ a → a) (Iso''.surj is b) .snd)
                 λ b i → rec (helper (morph.fun (Iso''.ϕ is) b)) (λ a → a) (propTruncIsProp (Iso''.surj is (morph.fun (Iso''.ϕ is) b)) ∣ b , refl ∣ i) .fst)
          (morph.ismorph (Iso''.ϕ is)))
  where
  helper : (b : _) → isProp (Σ (Group.type A) (λ a → (morph.fun (Iso''.ϕ is)) a ≡ b))
  helper b (a1 , pf1) (a2 , pf2) =
    ΣProp≡ (λ _ → isOfHLevelPath' 1 (Group.setStruc B) _ _)
           fstId
    where
    open Group
    open isGroup
    open morph
    A' = groupStruc A
    B' = groupStruc B
    ϕ = morph.fun (Iso''.ϕ is)
    ϕmf = morph.ismorph (Iso''.ϕ is)

    fstIdHelper : isGroup.comp (Group.groupStruc A) a1 (isGroup.inv (Group.groupStruc A) a2)
                ≡ isGroup.id (Group.groupStruc A)
    fstIdHelper =
      let -A = isGroup.inv (Group.groupStruc A)
          -B = isGroup.inv (Group.groupStruc B)
          rCancelB = isGroup.rCancel (Group.groupStruc B)
          _+B_ = isGroup.comp (Group.groupStruc B)
      in Iso''.inj is _
                   (ϕmf a1 (inv A' a2)
                  ∙ cong (λ x → comp B' (ϕ a1) x) (morphMinus A B ϕ ϕmf a2)
                  ∙ cong (λ x → comp B' x (inv B' (ϕ a2))) (pf1 ∙ sym pf2)
                  ∙ rCancel B' (ϕ a2))
    fstId : a1 ≡ a2
    fstId =
      a1 ≡⟨ sym (rUnit A' a1) ⟩
      comp A' a1 (id A') ≡⟨ cong (λ x → comp A' a1 x) (sym (lCancel A' a2)) ⟩
      comp A' a1 (comp A' (inv A' a2) a2) ≡⟨ sym (assoc A' a1 (inv A' a2) a2) ⟩
      comp A' (comp A' a1 (inv A' a2)) a2 ≡⟨ cong (λ x → comp A' x a2) fstIdHelper ⟩
      comp A' (id A') a2 ≡⟨ lUnit A' a2 ⟩
      a2 ∎


-- -- Injectivity and surjectivity in terms of exact sequences

-- {-
-- exactInjectiveL : ∀ {ℓ ℓ' ℓ''} (E : Group ℓ'') (F : Group ℓ'') (G : Group ℓ) (H : Group ℓ')
--                 (ϕ : morph E F) (ψ : morph F G) (ξ : morph G H) 
--               → isSurjective E F ϕ
--               → ((x : Group.type G) → isInKer G H (fst ξ) x → (isInIm F G (fst ψ) x))
--               → isProp (Group.type E)
--               → isInjective G H ξ
-- exactInjectiveL (group E _ (group-struct idE _ _ _ _ _ _ _)) F G H
--                (ϕ , mfϕ) (ψ , mfψ) _ surjϕ ker⊂im isPropE x inker =
--                  rec (Group.setStruc G _ _)
--                      (λ {(f , id) → sym id ∙ cong ψ (isPropF f (isGroup.id (Group.groupStruc F))) ∙ morph0→0 F G ψ mfψ})
--                      (ker⊂im x inker)
--   where
--   isPropF : isProp (Group.type F)
--   isPropF a b = rec (Group.setStruc F _ _)
--                      (λ {(c , id-c) → rec (Group.setStruc F _ _)
--                                            (λ {(d , id-d) → sym id-c ∙ cong ϕ (isPropE c d) ∙ id-d})
--                                            (surjϕ b) })
--                      (surjϕ a)


-- exactSurjectiveR : ∀ {ℓ ℓ' ℓ''} (E : Group ℓ'') (F : Group ℓ'') (G : Group ℓ) (H : Group ℓ')
--                   (ϕ : morph E F) (ψ : morph F G) (ξ : morph G H) 
--                 → isInjective G H ξ
--                 → ((x : Group.type F) → (isInKer F G (fst ψ) x) → isInIm E F (fst ϕ) x)
--                 → isProp (Group.type H)
--                 → isSurjective E F ϕ
-- exactSurjectiveR E F (group G GSet (group-struct idG -G _+G_ lUnitG rUnitG assocG lCancelG rCancelG))
--                 (group H _ (group-struct idH _ _ _ _ _ _ _))
--                 (ϕ , mfϕ) (ψ , mfψ) (ξ , mfξ) isInjξ ker⊂im isPropH x = ker⊂im x (isPropF (ψ x) idG)

--   where
--   isPropF : isProp G
--   isPropF a b = sym (rUnitG a)
--               ∙ cong (a +G_) (sym (lCancelG b))
--               ∙ sym (assocG a (-G b) b)
--               ∙ cong (λ x → x +G b) helper
--               ∙ lUnitG b
--     where
--     helper : a +G (-G b) ≡ idG
--     helper = isInjξ (a +G (-G b)) (isPropH (ξ (a +G -G b)) idH )

-- exactSurjectiveR' : ∀ {ℓ ℓ' ℓ''} (E : Group ℓ) (F : Group ℓ') (G : Group ℓ'')
--                   (ϕ : morph E F) (ψ : morph F G)
--                 → ((x : Group.type F) → (isInKer F G (fst ψ) x) → isInIm E F (fst ϕ) x)
--                 → isProp (Group.type G)
--                 → isSurjective E F ϕ
-- exactSurjectiveR' E F (group G GSet (group-struct idG -G _+G_ lUnitG rUnitG assocG lCancelG rCancelG))
--                 (ϕ , mfϕ) (ψ , mfψ) ker⊂im isPropG x = ker⊂im x (isPropG (ψ x) idG)
-- -}




