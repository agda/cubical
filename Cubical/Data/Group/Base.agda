{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Group.Base where

open import Cubical.Foundations.Prelude renaming (comp to comp')
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.Data.Sigma hiding (_×_ ; comp)

import Cubical.Foundations.Isomorphism as I
import Cubical.Foundations.Equiv as E
import Cubical.Foundations.Equiv.HalfAdjoint as HAE

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

isInIm : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (morph G H)
       → Group.type H → Type (ℓ-max ℓ ℓ')
isInIm G H ϕ h = ∃[ g ∈ Group.type G ] (morph.fun ϕ g) ≡ h

isInKer : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H
       → Group.type G → Type ℓ'
isInKer G H ϕ g = (morph.fun ϕ g) ≡ isGroup.id (Group.groupStruc H)

isSurjective : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H → Type (ℓ-max ℓ ℓ')
isSurjective G H ϕ = (x : Group.type H) → isInIm G H ϕ x

isInjective : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → morph G H → Type (ℓ-max ℓ ℓ')
isInjective G H ϕ = (x : Group.type G) → isInKer G H ϕ x → x ≡ isGroup.id (Group.groupStruc G)

-0≡0 : ∀ {ℓ} {G : Group ℓ} → isGroup.inv (Group.groupStruc G) (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc G)
-0≡0 {G = G} = sym (isGroup.lUnit (Group.groupStruc G) _) ∙ isGroup.rCancel (Group.groupStruc G) _

morph0→0 : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') (f : morph G H)
           → morph.fun f (isGroup.id (Group.groupStruc G)) ≡ isGroup.id (Group.groupStruc H)
morph0→0 G' H' f' = 0→0
  where
  open Group
  open isGroup
  G = groupStruc G'
  H = groupStruc H'
  f = morph.fun f'
  ismorph = morph.ismorph f'

  0→0 : f (id G) ≡ id H
  0→0 =
    f (id G)                                                   ≡⟨ sym (rUnit H (f (id G))) ⟩
    comp H (f (id G)) (id H)                                   ≡⟨ (λ i → comp H (f (id G)) (rCancel H (f (id G)) (~ i))) ⟩
    comp H (f (id G)) (comp H (f (id G)) (inv H (f (id G))))   ≡⟨ sym (assoc H (f (id G)) (f (id G)) (inv H (f (id G)))) ⟩
    comp H (comp H (f (id G)) (f (id G))) (inv H (f (id G)))   ≡⟨ sym (cong (λ x → comp H x (inv H (f (id G)))) (sym (cong f (lUnit G (id G))) ∙ ismorph (id G) (id G))) ⟩
    comp H (f (id G)) (inv H (f (id G)))                       ≡⟨ rCancel H (f (id G)) ⟩
    id H ∎

{- a morphism ϕ satisfies ϕ(- a) = - ϕ(a)  -}
morphMinus : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') → (ϕ : morph G H)
           → (g : Group.type G) → morph.fun ϕ (isGroup.inv (Group.groupStruc G) g) ≡ isGroup.inv (Group.groupStruc H) (morph.fun ϕ g)
morphMinus G' H' ϕ g = mainLemma
  where
  open Group
  open isGroup
  H = groupStruc H'
  G = groupStruc G'
  f = morph.fun ϕ

  helper : comp H (f (inv G g)) (f g) ≡ id H
  helper = sym (morph.ismorph ϕ (inv G g) g) ∙∙ cong f (lCancel G g) ∙∙ morph0→0 G' H' ϕ

  mainLemma : f (inv G g) ≡ inv H (f g)
  mainLemma = f (inv G g)                                   ≡⟨ sym (rUnit H (f (inv G g))) ⟩
              comp H (f (inv G g)) (id H)                                       ≡⟨ cong (comp H (f (inv G g))) (sym (rCancel H (f g))) ⟩
              comp H (f (inv G g)) (comp H (f g) (inv H (f g)))                ≡⟨ sym (assoc H (f (inv G g)) (f g) (inv H (f g))) ⟩
              comp H (comp H (f (inv G g)) (f g)) (inv H (f g))                ≡⟨ cong (λ x → comp H x (inv H (f g))) helper ⟩
              comp H (id H) (inv H (f g))                                       ≡⟨ lUnit H (inv H (f g)) ⟩
              inv H (f g) ∎

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

----------- Equivalent notions of isomorphisms --------------

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

record Iso''' {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') : Type (ℓ-max ℓ ℓ') where -- Should perhaps replace Iso'. Appears to compute somewhat better.
  constructor iso'''
  field
    fun : morph G H
    inv : Group.type H → Group.type G
    rightInv : I.section (morph.fun fun) inv
    leftInv : I.retract (morph.fun fun) inv

record SES {ℓ ℓ' ℓ'' ℓ'''} (A : Group ℓ) (B : Group ℓ') (leftGr : Group ℓ'') (rightGr : Group ℓ''')
           : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))) where
  constructor ses
  field
    isTrivialLeft : isProp (Group.type leftGr)
    isTrivialRight : isProp (Group.type rightGr)

    left : morph leftGr A
    right : morph B rightGr
    ϕ : morph A B

    Ker-ϕ⊂Im-left : (x : Group.type A) --
                  → isInKer A B ϕ x
                  → isInIm leftGr A left x
    Ker-right⊂Im-ϕ : (x : Group.type B) --
                   → isInKer B rightGr right x
                   → isInIm A B ϕ x

_≃_ : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (morph A B) \ f → (E.isEquiv (morph.fun f))

-----------
compMorph : ∀ {ℓ ℓ' ℓ''} {F : Group ℓ} {G : Group ℓ'} {H : Group ℓ''} (I : morph F G) (J : morph G H) → morph F H
morph.fun (compMorph I J) x = morph.fun J (morph.fun I x)
morph.ismorph (compMorph {F = F} {G = G} {H = H} I J) g0 g1 =
    cong (morph.fun J) (morph.ismorph I g0 g1)
  ∙ morph.ismorph J (morph.fun I g0) (morph.fun I g1)

compIso : ∀ {ℓ} {F G H : Group ℓ} (I : Iso F G) (J : Iso G H) → Iso F H
Iso.fun (compIso iso1 iso2) = compMorph (Iso.fun iso1) (Iso.fun iso2)
Iso.inv (compIso iso1 iso2) = compMorph (Iso.inv iso2) (Iso.inv iso1)
Iso.rightInv (compIso iso1 iso2) b =
  cong (morph.fun (Iso.fun iso2)) (Iso.rightInv iso1 _) ∙ Iso.rightInv iso2 _
Iso.leftInv (compIso iso1 iso2) b =
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

groupIso→Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso G H → I.Iso (Group.type G) (Group.type H)
I.Iso.fun (groupIso→Iso i) = morph.fun (Iso.fun i)
I.Iso.inv (groupIso→Iso i) = morph.fun (Iso.inv i)
I.Iso.rightInv (groupIso→Iso i) = Iso.rightInv i
I.Iso.leftInv (groupIso→Iso i) = Iso.leftInv i


--- Proofs that different notions of ismomorphisms agree ---
Equiv→Iso' : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → G ≃ H → Iso' G H
Iso'.isoSet (Equiv→Iso' {G = G} {H = H} e) = E.equivToIso (morph.fun (e .fst) , e .snd)
Iso'.isoSetMorph (Equiv→Iso' {G = G} {H = H} e) = morph.ismorph (e .fst)

open isGroup
Iso'''→Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso''' G H → Iso G H
Iso.fun (Iso'''→Iso is) = Iso'''.fun is
morph.fun (Iso.inv (Iso'''→Iso is)) = Iso'''.inv is
morph.ismorph (Iso.inv (Iso'''→Iso {G = G} {H = H} is)) a b =
    cong₂ (λ x y → (Iso'''.inv is) (comp (Group.groupStruc H) x y))
          (sym (Iso'''.rightInv is _))
          (sym (Iso'''.rightInv is _))
  ∙ cong (Iso'''.inv is) (sym (morph.ismorph (Iso'''.fun is) _ _))
  ∙ Iso'''.leftInv is _
Iso.rightInv (Iso'''→Iso is) = Iso'''.rightInv is
Iso.leftInv (Iso'''→Iso is) = Iso'''.leftInv is

Iso'→Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} → Iso' G H → Iso G H
morph.fun (Iso.fun (Iso'→Iso iso1)) = I.Iso.fun (Iso'.isoSet iso1)
morph.ismorph (Iso.fun (Iso'→Iso iso1)) = Iso'.isoSetMorph iso1
morph.fun (Iso.inv (Iso'→Iso iso1)) = I.Iso.inv (Iso'.isoSet iso1)
morph.ismorph (Iso.inv (Iso'→Iso {G = G} {H = H} iso1)) a b =
    cong₂ (λ x y → ψ (comp H' x y))
          (sym (I.Iso.rightInv (Iso'.isoSet iso1) _))
          (sym (I.Iso.rightInv (Iso'.isoSet iso1) _))
  ∙ cong ψ (sym (Iso'.isoSetMorph iso1 _ _))
  ∙ I.Iso.leftInv (Iso'.isoSet iso1) _
  where
  H' = Group.groupStruc H
  ψ = I.Iso.inv (Iso'.isoSet iso1)

Iso.rightInv (Iso'→Iso iso1) = I.Iso.rightInv (Iso'.isoSet iso1)
Iso.leftInv (Iso'→Iso iso1) = I.Iso.leftInv (Iso'.isoSet iso1)

open import Cubical.Data.Sigma hiding (comp ; _×_)

Iso''→Iso : ∀ {ℓ ℓ'} {A : Group ℓ} {B : Group ℓ'} → Iso'' A B → Iso A B
Iso''→Iso {A = A} {B = B} is = Iso'''→Iso theIso
  where
  helper : (b : _) → isProp (Σ (Group.type A) (λ a → (morph.fun (Iso''.ϕ is)) a ≡ b))
  helper _ a b =
    Σ≡Prop (λ _ → isOfHLevelPath' 1 (Group.setStruc B) _ _)
           fstId
    where
    open Group
    open morph
    A' = groupStruc A
    B' = groupStruc B

    fstIdHelper : comp (A') (fst a) (inv (A') (fst b))
                ≡ id (A')
    fstIdHelper =
        Iso''.inj is _
                   (morph.ismorph (Iso''.ϕ is) (fst a) (inv A' (fst b))
                  ∙ cong (λ x → comp B' (morph.fun (Iso''.ϕ is) (fst a)) x) (morphMinus A B (Iso''.ϕ is) (fst b))
                  ∙ cong (λ x → comp B' x (inv B' (morph.fun (Iso''.ϕ is) (fst b)))) ((snd a) ∙ sym (snd b))
                  ∙ rCancel B' (morph.fun (Iso''.ϕ is) (fst b)))
    fstId : fst a ≡ fst b
    fstId =
      (fst a)                                              ≡⟨ sym (rUnit A' (fst a)) ⟩
      comp A' (fst a) (id A')                              ≡⟨ cong (λ x → comp A' (fst a) x) (sym (lCancel A' (fst b))) ⟩
      comp A' (fst a) (comp A' (inv A' (fst b)) (fst b))   ≡⟨ sym (assoc A' (fst a) (inv A' (fst b)) (fst b)) ⟩
      comp A' (comp A' (fst a) (inv A' (fst b))) (fst b)   ≡⟨ cong (λ x → comp A' x (fst b)) fstIdHelper ⟩
      comp A' (id A') (fst b)                              ≡⟨ lUnit A' (fst b) ⟩
      (fst b) ∎

  theIso : Iso''' A B
  Iso'''.fun theIso = Iso''.ϕ is
  Iso'''.inv theIso b = rec (helper b) (λ a → a) (Iso''.surj is b) .fst
  Iso'''.rightInv theIso b = rec (helper b) (λ a → a) (Iso''.surj is b) .snd
  Iso'''.leftInv theIso b i = rec (helper (morph.fun (Iso''.ϕ is) b)) (λ a → a)
                                  (propTruncIsProp (Iso''.surj is (morph.fun (Iso''.ϕ is) b)) ∣ b , refl ∣ i) .fst


SES→Iso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} (leftGr : Group ℓ'') (rightGr : Group ℓ''')
        → SES A B leftGr rightGr
        → Iso A B
SES→Iso {A = A} lGr rGr sess =
  Iso''→Iso
    (iso'' (SES.ϕ sess)
           (λ a inker → rec (Group.setStruc A _ _)
                             (λ {(a , p) → sym p ∙ cong (morph.fun (SES.left sess)) (SES.isTrivialLeft sess a _)
                                          ∙ morph0→0 lGr A (SES.left sess)})
                             (SES.Ker-ϕ⊂Im-left sess a inker))
           λ a → SES.Ker-right⊂Im-ϕ sess a (SES.isTrivialRight sess _ _))

--- Some elementary groups ---

open import Cubical.Data.Unit
open Group
trivialGroup : Group ℓ-zero
type trivialGroup = Unit
setStruc trivialGroup = isOfHLevelSuc 1 isPropUnit
id (groupStruc trivialGroup) = tt
inv (groupStruc trivialGroup) _ =  tt
comp (groupStruc trivialGroup) _ _ = tt
lUnit (groupStruc trivialGroup) _ = refl
rUnit (groupStruc trivialGroup) _ = refl
assoc (groupStruc trivialGroup) _ _ _ = refl
lCancel (groupStruc trivialGroup) _ = refl
rCancel (groupStruc trivialGroup) _ = refl

open import Cubical.Data.Int

intGroup : Group ℓ-zero
type intGroup = Int
setStruc intGroup = isSetInt
id (groupStruc intGroup) = pos 0
inv (groupStruc intGroup) = pos 0 -_
comp (groupStruc intGroup) = _+_
lUnit (groupStruc intGroup) a = +-comm (pos 0) a
rUnit (groupStruc intGroup) _ =  refl
assoc (groupStruc intGroup) a b c = sym (+-assoc a b c)
lCancel (groupStruc intGroup) a = minusPlus a 0
rCancel (groupStruc intGroup) a = +-comm a (pos 0 - a) ∙ minusPlus a 0

dirProd : ∀ {ℓ ℓ'} (A : Group ℓ) (B : Group ℓ') → Group (ℓ-max ℓ ℓ')
type (dirProd A B) = type A × type B
setStruc (dirProd A B) = isOfHLevelProd 2 (setStruc A) (setStruc B)
id (groupStruc (dirProd A B)) = id (groupStruc A) , id (groupStruc B)
inv (groupStruc (dirProd A B)) = ×Inv
  where
  ×Inv : _
  ×Inv (a , b) = (inv (groupStruc A) a) , (inv (groupStruc B) b)
comp (groupStruc (dirProd A B)) = ×comp
  where
  ×comp : _
  ×comp (a , b) (c , d) = (comp (groupStruc A) a c) , comp (groupStruc B) b d
lUnit (groupStruc (dirProd A B)) = ×lUnit
  where
  ×lUnit : _
  ×lUnit (a , b) i = lUnit (groupStruc A) a i , lUnit (groupStruc B) b i
rUnit (groupStruc (dirProd A B)) = ×rUnit
  where
  ×rUnit : _
  ×rUnit (a , b) i = rUnit (groupStruc A) a i , rUnit (groupStruc B) b i
assoc (groupStruc (dirProd A B)) = ×assoc
  where
  ×assoc : _
  ×assoc (a , b) (c , d) (e , f) i = (assoc (groupStruc A) a c e i) , (assoc (groupStruc B) b d f i)
lCancel (groupStruc (dirProd A B)) = ×lCancel
  where
  ×lCancel : _
  ×lCancel (a , b) i = (lCancel (groupStruc A) a i) , lCancel (groupStruc B) b i
rCancel (groupStruc (dirProd A B)) = ×rCancel
  where
  ×rCancel : _
  ×rCancel (a , b) i = (rCancel (groupStruc A) a i) , rCancel (groupStruc B) b i


×morph : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''}
       → morph A B → morph C D → morph (dirProd A C) (dirProd B D)
morph.fun (×morph mf1 mf2) = fun
  where
  fun : _
  fun (a , b) = morph.fun mf1 a , morph.fun mf2 b
morph.ismorph (×morph mf1 mf2) = ismf
  where
  ismf : _
  ismf (a , b) (c , d) i = morph.ismorph mf1 a c i , morph.ismorph mf2 b d i

dirProdIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''}
           → Iso A C → Iso B D
           → Iso (dirProd A B) (dirProd C D)
Iso.fun (dirProdIso isoAC isoBD) = ×morph (Iso.fun isoAC) (Iso.fun isoBD)
Iso.inv (dirProdIso isoAC isoBD) = ×morph (Iso.inv isoAC) (Iso.inv isoBD)
Iso.rightInv (dirProdIso isoAC isoBD) = rInv
  where
  rInv : _
  rInv (a , b) = ×≡ (Iso.rightInv isoAC a) (Iso.rightInv isoBD b)
Iso.leftInv (dirProdIso isoAC isoBD) = lInv
  where
  lInv : _
  lInv (a , b) = ×≡ (Iso.leftInv isoAC a) (Iso.leftInv isoBD b)



---
lUnitGroupIso : ∀ {ℓ} {G : Group ℓ} → Iso (dirProd trivialGroup G) G
lUnitGroupIso =
  Iso'''→Iso
    (iso'''
      (mph proj₂ λ { (x , y) (z , w) → refl})
      (λ g → tt , g)
      (λ _ → refl)
      λ _ → ×≡ refl refl)

rUnitGroupIso : ∀ {ℓ} {G : Group ℓ} → Iso (dirProd G trivialGroup) G
rUnitGroupIso =
  Iso'''→Iso
    (iso'''
      (mph proj₁ λ { (x , y) (z , w) → refl})
      (λ g → g , tt)
      (λ _ → refl)
      λ _ → ×≡ refl refl)
