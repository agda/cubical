{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Group.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism as I
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Pointed
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)

open import Cubical.Structures.Group.Base
open import Cubical.Structures.Group.Properties
open import Cubical.Structures.Group.Morphism
open import Cubical.Structures.Group.MorphismProperties

open import Cubical.HITs.PropositionalTruncation hiding (map)

-- open import Cubical.Data.Group.Base

open Iso
open Group
open GroupHom

private
  variable
    ℓ ℓ' ℓ'' : Level



-0≡0 : ∀ {ℓ} {G : Group {ℓ}} → (- G) (0g G) ≡ (0g G) --  - 0 ≡ 0
-0≡0 {G = G} =  sym (IsGroup.lid (isGroup G) _) ∙ fst (IsGroup.inverse (isGroup G) _)

morph0→0 : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupHom G H)
           → fun f (0g G) ≡ 0g H
morph0→0 G H f =
  (fun f) (0g G)                                        ≡⟨ sym (IsGroup.rid (isGroup H) _) ⟩
  (f' (0g G) H.+ 0g H)                                  ≡⟨ (λ i → f' (0g G) H.+ invr H (f' (0g G)) (~ i)) ⟩
  (f' (0g G) H.+ (f' (0g G) H.+ (H.- f' (0g G))))       ≡⟨ (Group.assoc H (f' (0g G)) (f' (0g G)) (H.- (f' (0g G)))) ⟩
  ((f' (0g G) H.+ f' (0g G)) H.+ (H.- f' (0g G)))       ≡⟨ sym (cong (λ x → x H.+ (H.- f' (0g G))) (sym (cong f' (IsGroup.lid (isGroup G) _)) ∙ isHom f (0g G) (0g G))) ⟩
  (f' (0g G)) H.+ (H.- (f' (0g G)))                     ≡⟨ invr H (f' (0g G)) ⟩
  0g H ∎
  where
  module G = Group G
  module H = Group H
  f' = fun f

morphMinus : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) → (ϕ : GroupHom G H)
            → (g : ⟨ G ⟩) → fun ϕ ((- G) g) ≡ (- H) (fun ϕ g)
morphMinus G H ϕ g =
  f (G.- g)                             ≡⟨ sym (IsGroup.rid (isGroup H) (f (G.- g))) ⟩
  (f (G.- g) H.+ 0g H)                  ≡⟨ cong (f (G.- g) H.+_) (sym (invr H (f g))) ⟩
  (f (G.- g) H.+ (f g H.+ (H.- f g)))   ≡⟨ Group.assoc H (f (G.- g)) (f g) (H.- f g) ⟩
  ((f (G.- g) H.+ f g) H.+ (H.- f g))   ≡⟨ cong (H._+ (H.- f g)) helper ⟩
  (0g H H.+ (H.- f g))                  ≡⟨ IsGroup.lid (isGroup H) (H.- (f g))⟩
  H.- (f g) ∎
  where
  module G = Group G
  module H = Group H
  f = fun ϕ
  helper : (f (G.- g) H.+ f g) ≡ 0g H
  helper = sym (isHom ϕ (G.- g) g) ∙∙ cong f (invl G g) ∙∙ morph0→0 G H ϕ

-- ----------- Equivalent notions of isomorphisms --------------

record GroupIso {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iso
  field
    map : GroupHom G H
    inv : ⟨ H ⟩ → ⟨ G ⟩
    rightInv : section (GroupHom.fun map) inv
    leftInv : retract (GroupHom.fun map) inv

infixr 35 _◆_

open GroupIso

compGroupIso : ∀ {ℓ''} {G : Group {ℓ}} {H : Group {ℓ'}} {A : Group {ℓ''}} → GroupIso G H → GroupIso H A → GroupIso G A
map (compGroupIso iso1 iso2) = compGroupHom (map iso1) (map iso2)
inv (compGroupIso iso1 iso2) = inv iso1 ∘ inv iso2
rightInv (compGroupIso iso1 iso2) a = cong (fun (map iso2)) (rightInv iso1 _) ∙ rightInv iso2 a
leftInv (compGroupIso iso1 iso2) a = cong (inv iso1) (leftInv iso2 _) ∙ leftInv iso1 a

isGroupHomInv' : {G : Group {ℓ}} {H : Group {ℓ'}} (f : GroupIso G H) → isGroupHom H G (inv f)
isGroupHomInv' {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ (rightInv f) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (rightInv f h) (rightInv f h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (map f) _ _) ⟩ -- sym (isHom (hom f) _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fun (map f)
  _⋆¹_ = Group._+_ G
  _⋆²_ = Group._+_ H
  g = inv f -- invEq (eq f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y p = sym (leftInv f _) ∙∙ cong g p ∙∙ leftInv f _

invGroupIso : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupIso G H → GroupIso H G
fun (map (invGroupIso iso1)) = inv iso1
isHom (map (invGroupIso iso1)) = isGroupHomInv' iso1
inv (invGroupIso iso1) = fun (map iso1)
rightInv (invGroupIso iso1) = leftInv iso1
leftInv (invGroupIso iso1) = rightInv iso1

_◆_ : _
_◆_ = compGroupIso

dirProdGroupIso : ∀ {ℓ'' ℓ'''} {G : Group {ℓ}} {H : Group {ℓ'}} {A : Group {ℓ''}} {B : Group {ℓ'''}}
               → GroupIso G H → GroupIso A B → GroupIso (dirProd G A) (dirProd H B)
map (dirProdGroupIso iso1 iso2) = grouphom (λ prod → fun (map iso1) (fst prod) , fun (map iso2) (snd prod))
                                           λ a b → ΣPathP (isHom (map iso1) (fst a) (fst b) , isHom (map iso2) (snd a) (snd b))
inv (dirProdGroupIso iso1 iso2) prod = (inv iso1) (fst prod) , (inv iso2) (snd prod)
rightInv (dirProdGroupIso iso1 iso2) a = ΣPathP (rightInv iso1 (fst a) , (rightInv iso2 (snd a)))
leftInv (dirProdGroupIso iso1 iso2) a = ΣPathP (leftInv iso1 (fst a) , (leftInv iso2 (snd a)))

GrIsoToGrEquiv : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupIso G H → GroupEquiv G H
GroupEquiv.eq (GrIsoToGrEquiv i) = isoToEquiv (iso (fun (map i)) (inv i) (rightInv i) (leftInv i))
GroupEquiv.isHom (GrIsoToGrEquiv i) = isHom (map i)

record Iso' {ℓ ℓ'} (A : Group {ℓ}) (B : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor iso'
  field
    map' : GroupHom A B
    inj : isInjective A B map'
    surj : isSurjective A B map'

open Iso'

-- "Very" short exact sequences
record vSES {ℓ ℓ' ℓ'' ℓ'''} (A : Group {ℓ}) (B : Group {ℓ'}) (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
           : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))) where
  constructor ses
  field
    isTrivialLeft : isProp ⟨ leftGr ⟩
    isTrivialRight : isProp ⟨ rightGr ⟩

    left : GroupHom leftGr A
    right : GroupHom B rightGr
    ϕ : GroupHom A B

    Ker-ϕ⊂Im-left : (x : ⟨ A ⟩)
                  → isInKer A B ϕ x
                  → isInIm leftGr A left x
    Ker-right⊂Im-ϕ : (x : ⟨ B ⟩)
                   → isInKer B rightGr right x
                   → isInIm A B ϕ x

--- Proofs that different notions of ismomorphisms agree ---

Iso'ToGroupIso : {A : Group {ℓ}} {B : Group {ℓ'}} → Iso' A B → GroupIso A B
Iso'ToGroupIso {A = A} {B = B} i = grIso
  where
  module A = Group A
  module B = Group B
  f = fun (map' i)

  helper : (b : _) → isProp (Σ[ a ∈ ⟨ A ⟩ ] f a ≡ b)
  helper _ a b =
    Σ≡Prop (λ _ → isSetCarrier B _ _)
           (fst a ≡⟨ sym (IsGroup.rid (isGroup A) (fst a)) ⟩
           ((fst a) A.+ 0g A) ≡⟨ cong ((fst a) A.+_) (sym (invl A (fst b))) ⟩
           ((fst a) A.+ ((A.- fst b) A.+ fst b)) ≡⟨ Group.assoc A _ _ _ ⟩
           (((fst a) A.+ (A.- fst b)) A.+ fst b) ≡⟨ cong (A._+ fst b) idHelper ⟩
           (0g A A.+ fst b) ≡⟨ IsGroup.lid (isGroup A) (fst b) ⟩
           fst b ∎)
    where
    idHelper : fst a A.+ (A.- fst b) ≡ 0g A
    idHelper =
      inj i _
           (isHom (map' i) (fst a) (A.- (fst b))
         ∙ (cong (f (fst a) B.+_) (morphMinus A B (map' i) (fst b))
         ∙∙ cong (B._+ (B.- f (fst b))) (snd a ∙ sym (snd b))
         ∙∙ invr B (f (fst b))))

  grIso : GroupIso A B
  map grIso = map' i
  inv grIso b = (rec (helper b) (λ a → a) (surj i b)) .fst
  rightInv grIso b = (rec (helper b) (λ a → a) (surj i b)) .snd
  leftInv grIso b j = rec (helper (f b)) (λ a → a) (propTruncIsProp (surj i (f b)) ∣ b , refl ∣ j) .fst

Iso'ToGroupEquiv : {A : Group {ℓ}} {B : Group {ℓ'}} → Iso' A B → GroupEquiv A B
Iso'ToGroupEquiv i = GrIsoToGrEquiv (Iso'ToGroupIso i) 

vSES→GroupIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
                → vSES A B leftGr rightGr
                → GroupIso A B
vSES→GroupIso {A = A} lGr rGr vses = Iso'ToGroupIso theIso
  where
  theIso : Iso' _ _
  map' theIso = vSES.ϕ vses
  inj theIso a inker = rec (isSetCarrier A _ _)
                            (λ (a , p) → sym p
                                        ∙∙ cong (fun (vSES.left vses)) (vSES.isTrivialLeft vses a _)
                                        ∙∙ morph0→0 lGr A (vSES.left vses))
                            (vSES.Ker-ϕ⊂Im-left vses a inker)
  surj theIso a = vSES.Ker-right⊂Im-ϕ vses a (vSES.isTrivialRight vses _ _)

vSES→GroupEquiv : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
        → vSES A B leftGr rightGr
        → GroupEquiv A B
vSES→GroupEquiv {A = A} lGr rGr vses = GrIsoToGrEquiv (vSES→GroupIso lGr rGr vses)

dirProdEquiv : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
           → GroupEquiv A C → GroupEquiv B D
           → GroupEquiv (dirProd A B) (dirProd C D)
GroupEquiv.eq (dirProdEquiv eq1 eq2) = ≃-× (GroupEquiv.eq eq1) (GroupEquiv.eq eq2)
GroupEquiv.isHom (dirProdEquiv eq1 eq2) = isHom (×hom (GroupEquiv.hom eq1) (GroupEquiv.hom eq2))


---
open import Cubical.Data.Unit
lUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd trivialGroup G) G
lUnitGroupIso =
  GrIsoToGrEquiv
    (iso (grouphom snd (λ a b → refl))
         (λ g → tt , g)
         (λ _ → refl)
         λ _ → refl)

rUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd G trivialGroup) G
rUnitGroupIso =
  GrIsoToGrEquiv
    (iso
      (grouphom fst λ _ _ → refl)
      (λ g → g , tt)
      (λ _ → refl)
      λ _ → refl)
