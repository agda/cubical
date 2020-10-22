{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.PropositionalTruncation hiding (map)

open Iso
open GroupHom

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ : Level

------- elementary properties of morphisms --------

module _ (G : Group {ℓ}) (H : Group {ℓ'}) where

  module G = GroupStr (snd G)
  module H = GroupStr (snd H)

  -0≡0 : G.- G.0g ≡ G.0g
  -0≡0 = sym (G.lid _) ∙ G.invr _

  -- ϕ(0) ≡ 0
  morph0→0 : (f : GroupHom G H) → f .fun G.0g ≡ H.0g
  morph0→0 fh@(grouphom f _) =
    f G.0g                         ≡⟨ sym (H.rid _) ⟩
    f G.0g H.+ H.0g                ≡⟨ (λ i → f G.0g H.+ H.invr (f G.0g) (~ i)) ⟩
    f G.0g H.+ (f G.0g H.- f G.0g) ≡⟨ H.assoc _ _ _ ⟩
    (f G.0g H.+ f G.0g) H.- f G.0g ≡⟨ sym (cong (λ x → x H.+ (H.- f G.0g))
                                                (sym (cong f (G.lid _)) ∙ isHom fh G.0g G.0g)) ⟩
    f G.0g H.- f G.0g              ≡⟨ H.invr _ ⟩
    H.0g ∎

  -- ϕ(- x) = - ϕ(x)
  morphMinus : (f : GroupHom G H) → (g : ⟨ G ⟩) → f .fun (G.- g) ≡ H.- (f .fun g)
  morphMinus fc@(grouphom f fh) g =
    f (G.- g)                   ≡⟨ sym (H.rid _) ⟩
    f (G.- g) H.+ H.0g          ≡⟨ cong (f (G.- g) H.+_) (sym (H.invr _)) ⟩
    f (G.- g) H.+ (f g H.- f g) ≡⟨ H.assoc _ _ _ ⟩
    (f (G.- g) H.+ f g) H.- f g ≡⟨ cong (H._+ (H.- f g)) helper ⟩
    H.0g H.- f g                ≡⟨ H.lid _ ⟩
    H.- f g ∎
    where
    helper : f (G.- g) H.+ f g ≡ H.0g
    helper = sym (fh (G.- g) g) ∙∙ cong f (G.invl g) ∙∙ morph0→0 fc


-- ----------- Alternative notions of isomorphisms --------------
record GroupIso {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where

  constructor iso
  field
    map : GroupHom G H
    inv : ⟨ H ⟩ → ⟨ G ⟩
    rightInv : section (GroupHom.fun map) inv
    leftInv : retract (GroupHom.fun map) inv

record BijectionIso {ℓ ℓ'} (A : Group {ℓ}) (B : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where

  constructor bij-iso
  field
    map' : GroupHom A B
    inj : isInjective A B map'
    surj : isSurjective A B map'

-- "Very" short exact sequences
-- i.e. an exact sequence A → B → C → D where A and D are trivial
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

open BijectionIso
open GroupIso
open vSES

Iso+Hom→GrIso : {G : Group {ℓ}} {H : Group {ℓ₁}} → (e : Iso ⟨ G ⟩ ⟨ H ⟩) → isGroupHom G H (Iso.fun e) → GroupIso G H
fun (map (Iso+Hom→GrIso e hom)) = Iso.fun e
isHom (map (Iso+Hom→GrIso e hom)) = hom
inv (Iso+Hom→GrIso e hom) = Iso.inv e
rightInv (Iso+Hom→GrIso e hom) = Iso.rightInv e
leftInv (Iso+Hom→GrIso e hom) = Iso.leftInv e

compGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} {A : Group {ℓ₂}} → GroupIso G H → GroupIso H A → GroupIso G A
map (compGroupIso iso1 iso2) = compGroupHom (map iso1) (map iso2)
inv (compGroupIso iso1 iso2) = inv iso1 ∘ inv iso2
rightInv (compGroupIso iso1 iso2) a = cong (fun (map iso2)) (rightInv iso1 _) ∙ rightInv iso2 a
leftInv (compGroupIso iso1 iso2) a = cong (inv iso1) (leftInv iso2 _) ∙ leftInv iso1 a

isGroupHomInv' : {G : Group {ℓ}} {H : Group {ℓ₁}} (f : GroupIso G H) → isGroupHom H G (inv f)
isGroupHomInv' {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ (rightInv f) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (rightInv f h) (rightInv f h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (map f) _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fun (map f)
  _⋆¹_ = GroupStr._+_ (snd G)
  _⋆²_ = GroupStr._+_ (snd H)
  g = inv f

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y p = sym (leftInv f _) ∙∙ cong g p ∙∙ leftInv f _

invGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} → GroupIso G H → GroupIso H G
fun (map (invGroupIso iso1)) = inv iso1
isHom (map (invGroupIso iso1)) = isGroupHomInv' iso1
inv (invGroupIso iso1) = fun (map iso1)
rightInv (invGroupIso iso1) = leftInv iso1
leftInv (invGroupIso iso1) = rightInv iso1

dirProdGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} {A : Group {ℓ₂}} {B : Group {ℓ₃}}
               → GroupIso G H → GroupIso A B → GroupIso (dirProd G A) (dirProd H B)
fun (map (dirProdGroupIso iso1 iso2)) prod = fun (map iso1) (fst prod) , fun (map iso2) (snd prod)
isHom (map (dirProdGroupIso iso1 iso2)) a b = ΣPathP (isHom (map iso1) (fst a) (fst b) , isHom (map iso2) (snd a) (snd b))
inv (dirProdGroupIso iso1 iso2) prod = (inv iso1) (fst prod) , (inv iso2) (snd prod)
rightInv (dirProdGroupIso iso1 iso2) a = ΣPathP (rightInv iso1 (fst a) , (rightInv iso2 (snd a)))
leftInv (dirProdGroupIso iso1 iso2) a = ΣPathP (leftInv iso1 (fst a) , (leftInv iso2 (snd a)))

GrIsoToGrEquiv : {G : Group {ℓ}} {H : Group {ℓ₂}} → GroupIso G H → GroupEquiv G H
GroupEquiv.eq (GrIsoToGrEquiv i) = isoToEquiv (iso (fun (map i)) (inv i) (rightInv i) (leftInv i))
GroupEquiv.isHom (GrIsoToGrEquiv i) = isHom (map i)

--- Proofs that BijectionIso and vSES both induce isomorphisms ---
BijectionIsoToGroupIso : {A : Group {ℓ}} {B : Group {ℓ'}} → BijectionIso A B → GroupIso A B
BijectionIsoToGroupIso {A = A} {B = B} i = grIso
  where
  module A = GroupStr (snd A)
  module B = GroupStr (snd B)
  f = fun (map' i)

  helper : (b : _) → isProp (Σ[ a ∈ ⟨ A ⟩ ] f a ≡ b)
  helper _ a b =
    Σ≡Prop (λ _ → isSetCarrier B _ _)
           (fst a                             ≡⟨ sym (A.rid _) ⟩
            fst a A.+ A.0g                    ≡⟨ cong (fst a A.+_) (sym (A.invl _)) ⟩
            fst a A.+ ((A.- fst b) A.+ fst b) ≡⟨ A.assoc _ _ _ ⟩
            (fst a A.- fst b) A.+ fst b       ≡⟨ cong (A._+ fst b) idHelper ⟩
            A.0g A.+ fst b                    ≡⟨ A.lid _ ⟩
            fst b ∎)
    where
    idHelper : fst a A.- fst b ≡ A.0g
    idHelper =
      inj i _
           (isHom (map' i) (fst a) (A.- (fst b))
         ∙ (cong (f (fst a) B.+_) (morphMinus A B (map' i) (fst b))
         ∙∙ cong (B._+ (B.- f (fst b))) (snd a ∙ sym (snd b))
         ∙∙ B.invr (f (fst b))))

  grIso : GroupIso A B
  map grIso = map' i
  inv grIso b = (rec (helper b) (λ a → a) (surj i b)) .fst
  rightInv grIso b = (rec (helper b) (λ a → a) (surj i b)) .snd
  leftInv grIso b j = rec (helper (f b)) (λ a → a) (propTruncIsProp (surj i (f b)) ∣ b , refl ∣ j) .fst

BijectionIsoToGroupEquiv : {A : Group {ℓ}} {B : Group {ℓ₂}} → BijectionIso A B → GroupEquiv A B
BijectionIsoToGroupEquiv i = GrIsoToGrEquiv (BijectionIsoToGroupIso i)

vSES→GroupIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
                → vSES A B leftGr rightGr
                → GroupIso A B
vSES→GroupIso {A = A} lGr rGr vses = BijectionIsoToGroupIso theIso
  where
  theIso : BijectionIso _ _
  map' theIso = vSES.ϕ vses
  inj theIso a inker = rec (isSetCarrier A _ _)
                            (λ (a , p) → sym p
                                        ∙∙ cong (fun (left vses)) (isTrivialLeft vses a _)
                                        ∙∙ morph0→0 lGr A (left vses))
                            (Ker-ϕ⊂Im-left vses a inker)
  surj theIso a = Ker-right⊂Im-ϕ vses a (isTrivialRight vses _ _)

vSES→GroupEquiv : {A : Group {ℓ}} {B : Group {ℓ₁}} (leftGr : Group {ℓ₂}) (rightGr : Group {ℓ₃})
        → vSES A B leftGr rightGr
        → GroupEquiv A B
vSES→GroupEquiv {A = A} lGr rGr vses = GrIsoToGrEquiv (vSES→GroupIso lGr rGr vses)

-- The trivial group is a unit.
lUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupIso (dirProd trivialGroup G) G
fun (map lUnitGroupIso) = snd
isHom (map lUnitGroupIso) _ _ = refl
inv lUnitGroupIso g = tt , g
rightInv lUnitGroupIso _ = refl
leftInv lUnitGroupIso _ = refl

rUnitGroupIso : ∀ {ℓ} {G : Group {ℓ}} → GroupIso (dirProd G trivialGroup) G
fun (map rUnitGroupIso) = fst
isHom (map rUnitGroupIso) _ _ = refl
inv rUnitGroupIso g = g , tt
rightInv rUnitGroupIso _ = refl
leftInv rUnitGroupIso _ = refl

lUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd trivialGroup G) G
lUnitGroupEquiv = GrIsoToGrEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd G trivialGroup) G
rUnitGroupEquiv = GrIsoToGrEquiv rUnitGroupIso

IsoContrGroupTrivialGroup : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupIso G trivialGroup
fun (map (IsoContrGroupTrivialGroup contr)) _ = tt
isHom (map (IsoContrGroupTrivialGroup contr)) _ _ = refl
inv (IsoContrGroupTrivialGroup contr) x = fst contr
rightInv (IsoContrGroupTrivialGroup contr) x = refl
leftInv (IsoContrGroupTrivialGroup contr) x = snd contr x

contrGroup≅trivialGroup : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupEquiv G trivialGroup
contrGroup≅trivialGroup contr = GrIsoToGrEquiv (IsoContrGroupTrivialGroup contr)

GroupIso→Iso : {A : Group {ℓ}} {B : Group {ℓ₁}} → GroupIso A B → Iso ⟨ A ⟩ ⟨ B ⟩
fun (GroupIso→Iso i) = fun (map i)
inv (GroupIso→Iso i) = inv i
rightInv (GroupIso→Iso i) = rightInv i
leftInv (GroupIso→Iso i) = leftInv i

congIdLeft≡congIdRight : {A : Type ℓ} (_+A_ : A → A → A) (-A_ : A → A)
            (0A : A)
            (rUnitA : (x : A) → x +A 0A ≡ x)
            (lUnitA : (x : A) → 0A +A x ≡ x)
          → (r≡l : rUnitA 0A ≡ lUnitA 0A)
          → (p : 0A ≡ 0A) →
            cong (0A +A_) p ≡ cong (_+A 0A) p
congIdLeft≡congIdRight _+A_ -A_ 0A rUnitA lUnitA r≡l p =
            rUnit (cong (0A +A_) p)
         ∙∙ ((λ i → (λ j → lUnitA 0A (i ∧ j)) ∙∙ cong (λ x → lUnitA x i) p ∙∙ λ j → lUnitA 0A (i ∧ ~ j))
         ∙∙ cong₂ (λ x y → x ∙∙ p ∙∙ y) (sym r≡l) (cong sym (sym r≡l))
         ∙∙ λ i → (λ j → rUnitA 0A (~ i ∧ j)) ∙∙ cong (λ x → rUnitA x (~ i)) p ∙∙ λ j → rUnitA 0A (~ i ∧ ~ j))
         ∙∙ sym (rUnit (cong (_+A 0A) p))
