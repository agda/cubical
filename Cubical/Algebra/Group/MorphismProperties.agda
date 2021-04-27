{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Pointed
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphism

open import Cubical.Reflection.StrictEquiv
open import Cubical.HITs.PropositionalTruncation hiding (map)

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₂ ℓ₃ : Level

open Iso
open GroupStr
open GroupHom
open GroupEquiv

isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩} → isProp (isGroupHom G H f)
isPropIsGroupHom G H {f} = isPropΠ2 λ a b → GroupStr.is-set (snd H) _ _

isSetGroupHom : {G : Group {ℓ}} {H : Group {ℓ'}} → isSet (GroupHom G H)
isSetGroupHom {G = G} {H = H} = isOfHLevelRespectEquiv 2 equiv (isSetΣ (isSetΠ λ _ → is-set (snd H)) λ _ → isProp→isSet (isPropIsGroupHom G H)) where
  equiv : (Σ[ g ∈ (⟨ G ⟩ → ⟨ H ⟩) ] (isGroupHom G H g)) ≃ (GroupHom G H)
  equiv =  isoToEquiv (iso (λ (g , m) → grouphom g m) (λ hom → fun hom , isHom hom) (λ _ → refl) λ _ → refl)

-- Morphism composition
isGroupHomComp : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} →
  (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (fun g ∘ fun f)
isGroupHomComp f g x y = cong (fun g) (isHom f _ _) ∙ isHom g _ _

compGroupHom : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupHom F G → GroupHom G H → GroupHom F H
fun (compGroupHom f g) = fun g ∘ fun f
isHom (compGroupHom f g) = isGroupHomComp f g

compGroupEquiv : {F : Group {ℓ}} {G : Group {ℓ'}} {H : Group {ℓ''}} → GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
eq (compGroupEquiv f g) = compEquiv (eq f) (eq g)
isHom (compGroupEquiv f g) = isHom (compGroupHom (hom f) (hom g))

idGroupEquiv : (G : Group {ℓ}) → GroupEquiv G G
eq (idGroupEquiv G) = idEquiv ⟨ G ⟩
isHom (idGroupEquiv G) = λ _ _ → refl

-- Isomorphism inversion
isGroupHomInv : {G : Group {ℓ}} {H : Group {ℓ'}} (f : GroupEquiv G H) → isGroupHom H G (invEq (GroupEquiv.eq f))
isGroupHomInv {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ retEq (eq f) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (retEq (eq f) h) (retEq (eq f) h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (hom f) _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fst (eq f)
  _⋆¹_ = _+_ (snd G)
  _⋆²_ = _+_ (snd H)
  g = invEq (eq f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (eq f)) x y)

invGroupEquiv : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupEquiv G H → GroupEquiv H G
eq (invGroupEquiv f) = invEquiv (eq f)
isHom (invGroupEquiv f) = isGroupHomInv f

dirProdEquiv : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
           → GroupEquiv A C → GroupEquiv B D
           → GroupEquiv (dirProd A B) (dirProd C D)
eq (dirProdEquiv eq1 eq2) = ≃-× (eq eq1) (eq eq2)
isHom (dirProdEquiv eq1 eq2) = isHom (×hom (GroupEquiv.hom eq1) (GroupEquiv.hom eq2))

groupHomEq : {G : Group {ℓ}} {H : Group {ℓ'}} {f g : GroupHom G H} → (fun f ≡ fun g) → f ≡ g
fun (groupHomEq p i) = p i
isHom (groupHomEq {G = G} {H = H} {f = f} {g = g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)

groupEquivEq : {G : Group {ℓ}} {H : Group {ℓ'}} {f g : GroupEquiv G H} → (eq f ≡ eq g) → f ≡ g
eq (groupEquivEq {G = G} {H = H} {f} {g} p i) = p i
isHom (groupEquivEq {G = G} {H = H} {f} {g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i .fst)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)



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


GroupIso→Iso : {A : Group {ℓ}} {B : Group {ℓ₁}} → GroupIso A B → Iso ⟨ A ⟩ ⟨ B ⟩
fun (GroupIso→Iso i) = fun (map i)
inv (GroupIso→Iso i) = inv i
rightInv (GroupIso→Iso i) = rightInv i
leftInv (GroupIso→Iso i) = leftInv i
