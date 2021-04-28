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
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Reflection.StrictEquiv
open import Cubical.HITs.PropositionalTruncation hiding (map)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂ ℓ₃ : Level

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
  _⋆¹_ = _·_ (snd G)
  _⋆²_ = _·_ (snd H)
  g = invEq (eq f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (eq f)) x y)

invGroupEquiv : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupEquiv G H → GroupEquiv H G
eq (invGroupEquiv f) = invEquiv (eq f)
isHom (invGroupEquiv f) = isGroupHomInv f

×hom : {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
    → GroupHom A C → GroupHom B D → GroupHom (dirProd A B) (dirProd C D)
fun (×hom mf1 mf2) = map-× (fun mf1) (fun mf2)
isHom (×hom mf1 mf2) a b = ≡-× (isHom mf1 _ _) (isHom mf2 _ _)

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

  -id≡id : G.inv G.id ≡ G.id
  -id≡id = sym (G.lid _) ∙ G.invr _

  -- ϕ(id) ≡ id
  morphid→id : (f : GroupHom G H) → f .fun G.id ≡ H.id
  morphid→id fh@(grouphom f _) =
    f G.id                         ≡⟨ sym (H.rid _) ⟩
    f G.id H.· H.id                ≡⟨ (λ i → f G.id H.· H.invr (f G.id) (~ i)) ⟩
    f G.id H.· (f G.id H.· H.inv (f G.id)) ≡⟨ H.assoc _ _ _ ⟩
    (f G.id H.· f G.id) H.· H.inv (f G.id) ≡⟨ sym (cong (λ x → x H.· _)
                                                (sym (cong f (G.lid _)) ∙ isHom fh G.id G.id)) ⟩
    f G.id H.· H.inv (f G.id)              ≡⟨ H.invr _ ⟩
    H.id ∎

  -- ϕ(- x) = - ϕ(x)
  morphMinus : (f : GroupHom G H) → (g : ⟨ G ⟩) → f .fun (G.inv g) ≡ H.inv (f .fun g)
  morphMinus fc@(grouphom f fh) g =
    f (G.inv g)                   ≡⟨ sym (H.rid _) ⟩
    f (G.inv g) H.· H.id          ≡⟨ cong (f (G.inv g) H.·_) (sym (H.invr _)) ⟩
    f (G.inv g) H.· (f g H.· H.inv (f g)) ≡⟨ H.assoc _ _ _ ⟩
    (f (G.inv g) H.· f g) H.· H.inv (f g) ≡⟨ cong (H._· _) helper ⟩
    H.id H.· H.inv (f g)                ≡⟨ H.lid _ ⟩
    H.inv (f g) ∎
    where
    helper : f (G.inv g) H.· f g ≡ H.id
    helper = sym (fh (G.inv g) g) ∙∙ cong f (G.invl g) ∙∙ morphid→id fc



open BijectionIso
open GroupIso
open vSES

compGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} {A : Group {ℓ₂}} → GroupIso G H → GroupIso H A → GroupIso G A
isom (compGroupIso iso1 iso2) = compIso (isom iso1) (isom iso2)
isHom (compGroupIso {G = G} {H = H} {A = A} iso1 iso2) =
  isGroupHomComp {F = G} {G = H} {H = A} (grouphom (fun (isom iso1)) (isHom iso1)) (grouphom (fun (isom iso2)) (isHom iso2))

isGroupHomInv' : {G : Group {ℓ}} {H : Group {ℓ₁}} (f : GroupIso G H) → isGroupHom H G (inv (isom f))
isGroupHomInv' {G = G} {H = H}  f h h' = isInj-f _ _ (
  f' (g (h ⋆² h')) ≡⟨ (rightInv (isom f)) _ ⟩
  (h ⋆² h') ≡⟨ sym (cong₂ _⋆²_ (rightInv (isom f) h) (rightInv (isom f) h')) ⟩
  (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom f _ _) ⟩
  f' (g h ⋆¹ g h') ∎)
  where
  f' = fun (isom f)
  _⋆¹_ = GroupStr._·_ (snd G)
  _⋆²_ = GroupStr._·_ (snd H)
  g = inv (isom f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y p = sym (leftInv (isom f) _) ∙∙ cong g p ∙∙ leftInv (isom f) _

invGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} → GroupIso G H → GroupIso H G
isom (invGroupIso iso1) = invIso (isom iso1)
isHom (invGroupIso iso1) = isGroupHomInv' iso1

dirProdGroupIso : {G : Group {ℓ}} {H : Group {ℓ₁}} {A : Group {ℓ₂}} {B : Group {ℓ₃}}
               → GroupIso G H → GroupIso A B → GroupIso (dirProd G A) (dirProd H B)
fun (isom (dirProdGroupIso iso1 iso2)) prod = fun (isom iso1) (fst prod) , fun (isom iso2) (snd prod)
inv (isom (dirProdGroupIso iso1 iso2)) prod = inv (isom iso1) (fst prod) , inv (isom iso2) (snd prod)
rightInv (isom (dirProdGroupIso iso1 iso2)) a = ΣPathP (rightInv (isom iso1) (fst a) , (rightInv (isom iso2) (snd a)))
leftInv (isom (dirProdGroupIso iso1 iso2)) a = ΣPathP (leftInv (isom iso1) (fst a) , (leftInv (isom iso2) (snd a)))
isHom (dirProdGroupIso iso1 iso2) a b = ΣPathP (isHom iso1 (fst a) (fst b) , isHom iso2 (snd a) (snd b))

GrIsoToGrEquiv : {G : Group {ℓ}} {H : Group {ℓ₂}} → GroupIso G H → GroupEquiv G H
GroupEquiv.eq (GrIsoToGrEquiv i) = isoToEquiv (isom i)
GroupEquiv.isHom (GrIsoToGrEquiv i) = isHom i

--- Proofs that BijectionIso and vSES both induce isomorphisms ---
BijectionIsoToGroupIso : {A : Group {ℓ}} {B : Group {ℓ'}} → BijectionIso A B → GroupIso A B
BijectionIsoToGroupIso {A = A} {B = B} i = grIso
  where
  module A = GroupStr (snd A)
  module B = GroupStr (snd B)
  f = fun (fun i)

  helper : (b : _) → isProp (Σ[ a ∈ ⟨ A ⟩ ] f a ≡ b)
  helper _ a b =
    Σ≡Prop (λ _ → isSetCarrier B _ _)
           (fst a                             ≡⟨ sym (A.rid _) ⟩
            fst a A.· A.id                    ≡⟨ cong (fst a A.·_) (sym (A.invl _)) ⟩
            fst a A.· ((A.inv (fst b)) A.· fst b) ≡⟨ A.assoc _ _ _ ⟩
            (fst a A.· A.inv (fst b)) A.· fst b   ≡⟨ cong (A._· fst b) idHelper ⟩
            A.id A.· fst b                    ≡⟨ A.lid _ ⟩
            fst b ∎)
    where
    idHelper : fst a A.· A.inv (fst b) ≡ A.id
    idHelper =
      inj i _
           (isHom (fun i) (fst a) (A.inv (fst b))
         ∙ (cong (f (fst a) B.·_) (morphMinus A B (fun i) (fst b))
         ∙∙ cong (B._· (B.inv (f (fst b)))) (snd a ∙ sym (snd b))
         ∙∙ B.invr (f (fst b))))

  grIso : GroupIso A B
  fun (isom grIso) = fun (fun i)
  inv (isom grIso) b = rec (helper b) (λ a → a) (surj i b) .fst
  rightInv (isom grIso) b = rec (helper b) (λ a → a) (surj i b) .snd
  leftInv (isom grIso) b j = rec (helper (f b)) (λ a → a) (propTruncIsProp (surj i (f b)) ∣ b , refl ∣ j) .fst
  isHom grIso = isHom (fun i)

BijectionIsoToGroupEquiv : {A : Group {ℓ}} {B : Group {ℓ₂}} → BijectionIso A B → GroupEquiv A B
BijectionIsoToGroupEquiv i = GrIsoToGrEquiv (BijectionIsoToGroupIso i)

vSES→GroupIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
                → vSES A B leftGr rightGr
                → GroupIso A B
vSES→GroupIso {A = A} lGr rGr isvses = BijectionIsoToGroupIso theIso
  where
  theIso : BijectionIso _ _
  fun theIso = vSES.ϕ isvses
  inj theIso a inker = rec (isSetCarrier A _ _)
                            (λ (a , p) → sym p
                                        ∙∙ cong (fun (left isvses)) (isTrivialLeft isvses a _)
                                        ∙∙ morphid→id lGr A (left isvses))
                            (Ker-ϕ⊂Im-left isvses a inker)
  surj theIso a = Ker-right⊂Im-ϕ isvses a (isTrivialRight isvses _ _)

vSES→GroupEquiv : {A : Group {ℓ}} {B : Group {ℓ₁}} (leftGr : Group {ℓ₂}) (rightGr : Group {ℓ₃})
        → vSES A B leftGr rightGr
        → GroupEquiv A B
vSES→GroupEquiv lGr rGr isvses = GrIsoToGrEquiv (vSES→GroupIso lGr rGr isvses)
