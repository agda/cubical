{-
This file contains:

- Elementary properties of homomorphisms
- H-level results for the properties of morphisms
- Special homomorphisms and operations (id, composition, inversion)
- Conversion functions between different notions of group morphisms

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.MorphismProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms

open import Cubical.HITs.PropositionalTruncation hiding (map)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    F G H : Group {ℓ}

open Iso
open GroupStr
open GroupHom
open GroupEquiv
open GroupIso
open BijectionIso


-- Elementary properties of homomorphisms
module _ {G : Group {ℓ}} {H : Group {ℓ'}} where

  private
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)

  -- ϕ(1g) ≡ 1g
  hom1g : (f : GroupHom G H) → f .fun G.1g ≡ H.1g
  hom1g fh@(grouphom f _) =
    f G.1g                                  ≡⟨ sym (H.rid _) ⟩
    f G.1g H.· H.1g                         ≡⟨ (λ i → f G.1g H.· H.invr (f G.1g) (~ i)) ⟩
    f G.1g H.· (f G.1g H.· H.inv (f G.1g))  ≡⟨ H.assoc _ _ _ ⟩
    (f G.1g H.· f G.1g) H.· H.inv (f G.1g)  ≡⟨ sym (cong (λ x → x H.· _)
                                                (sym (cong f (G.lid _)) ∙ isHom fh G.1g G.1g)) ⟩
    f G.1g H.· H.inv (f G.1g)               ≡⟨ H.invr _ ⟩
    H.1g ∎

  -- ϕ(- x) = - ϕ(x)
  homInv : (f : GroupHom G H) → (g : ⟨ G ⟩) → f .fun (G.inv g) ≡ H.inv (f .fun g)
  homInv fc@(grouphom f fh) g =
    f (G.inv g)                            ≡⟨ sym (H.rid _) ⟩
    f (G.inv g) H.· H.1g                   ≡⟨ cong (_ H.·_) (sym (H.invr _)) ⟩
    f (G.inv g) H.· (f g H.· H.inv (f g))  ≡⟨ H.assoc _ _ _ ⟩
    (f (G.inv g) H.· f g) H.· H.inv (f g)  ≡⟨ cong (H._· _) (sym (fh _ g) ∙∙ cong f (G.invl g) ∙∙ hom1g fc) ⟩
    H.1g H.· H.inv (f g)                   ≡⟨ H.lid _ ⟩
    H.inv (f g) ∎


-- H-level results
isPropIsGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) {f : ⟨ G ⟩ → ⟨ H ⟩}
                 → isProp (isGroupHom G H f)
isPropIsGroupHom G H = isPropΠ2 λ a b → GroupStr.is-set (snd H) _ _

isSetGroupHom : isSet (GroupHom G H)
isSetGroupHom {G = G} {H = H} =
  isSetRetract
    (λ hom → fun hom , isHom hom) (λ (g , m) → grouphom g m) (λ _ → refl)
    (isSetΣ (isSetΠ λ _ → is-set (snd H)) λ _ → isProp→isSet (isPropIsGroupHom G H))

isPropIsInIm : (f : GroupHom G H) (x : ⟨ H ⟩) → isProp (isInIm f x)
isPropIsInIm f x = squash

isSetIm : (f : GroupHom G H) → isSet (Im f)
isSetIm {H = H} f = isSetΣ (is-set (snd H)) λ x → isProp→isSet (isPropIsInIm f x)

isPropIsInKer : (f : GroupHom G H) (x : ⟨ G ⟩) → isProp (isInKer f x)
isPropIsInKer {H = H} f x = is-set (snd H) _ _

isSetKer : (f : GroupHom G H) → isSet (Ker f)
isSetKer {G = G} f = isSetΣ (is-set (snd G)) λ x → isProp→isSet (isPropIsInKer f x)

isPropIsSurjective : (f : GroupHom G H) → isProp (isSurjective f)
isPropIsSurjective f = isPropΠ (λ x → isPropIsInIm f x)

isPropIsInjective : (f : GroupHom G H) → isProp (isInjective f)
isPropIsInjective {G = G} _ = isPropΠ2 (λ _ _ → is-set (snd G) _ _)

isPropIsMono : (f : GroupHom G H) → isProp (isMono f)
isPropIsMono {G = G} f = isPropImplicitΠ2 λ _ _ → isPropΠ (λ _ → is-set (snd G) _ _)


-- Logically equivalent versions of isInjective
isMono→isInjective : (f : GroupHom G H) → isMono f → isInjective f
isMono→isInjective f h x p = h (p ∙ sym (hom1g f))

isInjective→isMono : (f : GroupHom G H) → isInjective f → isMono f
isInjective→isMono {G = G} {H = H} f h {x = x} {y = y} p =
  x                      ≡⟨ sym (G.rid _) ⟩
  x G.· G.1g             ≡⟨ cong (x G.·_) (sym (G.invl _)) ⟩
  x G.· (G.inv y G.· y)  ≡⟨ G.assoc _ _ _ ⟩
  (x G.· G.inv y) G.· y  ≡⟨ cong (G._· y) idHelper ⟩
  G.1g G.· y             ≡⟨ G.lid _ ⟩
  y ∎
    where
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)

    idHelper : x G.· G.inv y ≡ G.1g
    idHelper = h _ (isHom f _ _ ∙
                    cong (λ a → f .fun x H.· a) (homInv f y) ∙
                    cong (H._· H.inv (f .fun y)) p ∙
                    H.invr _)

-- TODO: maybe it would be better to take this as the definition of isInjective?
isInjective→isContrKer : (f : GroupHom G H) → isInjective f → isContr (Ker f)
fst (isInjective→isContrKer {G = G} f hf) = 1g (snd G) , hom1g f
snd (isInjective→isContrKer {G = G} f hf) k =
  Σ≡Prop (isPropIsInKer f) (sym (isInjective→isMono f hf (k .snd ∙ sym (hom1g f))))

isContrKer→isInjective : (f : GroupHom G H) → isContr (Ker f) → isInjective f
isContrKer→isInjective {G = G} f ((a , b) , c) x y = cong fst (sym (c (x , y)) ∙ rem)
  where
  rem : (a , b) ≡ (1g (snd G) , hom1g f)
  rem = c (1g (snd G) , hom1g f)


-- Special homomorphisms and operations (id, composition...)
idGroupHom : GroupHom G G
fun idGroupHom = λ x → x
isHom idGroupHom _ _ = refl

isGroupHomComp : (f : GroupHom F G) → (g : GroupHom G H) → isGroupHom F H (fun g ∘ fun f)
isGroupHomComp f g x y = cong (fun g) (isHom f _ _) ∙ isHom g _ _

compGroupHom : GroupHom F G → GroupHom G H → GroupHom F H
fun (compGroupHom f g) = fun g ∘ fun f
isHom (compGroupHom f g) = isGroupHomComp f g

GroupHomDirProd : {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
                → GroupHom A C → GroupHom B D → GroupHom (DirProd A B) (DirProd C D)
fun (GroupHomDirProd mf1 mf2) = map-× (fun mf1) (fun mf2)
isHom (GroupHomDirProd mf1 mf2) a b = ≡-× (isHom mf1 _ _) (isHom mf2 _ _)

GroupHom≡ : {f g : GroupHom G H} → (fun f ≡ fun g) → f ≡ g
fun (GroupHom≡ p i) = p i
isHom (GroupHom≡ {G = G} {H = H} {f = f} {g = g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)


-- GroupEquiv identity, composition and inversion
idGroupEquiv : GroupEquiv G G
eq (idGroupEquiv {G = G}) = idEquiv ⟨ G ⟩
isHom idGroupEquiv = λ _ _ → refl

compGroupEquiv : GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
eq (compGroupEquiv f g) = compEquiv (eq f) (eq g)
isHom (compGroupEquiv f g) = isHom (compGroupHom (GroupEquiv.hom f) (GroupEquiv.hom g))

invGroupEquiv : GroupEquiv G H → GroupEquiv H G
eq (invGroupEquiv f) = invEquiv (eq f)
isHom (invGroupEquiv f) = isGroupHomInv f
  where
  isGroupHomInv : (f : GroupEquiv G H) → isGroupHom H G (invEq (GroupEquiv.eq f))
  isGroupHomInv {G = G} {H = H} f h h' = isInj-f _ _ (
    f' (g (h ⋆² h'))        ≡⟨ retEq (eq f) _ ⟩
    (h ⋆² h')               ≡⟨ sym (cong₂ _⋆²_ (retEq (eq f) h) (retEq (eq f) h')) ⟩
    (f' (g h) ⋆² f' (g h')) ≡⟨ sym (isHom (GroupEquiv.hom f) _ _) ⟩
    f' (g h ⋆¹ g h') ∎)
    where
    f' = fst (eq f)
    _⋆¹_ = _·_ (snd G)
    _⋆²_ = _·_ (snd H)
    g = invEq (eq f)

    isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
    isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (eq f)) x y)

GroupEquivDirProd : {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
                  → GroupEquiv A C → GroupEquiv B D
                  → GroupEquiv (DirProd A B) (DirProd C D)
eq (GroupEquivDirProd eq1 eq2) = ≃-× (eq eq1) (eq eq2)
isHom (GroupEquivDirProd eq1 eq2) = isHom (GroupHomDirProd (GroupEquiv.hom eq1) (GroupEquiv.hom eq2))

GroupEquiv≡ : {f g : GroupEquiv G H} → eq f ≡ eq g → f ≡ g
eq (GroupEquiv≡ p i) = p i
isHom (GroupEquiv≡ {G = G} {H = H} {f} {g} p i) = p-hom i
  where
  p-hom : PathP (λ i → isGroupHom G H (p i .fst)) (isHom f) (isHom g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)


-- GroupIso identity, composition and inversion
idGroupIso : GroupIso G G
isom idGroupIso = idIso
isHom idGroupIso = λ _ _ → refl

compGroupIso : GroupIso G H → GroupIso H F → GroupIso G F
isom (compGroupIso iso1 iso2) = compIso (isom iso1) (isom iso2)
isHom (compGroupIso iso1 iso2) = isGroupHomComp (GroupIso.hom iso1) (GroupIso.hom iso2)

invGroupIso : GroupIso G H → GroupIso H G
isom (invGroupIso iso1) = invIso (isom iso1)
isHom (invGroupIso iso1) = isGroupHomInv iso1
  where
  isGroupHomInv : (f : GroupIso G H) → isGroupHom H G (inv (isom f))
  isGroupHomInv {G = G} {H = H}  f h h' = isInj-f _ _ (
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

GroupIsoDirProd : {G : Group {ℓ}} {H : Group {ℓ'}} {A : Group {ℓ''}} {B : Group {ℓ'''}}
                → GroupIso G H → GroupIso A B → GroupIso (DirProd G A) (DirProd H B)
fun (isom (GroupIsoDirProd iso1 iso2)) prod =
  fun (isom iso1) (fst prod) , fun (isom iso2) (snd prod)
inv (isom (GroupIsoDirProd iso1 iso2)) prod =
  inv (isom iso1) (fst prod) , inv (isom iso2) (snd prod)
rightInv (isom (GroupIsoDirProd iso1 iso2)) a =
  ΣPathP (rightInv (isom iso1) (fst a) , (rightInv (isom iso2) (snd a)))
leftInv (isom (GroupIsoDirProd iso1 iso2)) a =
  ΣPathP (leftInv (isom iso1) (fst a) , (leftInv (isom iso2) (snd a)))
isHom (GroupIsoDirProd iso1 iso2) a b =
  ΣPathP (isHom iso1 (fst a) (fst b) , isHom iso2 (snd a) (snd b))


-- Conversion functions between different notions of group morphisms

GroupIso→GroupEquiv : GroupIso G H → GroupEquiv G H
GroupEquiv.eq (GroupIso→GroupEquiv i) = isoToEquiv (isom i)
GroupEquiv.isHom (GroupIso→GroupEquiv i) = isHom i

GroupEquiv→GroupIso : GroupEquiv G H → GroupIso G H
isom (GroupEquiv→GroupIso e) = equivToIso (eq e)
isHom (GroupEquiv→GroupIso e) = isHom e

-- TODO: prove the converse
BijectionIso→GroupIso : BijectionIso G H → GroupIso G H
BijectionIso→GroupIso {G = G} {H = H} i = grIso
  where
  f = fun (fun i)

  helper : (b : _) → isProp (Σ[ a ∈ ⟨ G ⟩ ] f a ≡ b)
  helper _ (a , ha) (b , hb) =
    Σ≡Prop (λ _ → is-set (snd H) _ _)
           (isInjective→isMono (fun i) (inj i) (ha ∙ sym hb) )

  grIso : GroupIso G H
  fun (isom grIso) = fun (fun i)
  inv (isom grIso) b = rec (helper b) (λ a → a) (surj i b) .fst
  rightInv (isom grIso) b = rec (helper b) (λ a → a) (surj i b) .snd
  leftInv (isom grIso) b j = rec (helper (f b)) (λ a → a)
                                 (propTruncIsProp (surj i (f b)) ∣ b , refl ∣ j) .fst
  isHom grIso = isHom (fun i)

BijectionIsoToGroupEquiv : BijectionIso G H → GroupEquiv G H
BijectionIsoToGroupEquiv i = GroupIso→GroupEquiv (BijectionIso→GroupIso i)
