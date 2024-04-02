{-
This file contains:

- Elementary properties of homomorphisms
- H-level results for the properties of morphisms
- Special homomorphisms and operations (id, composition, inversion)
- Conversion functions between different notions of group morphisms

-}
{-# OPTIONS --safe #-}
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

open import Cubical.HITs.PropositionalTruncation renaming (map to pMap)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    E F G H : Group ℓ

open Iso
open GroupStr
open IsGroupHom
open BijectionIso


-- Elementary properties of homomorphisms
module _ {A : Type ℓ} {B : Type ℓ'} (G : GroupStr A) (f : A → B) (H : GroupStr B)
  (pres : (x y : A) → f (G ._·_ x y) ≡ H ._·_ (f x) (f y))
  where

  private
    module G = GroupStr G
    module H = GroupStr H

  -- ϕ(1g) ≡ 1g
  hom1g : f G.1g ≡ H.1g
  hom1g =
    f G.1g                                  ≡⟨ sym (H.·IdR _) ⟩
    f G.1g H.· H.1g                         ≡⟨ (λ i → f G.1g H.· H.·InvR (f G.1g) (~ i)) ⟩
    f G.1g H.· (f G.1g H.· H.inv (f G.1g))  ≡⟨ H.·Assoc _ _ _ ⟩
    (f G.1g H.· f G.1g) H.· H.inv (f G.1g)  ≡⟨ sym (cong (λ x → x H.· _)
                                                (sym (cong f (G.·IdL _)) ∙ pres G.1g G.1g)) ⟩
    f G.1g H.· H.inv (f G.1g)               ≡⟨ H.·InvR _ ⟩
    H.1g ∎

  -- ϕ(- x) = - ϕ(x)
  homInv : ∀ g → f (G.inv g) ≡ H.inv (f g)
  homInv g =
    f (G.inv g)                            ≡⟨ sym (H.·IdR _) ⟩
    f (G.inv g) H.· H.1g                   ≡⟨ cong (_ H.·_) (sym (H.·InvR _)) ⟩
    f (G.inv g) H.· (f g H.· H.inv (f g))  ≡⟨ H.·Assoc _ _ _ ⟩
    (f (G.inv g) H.· f g) H.· H.inv (f g)  ≡⟨ cong (H._· _) (sym (pres _ g) ∙∙ cong f (G.·InvL g) ∙∙ hom1g) ⟩
    H.1g H.· H.inv (f g)                   ≡⟨ H.·IdL _ ⟩
    H.inv (f g) ∎

module _ {A : Type ℓ} {B : Type ℓ'} {G : GroupStr A} {f : A → B} {H : GroupStr B}
  (pres : (x y : A) → f (G ._·_ x y) ≡ H ._·_ (f x) (f y))
  where

  makeIsGroupHom : IsGroupHom G f H
  makeIsGroupHom .pres· = pres
  makeIsGroupHom .pres1 = hom1g G f H pres
  makeIsGroupHom .presinv = homInv G f H pres

isGroupHomInv : (f : GroupEquiv G H) → IsGroupHom (H .snd) (invEq (fst f)) (G .snd)
isGroupHomInv {G = G} {H = H} f = makeIsGroupHom λ h h' →
  isInj-f _ _
    (f' (g (h ⋆² h'))        ≡⟨ secEq (fst f) _ ⟩
     (h ⋆² h')               ≡⟨ sym (cong₂ _⋆²_ (secEq (fst f) h) (secEq (fst f) h')) ⟩
     (f' (g h) ⋆² f' (g h')) ≡⟨ sym (pres· (snd f) _ _) ⟩
     f' (g h ⋆¹ g h') ∎)
  where
  f' = fst (fst f)
  _⋆¹_ = _·_ (snd G)
  _⋆²_ = _·_ (snd H)
  g = invEq (fst f)

  isInj-f : (x y : ⟨ G ⟩) → f' x ≡ f' y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding (snd (fst f)) x y)

-- H-level results
isPropIsGroupHom : (G : Group ℓ) (H : Group ℓ') {f : ⟨ G ⟩ → ⟨ H ⟩}
                 → isProp (IsGroupHom (G .snd) f (H .snd))
isPropIsGroupHom G H =
  isOfHLevelRetractFromIso 1 IsGroupHomIsoΣ
    (isProp×
      (isPropΠ2 λ _ _ → GroupStr.is-set (snd H) _ _)
      (isProp×
        (GroupStr.is-set (snd H) _ _)
        (isPropΠ λ _ → GroupStr.is-set (snd H) _ _)))

isSetGroupHom : isSet (GroupHom G H)
isSetGroupHom {G = G} {H = H} =
  isSetΣ (isSetΠ λ _ → is-set (snd H)) λ _ → isProp→isSet (isPropIsGroupHom G H)

isPropIsInIm : (f : GroupHom G H) (x : ⟨ H ⟩) → isProp (isInIm f x)
isPropIsInIm f x = squash₁

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
isMono→isInjective f h x p = h (p ∙ sym (f .snd .pres1))

isInjective→isMono : (f : GroupHom G H) → isInjective f → isMono f
isInjective→isMono {G = G} {H = H} f h {x = x} {y = y} p =
  x                      ≡⟨ sym (G.·IdR _) ⟩
  x G.· G.1g             ≡⟨ cong (x G.·_) (sym (G.·InvL _)) ⟩
  x G.· (G.inv y G.· y)  ≡⟨ G.·Assoc _ _ _ ⟩
  (x G.· G.inv y) G.· y  ≡⟨ cong (G._· y) idHelper ⟩
  G.1g G.· y             ≡⟨ G.·IdL _ ⟩
  y ∎
    where
    module G = GroupStr (snd G)
    module H = GroupStr (snd H)

    idHelper : x G.· G.inv y ≡ G.1g
    idHelper = h _ (f .snd .pres· _ _ ∙
                    cong (λ a → f .fst x H.· a) (f .snd .presinv y) ∙
                    cong (H._· H.inv (f .fst y)) p ∙
                    H.·InvR _)

-- TODO: maybe it would be better to take this as the definition of isInjective?
isInjective→isContrKer : (f : GroupHom G H) → isInjective f → isContr (Ker f)
fst (isInjective→isContrKer {G = G} f hf) = 1g (snd G) , f .snd .pres1
snd (isInjective→isContrKer {G = G} f hf) k =
  Σ≡Prop (isPropIsInKer f) (sym (isInjective→isMono f hf (k .snd ∙ sym (f .snd .pres1))))

isContrKer→isInjective : (f : GroupHom G H) → isContr (Ker f) → isInjective f
isContrKer→isInjective {G = G} f ((a , b) , c) x y = cong fst (sym (c (x , y)) ∙ rem)
  where
  rem : (a , b) ≡ (1g (snd G) , pres1 (snd f))
  rem = c (1g (snd G) , pres1 (snd f))


-- Special homomorphisms and operations (id, composition...)
idGroupHom : GroupHom G G
idGroupHom .fst x = x
idGroupHom .snd = makeIsGroupHom λ _ _ → refl

isGroupHomComp : (f : GroupHom F G) → (g : GroupHom G H) → IsGroupHom (F .snd) (fst g ∘ fst f) (H .snd)
isGroupHomComp f g = makeIsGroupHom λ _ _ → cong (fst g) (f .snd .pres· _ _) ∙ (g .snd .pres· _ _)

compGroupHom : GroupHom F G → GroupHom G H → GroupHom F H
fst (compGroupHom f g) = fst g ∘ fst f
snd (compGroupHom f g) = isGroupHomComp f g

trivGroupHom : GroupHom G H
fst (trivGroupHom {H = H}) _ = 1g (snd H)
snd (trivGroupHom {H = H}) = makeIsGroupHom λ _ _ → sym (·IdR (snd H) _)

GroupHomDirProd : {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''}
                → GroupHom A C → GroupHom B D → GroupHom (DirProd A B) (DirProd C D)
fst (GroupHomDirProd mf1 mf2) = map-× (fst mf1) (fst mf2)
snd (GroupHomDirProd mf1 mf2) = makeIsGroupHom λ _ _ → ≡-× (mf1 .snd .pres· _ _) (mf2 .snd .pres· _ _)

GroupHom≡ : {f g : GroupHom G H} → (fst f ≡ fst g) → f ≡ g
fst (GroupHom≡ p i) = p i
snd (GroupHom≡ {G = G} {H = H} {f = f} {g = g} p i) = p-hom i
  where
  p-hom : PathP (λ i → IsGroupHom (G .snd) (p i) (H .snd)) (f .snd) (g .snd)
  p-hom = toPathP (isPropIsGroupHom G H _ _)

compGroupHomAssoc : (e : GroupHom E F) → (f : GroupHom F G) → (g : GroupHom G H)
                  → compGroupHom (compGroupHom e f) g ≡ compGroupHom e (compGroupHom f g)
compGroupHomAssoc e f g = GroupHom≡ refl

compGroupHomId : (f : GroupHom F G) → compGroupHom f idGroupHom ≡ f
compGroupHomId f = GroupHom≡ refl

-- The composition of surjective maps is surjective
compSurjective : ∀ {ℓ ℓ' ℓ''} {G : Group ℓ} {H : Group ℓ'} {L : Group ℓ''}
         → (G→H : GroupHom G H) (H→L : GroupHom H L)
         → isSurjective G→H → isSurjective H→L
         → isSurjective (compGroupHom G→H H→L)
compSurjective G→H H→L surj1 surj2 l =
  rec squash₁
    (λ {(h , p)
      → pMap (λ {(g , q) → g , (cong (fst H→L) q ∙ p)})
        (surj1 h)})
    (surj2 l)

-- GroupEquiv identity, composition and inversion
idGroupEquiv : GroupEquiv G G
fst (idGroupEquiv {G = G}) = idEquiv ⟨ G ⟩
snd idGroupEquiv = makeIsGroupHom λ _ _ → refl

compGroupEquiv : GroupEquiv F G → GroupEquiv G H → GroupEquiv F H
fst (compGroupEquiv f g) = compEquiv (fst f) (fst g)
snd (compGroupEquiv f g) = isGroupHomComp (_ , f .snd) (_ , g .snd)

invGroupEquiv : GroupEquiv G H → GroupEquiv H G
fst (invGroupEquiv f) = invEquiv (fst f)
snd (invGroupEquiv f) = isGroupHomInv f

GroupEquivDirProd : {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''} {D : Group ℓ'''}
                  → GroupEquiv A C → GroupEquiv B D
                  → GroupEquiv (DirProd A B) (DirProd C D)
fst (GroupEquivDirProd eq1 eq2) = ≃-× (fst eq1) (fst eq2)
snd (GroupEquivDirProd eq1 eq2) = GroupHomDirProd (_ , eq1 .snd) (_ , eq2 .snd) .snd

GroupEquiv≡ : {f g : GroupEquiv G H} → fst f ≡ fst g → f ≡ g
fst (GroupEquiv≡ p i) = p i
snd (GroupEquiv≡ {G = G} {H = H} {f} {g} p i) = p-hom i
  where
  p-hom : PathP (λ i → IsGroupHom (G .snd) (p i .fst) (H .snd)) (snd f) (snd g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)


-- GroupIso identity, composition and inversion
idGroupIso : GroupIso G G
fst idGroupIso = idIso
snd idGroupIso = makeIsGroupHom λ _ _ → refl

compGroupIso : GroupIso G H → GroupIso H F → GroupIso G F
fst (compGroupIso iso1 iso2) = compIso (fst iso1) (fst iso2)
snd (compGroupIso iso1 iso2) = isGroupHomComp (_ , snd iso1) (_ , snd iso2)

invGroupIso : GroupIso G H → GroupIso H G
fst (invGroupIso iso1) = invIso (fst iso1)
snd (invGroupIso iso1) = isGroupHomInv (isoToEquiv (fst iso1) , snd iso1)

GroupIsoDirProd : {G : Group ℓ} {H : Group ℓ'} {A : Group ℓ''} {B : Group ℓ'''}
                → GroupIso G H → GroupIso A B → GroupIso (DirProd G A) (DirProd H B)
fun (fst (GroupIsoDirProd iso1 iso2)) prod =
  fun (fst iso1) (fst prod) , fun (fst iso2) (snd prod)
inv (fst (GroupIsoDirProd iso1 iso2)) prod =
  inv (fst iso1) (fst prod) , inv (fst iso2) (snd prod)
rightInv (fst (GroupIsoDirProd iso1 iso2)) a =
  ΣPathP (rightInv (fst iso1) (fst a) , (rightInv (fst iso2) (snd a)))
leftInv (fst (GroupIsoDirProd iso1 iso2)) a =
  ΣPathP (leftInv (fst iso1) (fst a) , (leftInv (fst iso2) (snd a)))
snd (GroupIsoDirProd iso1 iso2) = makeIsGroupHom λ a b →
  ΣPathP (pres· (snd iso1) (fst a) (fst b) , pres· (snd iso2) (snd a) (snd b))

GroupIso≡ : {f g : GroupIso G H} → f .fst ≡ g .fst → f ≡ g
fst (GroupIso≡ {G = G} {H = H} {f} {g} p i) = p i
snd (GroupIso≡ {G = G} {H = H} {f} {g} p i) = p-hom i
  where
  p-hom : PathP (λ i → IsGroupHom (G .snd) (p i .fun) (H .snd)) (snd f) (snd g)
  p-hom = toPathP (isPropIsGroupHom G H _ _)


-- Conversion functions between different notions of group morphisms
GroupEquiv→GroupHom : GroupEquiv G H → GroupHom G H
fst (GroupEquiv→GroupHom ((f , _) , _)) = f
snd (GroupEquiv→GroupHom (_ , isHom)) = isHom

GroupIso→GroupEquiv : GroupIso G H → GroupEquiv G H
fst (GroupIso→GroupEquiv i) = isoToEquiv (fst i)
snd (GroupIso→GroupEquiv i) = snd i

GroupEquiv→GroupIso : GroupEquiv G H → GroupIso G H
fst (GroupEquiv→GroupIso e) = equivToIso (fst e)
snd (GroupEquiv→GroupIso e) = snd e

GroupIso→GroupHom : GroupIso G H → GroupHom G H
GroupIso→GroupHom i = GroupEquiv→GroupHom (GroupIso→GroupEquiv i)

-- TODO: prove the converse
BijectionIso→GroupIso : BijectionIso G H → GroupIso G H
BijectionIso→GroupIso {G = G} {H = H} i = grIso
  where
  f = fst (fun i)

  helper : (b : _) → isProp (Σ[ a ∈ ⟨ G ⟩ ] f a ≡ b)
  helper _ (a , ha) (b , hb) =
    Σ≡Prop (λ _ → is-set (snd H) _ _)
           (isInjective→isMono (fun i) (inj i) (ha ∙ sym hb) )

  grIso : GroupIso G H
  fun (fst grIso) = f
  inv (fst grIso) b = rec (helper b) (λ a → a) (surj i b) .fst
  rightInv (fst grIso) b = rec (helper b) (λ a → a) (surj i b) .snd
  leftInv (fst grIso) b j = rec (helper (f b)) (λ a → a)
                                 (isPropPropTrunc (surj i (f b)) ∣ b , refl ∣₁ j) .fst
  snd grIso = snd (fun i)

BijectionIsoToGroupEquiv : BijectionIso G H → GroupEquiv G H
BijectionIsoToGroupEquiv i = GroupIso→GroupEquiv (BijectionIso→GroupIso i)
