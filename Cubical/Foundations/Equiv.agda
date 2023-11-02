{-

Theory about equivalences

Definitions are in Core/Glue.agda but re-exported by this module

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])

There are more statements about equivalences in Equiv/Properties.agda:

- if f is an equivalence then (cong f) is an equivalence
- if f is an equivalence then precomposition with f is an equivalence
- if f is an equivalence then postcomposition with f is an equivalence

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Equiv.Base public
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

infixr 30 _∙ₑ_

equivIsEquiv : (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = snd e

equivCtr : (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst

equivCtrPath : (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .snd .equiv-proof y .snd


-- Proof using isPropIsContr. This is slow and the direct proof below is better

isPropIsEquiv' : (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv' f u0 u1 i) y =
  isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

-- Direct proof that computes quite ok (can be optimized further if
-- necessary, see:
-- https://github.com/mortberg/cubicaltt/blob/pi4s3_dimclosures/examples/brunerie2.ctt#L562

isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv f p q i) y =
  let p2 = p .equiv-proof y .snd
      q2 = q .equiv-proof y .snd
  in p2 (q .equiv-proof y .fst) i
   , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                            ; (i = i1) → q2 w (j ∨ ~ k)
                            ; (j = i0) → p2 (q2 w (~ k)) i
                            ; (j = i1) → w })
                   (p2 w (i ∨ j))

equivEq : {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
equivEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i

module _ {f : A → B} (equivF : isEquiv f) where
  funIsEq : A → B
  funIsEq = f

  invIsEq : B → A
  invIsEq y = equivF .equiv-proof y .fst .fst

  secIsEq : section f invIsEq
  secIsEq y = equivF .equiv-proof y .fst .snd

  retIsEq : retract f invIsEq
  retIsEq a i = equivF .equiv-proof (f a) .snd (a , refl) i .fst

  commSqIsEq : ∀ a → Square (secIsEq (f a)) refl (cong f (retIsEq a)) refl
  commSqIsEq a i = equivF .equiv-proof (f a) .snd (a , refl) i .snd

  commPathIsEq : ∀ a → secIsEq (f a) ≡ cong f (retIsEq a)
  commPathIsEq a i j =
    hcomp
      (λ k → λ
        { (i = i0) → secIsEq (f a) j
        ; (i = i1) → f (retIsEq a (j ∨ ~ k))
        ; (j = i0) → f (retIsEq a (i ∧ ~ k))
        ; (j = i1) → f a
        })
      (commSqIsEq a i j)

module _ (w : A ≃ B) where
  invEq : B → A
  invEq = invIsEq (snd w)

  retEq : retract (w .fst) invEq
  retEq = retIsEq (snd w)

  secEq : section (w .fst) invEq
  secEq = secIsEq (snd w)

open Iso

equivToIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → Iso A B
fun (equivToIso e) = e .fst
inv (equivToIso e) = invEq e
rightInv (equivToIso e) = secEq e
leftInv (equivToIso e)  = retEq e

-- TODO: there should be a direct proof of this that doesn't use equivToIso
invEquiv : A ≃ B → B ≃ A
invEquiv e = isoToEquiv (invIso (equivToIso e))

invEquivIdEquiv : (A : Type ℓ) → invEquiv (idEquiv A) ≡ idEquiv A
invEquivIdEquiv _ = equivEq refl

compEquiv : A ≃ B → B ≃ C → A ≃ C
compEquiv f g .fst = g .fst ∘ f .fst
compEquiv {A = A} {C = C} f g .snd .equiv-proof c = contr
  where
  contractG = g .snd .equiv-proof c .snd

  secFiller : (a : A) (p : g .fst (f .fst a) ≡ c) → _ {- square in A -}
  secFiller a p = compPath-filler (cong (invEq f ∘ fst) (contractG (_ , p))) (retEq f a)

  contr : isContr (fiber (g .fst ∘ f .fst) c)
  contr .fst .fst = invEq f (invEq g c)
  contr .fst .snd = cong (g .fst) (secEq f (invEq g c)) ∙ secEq g c
  contr .snd (a , p) i .fst = secFiller a p i1 i
  contr .snd (a , p) i .snd j =
    hcomp
      (λ k → λ
        { (i = i1) → fSquare k
        ; (j = i0) → g .fst (f .fst (secFiller a p k i))
        ; (j = i1) → contractG (_  , p) i .snd k
        })
      (g .fst (secEq f (contractG (_ , p) i .fst) j))
    where
    fSquare : I → C
    fSquare k =
      hcomp
        (λ l → λ
          { (j = i0) → g .fst (f .fst (retEq f a k))
          ; (j = i1) → p (k ∧ l)
          ; (k = i0) → g .fst (secEq f (f .fst a) j)
          ; (k = i1) → p (j ∧ l)
          })
        (g .fst (f .snd .equiv-proof (f .fst a) .snd (a , refl) k .snd j))

_∙ₑ_ = compEquiv

compEquivIdEquiv : (e : A ≃ B) → compEquiv (idEquiv A) e ≡ e
compEquivIdEquiv e = equivEq refl

compEquivEquivId : (e : A ≃ B) → compEquiv e (idEquiv B) ≡ e
compEquivEquivId e = equivEq refl

invEquiv-is-rinv : (e : A ≃ B) → compEquiv e (invEquiv e) ≡ idEquiv A
invEquiv-is-rinv e = equivEq (funExt (retEq e))

invEquiv-is-linv : (e : A ≃ B) → compEquiv (invEquiv e) e ≡ idEquiv B
invEquiv-is-linv e = equivEq (funExt (secEq e))

compEquiv-assoc : (f : A ≃ B) (g : B ≃ C) (h : C ≃ D)
                → compEquiv f (compEquiv g h) ≡ compEquiv (compEquiv f g) h
compEquiv-assoc f g h = equivEq refl

LiftEquiv : A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv .fst a .lower = a
LiftEquiv .snd .equiv-proof = strictContrFibers lower

Lift≃Lift : (e : A ≃ B) → Lift {j = ℓ'} A ≃ Lift {j = ℓ''} B
Lift≃Lift e .fst a .lower = e .fst (a .lower)
Lift≃Lift e .snd .equiv-proof b .fst .fst .lower = invEq e (b .lower)
Lift≃Lift e .snd .equiv-proof b .fst .snd i .lower =
  e .snd .equiv-proof (b .lower) .fst .snd i
Lift≃Lift e .snd .equiv-proof b .snd (a , p) i .fst .lower =
  e .snd .equiv-proof (b .lower) .snd (a .lower , cong lower p) i .fst
Lift≃Lift e .snd .equiv-proof b .snd (a , p) i .snd j .lower =
  e .snd .equiv-proof (b .lower) .snd (a .lower , cong lower p) i .snd j

isContr→Equiv : isContr A → isContr B → A ≃ B
isContr→Equiv Actr Bctr = isoToEquiv (isContr→Iso Actr Bctr)

propBiimpl→Equiv : (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → A ≃ B
propBiimpl→Equiv Aprop Bprop f g = f , hf
  where
  hf : isEquiv f
  hf .equiv-proof y .fst          = (g y , Bprop (f (g y)) y)
  hf .equiv-proof y .snd h i .fst = Aprop (g y) (h .fst) i
  hf .equiv-proof y .snd h i .snd = isProp→isSet' Bprop (Bprop (f (g y)) y) (h .snd)
                                                  (cong f (Aprop (g y) (h .fst))) refl i

isEquivPropBiimpl→Equiv : isProp A → isProp B
                        → ((A → B) × (B → A)) ≃ (A ≃ B)
isEquivPropBiimpl→Equiv {A = A} {B = B} Aprop Bprop = isoToEquiv isom where
  isom : Iso (Σ (A → B) (λ _ → B → A)) (A ≃ B)
  isom .fun (f , g) = propBiimpl→Equiv Aprop Bprop f g
  isom .inv e = equivFun e , invEq e
  isom .rightInv e = equivEq refl
  isom .leftInv _ = refl

equivΠCod : ∀ {F : A → Type ℓ} {G : A → Type ℓ'}
        → ((x : A) → F x ≃ G x) → ((x : A) → F x) ≃ ((x : A) → G x)
equivΠCod k .fst f x = k x .fst (f x)
equivΠCod k .snd .equiv-proof f .fst .fst x   = equivCtr (k x) (f x) .fst
equivΠCod k .snd .equiv-proof f .fst .snd i x = equivCtr (k x) (f x) .snd i
equivΠCod k .snd .equiv-proof f .snd (g , p) i .fst x =
  equivCtrPath (k x) (f x) (g x , λ j → p j x) i .fst
equivΠCod k .snd .equiv-proof f .snd (g , p) i .snd j x =
  equivCtrPath (k x) (f x) (g x , λ k → p k x) i .snd j

equivImplicitΠCod : ∀ {F : A → Type ℓ} {G : A → Type ℓ'}
        → ({x : A} → F x ≃ G x) → ({x : A} → F x) ≃ ({x : A} → G x)
equivImplicitΠCod k .fst f {x} = k {x} .fst (f {x})
equivImplicitΠCod k .snd .equiv-proof f .fst .fst {x}   = equivCtr (k {x}) (f {x}) .fst
equivImplicitΠCod k .snd .equiv-proof f .fst .snd i {x} = equivCtr (k {x}) (f {x}) .snd i
equivImplicitΠCod k .snd .equiv-proof f .snd (g , p) i .fst {x} =
  equivCtrPath (k {x}) (f {x}) (g {x} , λ j → p j {x}) i .fst
equivImplicitΠCod k .snd .equiv-proof f .snd (g , p) i .snd j {x} =
  equivCtrPath (k {x}) (f {x}) (g {x} , λ k → p k {x}) i .snd j

equiv→Iso : (A ≃ B) → (C ≃ D) → Iso (A → C) (B → D)
equiv→Iso h k .Iso.fun f b = equivFun k (f (invEq h b))
equiv→Iso h k .Iso.inv g a = invEq k (g (equivFun h a))
equiv→Iso h k .Iso.rightInv g = funExt λ b → secEq k _ ∙ cong g (secEq h b)
equiv→Iso h k .Iso.leftInv f = funExt λ a → retEq k _ ∙ cong f (retEq h a)

equiv→ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
equiv→ h k = isoToEquiv (equiv→Iso h k)


equivΠ' : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {A' : Type ℓA'}
  {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (eA : A ≃ A')
  (eB : {a : A} {a' : A'} → eA .fst a ≡ a' → B a ≃ B' a')
  → ((a : A) → B a) ≃ ((a' : A') → B' a')
equivΠ' {B' = B'} eA eB = isoToEquiv isom
  where
  open Iso

  isom : Iso _ _
  isom .fun f a' =
    eB (secEq eA a') .fst (f (invEq eA a'))
  isom .inv f' a =
    invEq (eB refl) (f' (eA .fst a))
  isom .rightInv f' =
    funExt λ a' →
    J (λ a'' p → eB p .fst (invEq (eB refl) (f' (p i0))) ≡ f' a'')
      (secEq (eB refl) (f' (eA .fst (invEq eA a'))))
      (secEq eA a')
  isom .leftInv f =
    funExt λ a →
    subst
      (λ p → invEq (eB refl) (eB p .fst (f (invEq eA (eA .fst a)))) ≡ f a)
      (sym (commPathIsEq (eA .snd) a))
      (J (λ a'' p → invEq (eB refl) (eB (cong (eA .fst) p) .fst (f (invEq eA (eA .fst a)))) ≡ f a'')
        (retEq (eB refl) (f (invEq eA (eA .fst a))))
        (retEq eA a))

equivΠ : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {A' : Type ℓA'}
  {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (eA : A ≃ A')
  (eB : (a : A) → B a ≃ B' (eA .fst a))
  → ((a : A) → B a) ≃ ((a' : A') → B' a')
equivΠ {B = B} {B' = B'} eA eB = equivΠ' eA (λ {a = a} p → J (λ a' p → B a ≃ B' a') (eB a) p)


equivCompIso : (A ≃ B) → (C ≃ D) → Iso (A ≃ C) (B ≃ D)
equivCompIso h k .Iso.fun f = compEquiv (compEquiv (invEquiv h) f) k
equivCompIso h k .Iso.inv g = compEquiv (compEquiv h g) (invEquiv k)
equivCompIso h k .Iso.rightInv g = equivEq (equiv→Iso h k .Iso.rightInv (equivFun g))
equivCompIso h k .Iso.leftInv f = equivEq (equiv→Iso h k .Iso.leftInv (equivFun f))

equivComp : (A ≃ B) → (C ≃ D) → (A ≃ C) ≃ (B ≃ D)
equivComp h k = isoToEquiv (equivCompIso h k)

-- Some helpful notation:
_≃⟨_⟩_ : (X : Type ℓ) → (X ≃ B) → (B ≃ C) → (X ≃ C)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (X : Type ℓ) → (X ≃ X)
_■ = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

composesToId→Equiv : (f : A → B) (g : B → A) → f ∘ g ≡ idfun B → isEquiv f → isEquiv g
composesToId→Equiv f g id iseqf =
  isoToIsEquiv
    (iso g f
         (λ b → (λ i → equiv-proof iseqf (f b) .snd (g (f b) , cong (λ h → h (f b)) id) (~ i) .fst)
                ∙∙ cong (λ x → equiv-proof iseqf (f b) .fst .fst) id
                ∙∙ λ i → equiv-proof iseqf (f b) .snd (b , refl) i .fst)
         λ a i → id i a)

precomposesToId→Equiv : (f : A → B) (g : B → A) → f ∘ g ≡ idfun B → isEquiv g → isEquiv f
precomposesToId→Equiv f g id iseqg =  subst isEquiv (sym f-≡-g⁻) (snd (invEquiv (_ , iseqg)))
  where
     g⁻ = invEq (g , iseqg)

     f-≡-g⁻ : _
     f-≡-g⁻ = cong (f ∘_ ) (cong fst (sym (invEquiv-is-linv (g , iseqg)))) ∙ cong (_∘ g⁻) id

-- equivalence between isEquiv and isEquiv'

isEquiv-isEquiv'-Iso : (f : A → B) → Iso (isEquiv f) (isEquiv' f)
isEquiv-isEquiv'-Iso f .fun p = p .equiv-proof
isEquiv-isEquiv'-Iso f .inv q .equiv-proof = q
isEquiv-isEquiv'-Iso f .rightInv q = refl
isEquiv-isEquiv'-Iso f .leftInv p i .equiv-proof = p .equiv-proof

isEquiv≃isEquiv' : (f : A → B) → isEquiv f ≃ isEquiv' f
isEquiv≃isEquiv' f = isoToEquiv (isEquiv-isEquiv'-Iso f)

-- The fact that funExt is an equivalence can be found in Cubical.Functions.FunExtEquiv

