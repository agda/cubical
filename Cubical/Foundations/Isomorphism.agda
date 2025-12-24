{-

Theory about isomorphisms

- Definitions of [section] and [retract]
- Definition of isomorphisms ([Iso])
- Any isomorphism is an equivalence ([isoToEquiv])

-}
module Cubical.Foundations.Isomorphism where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Base

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

-- Section and retract
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a

record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    sec : section fun inv
    ret : retract fun inv

isIso : (A → B) → Type _
isIso {A = A} {B = B} f = Σ[ g ∈ (B → A) ] Σ[ _ ∈ section f g ] retract f g

isoFunInjective : (f : Iso A B) → (x y : A) → Iso.fun f x ≡ Iso.fun f y → x ≡ y
isoFunInjective f x y h = sym (Iso.ret f x) ∙∙ cong (Iso.inv f) h ∙∙ Iso.ret f y

isoInvInjective : (f : Iso A B) → (x y : B) → Iso.inv f x ≡ Iso.inv f y → x ≡ y
isoInvInjective f x y h = sym (Iso.sec f x) ∙∙ cong (Iso.fun f) h ∙∙ Iso.sec f y

-- Any iso is an equivalence
module _ (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; sec to s
                      ; ret to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)


isoToEquiv : Iso A B → A ≃ B
isoToEquiv i .fst = i .Iso.fun
isoToEquiv i .snd = isoToIsEquiv i

IsoToIsIso : (f : Iso A B) → isIso (f .Iso.fun)
IsoToIsIso f .fst = f .Iso.inv
IsoToIsIso f .snd .fst = f .Iso.sec
IsoToIsIso f .snd .snd = f .Iso.ret

isIsoToIso : {f : A → B} → isIso f → Iso A B
isIsoToIso {f = f} fIsIso .Iso.fun = f
isIsoToIso fIsIso .Iso.inv = fIsIso .fst
isIsoToIso fIsIso .Iso.sec = fIsIso .snd .fst
isIsoToIso fIsIso .Iso.ret = fIsIso .snd .snd

isIsoToIsEquiv : {f : A → B} → isIso f → isEquiv f
isIsoToIsEquiv fIsIso = isoToIsEquiv (isIsoToIso fIsIso)

isoToPath : Iso A B → A ≡ B
isoToPath {A = A} {B = B} f i =
  Glue B (λ { (i = i0) → (A , isoToEquiv f)
            ; (i = i1) → (B , idEquiv B) })

open Iso

invIso : Iso A B → Iso B A
fun (invIso f) = inv f
inv (invIso f) = fun f
sec (invIso f) = ret f
ret (invIso f)  = sec f

compIso : Iso A B → Iso B C → Iso A C
fun (compIso i j)       = fun j ∘ fun i
inv (compIso i j) = inv i ∘ inv j
sec (compIso i j) b = cong (fun j) (sec i (inv j b)) ∙ sec j b
ret (compIso i j) a = cong (inv i) (ret j (fun i a)) ∙ ret i a

composesToId→Iso : (G : Iso A B) (g : B → A) → G .fun ∘ g ≡ idfun B → Iso B A
fun (composesToId→Iso _ g _)             = g
inv (composesToId→Iso j _ _) = fun j
sec (composesToId→Iso i g path) b =
  sym (ret i (g (fun i b))) ∙∙ cong (λ g → inv i (g (fun i b))) path ∙∙ ret i b
ret (composesToId→Iso _ _ path) b i = path i b

idIso : Iso A A
fun idIso = idfun _
inv idIso = idfun _
sec idIso _ = refl
ret idIso _  = refl

compIsoIdL : (isom : Iso A B) → compIso idIso isom ≡ isom
fun (compIsoIdL isom i) = fun isom
inv (compIsoIdL isom i) = inv isom
sec (compIsoIdL isom i) b = lUnit (isom .sec b) (~ i)
ret (compIsoIdL isom i) a = rUnit (isom .ret a) (~ i)

compIsoIdR : (isom : Iso A B) → compIso isom idIso ≡ isom
fun (compIsoIdR isom i) = fun isom
inv (compIsoIdR isom i) = inv isom
sec (compIsoIdR isom i) b = rUnit (isom .sec b) (~ i)
ret (compIsoIdR isom i) a = lUnit (isom .ret a) (~ i)

LiftIso : Iso A (Lift ℓ' A)
fun LiftIso = lift
inv LiftIso = lower
sec LiftIso _ = refl
ret LiftIso _  = refl

isContr→Iso : isContr A → isContr B → Iso A B
fun (isContr→Iso _ Bctr) _ = Bctr .fst
inv (isContr→Iso Actr _) _ = Actr .fst
sec (isContr→Iso _ Bctr) = Bctr .snd
ret (isContr→Iso Actr _)  = Actr .snd

isContr→Iso' : isContr A → isContr B → (A → B) → Iso A B
fun (isContr→Iso' _ Bctr f) = f
inv (isContr→Iso' Actr _ _) _ = Actr .fst
sec (isContr→Iso' _ Bctr f) = isContr→isProp Bctr _
ret (isContr→Iso' Actr _ _)  = Actr .snd

isProp→Iso :  (Aprop : isProp A) (Bprop : isProp B) (f : A → B) (g : B → A) → Iso A B
fun (isProp→Iso _ _ f _) = f
inv (isProp→Iso _ _ _ g) = g
sec (isProp→Iso _ Bprop f g) b = Bprop (f (g b)) b
ret (isProp→Iso Aprop _ f g) a  = Aprop (g (f a)) a

domIso : ∀ {ℓ} {C : Type ℓ} → Iso A B → Iso (A → C) (B → C)
fun (domIso e) f b = f (inv e b)
inv (domIso e) f a = f (fun e a)
sec (domIso e) f i x = f (sec e x i)
ret (domIso e) f i x = f (ret e x i)

-- Helpful notation
_Iso⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} {B : Type ℓ'} {C : Type ℓ''} (X : Type ℓ) → Iso X B → Iso B C → Iso X C
_ Iso⟨ f ⟩ g = compIso f g

_∎Iso : ∀ {ℓ} (A : Type ℓ) → Iso A A
A ∎Iso = idIso {A = A}

infixr  0 _Iso⟨_⟩_
infix   1 _∎Iso

codomainIsoDep : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
                 → ((a : A) → Iso (B a) (C a))
                 → Iso ((a : A) → B a) ((a : A) → C a)
fun (codomainIsoDep is) f a = fun (is a) (f a)
inv (codomainIsoDep is) f a = inv (is a) (f a)
sec (codomainIsoDep is) f = funExt λ a → sec (is a) (f a)
ret (codomainIsoDep is) f = funExt λ a → ret (is a) (f a)

codomainIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
           → Iso B C
           → Iso (A → B) (A → C)
codomainIso z = codomainIsoDep λ _ → z

endoIso : Iso A B → Iso (A → A) (B → B)
endoIso is = compIso (domIso is) (codomainIso is)

binaryOpIso : Iso A B → Iso (A → A → A) (B → B → B)
binaryOpIso is = compIso (domIso is) (codomainIso (endoIso is))

Iso≡Set : isSet A → isSet B → (f g : Iso A B)
        → ((x : A) → f .fun x ≡ g .fun x)
        → ((x : B) → f .inv x ≡ g .inv x)
        → f ≡ g
fun (Iso≡Set hA hB f g hfun hinv i) x = hfun x i
inv (Iso≡Set hA hB f g hfun hinv i) x = hinv x i
sec (Iso≡Set hA hB f g hfun hinv i) x j =
  isSet→isSet' hB (sec f x) (sec g x) (λ i → hfun (hinv x i) i) refl i j
ret (Iso≡Set hA hB f g hfun hinv i) x j =
  isSet→isSet' hA (ret f x) (ret g x) (λ i → hinv (hfun x i) i) refl i j

transportIsoToPath : (f : Iso A B) (x : A) → transport (isoToPath f) x ≡ f .fun x
transportIsoToPath f x = transportRefl _

transportIsoToPath⁻ : (f : Iso A B) (x : B) → transport (sym (isoToPath f)) x ≡ f .inv x
transportIsoToPath⁻ f x = cong (f .inv) (transportRefl _)
