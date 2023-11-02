{-

Some theory about Bi-Invertible Equivalences

- BiInvEquiv to Iso
- BiInvEquiv to Equiv
- BiInvEquiv to HAEquiv
- Iso to BiInvEquiv
- Dependent version of these results

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.BiInvertible where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''
    P : A → Type ℓ''
    Q : B → Type ℓ'''


record BiInvEquiv {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor biInvEquiv
  field
    fun : A → B
    invr : B → A
    invr-rightInv : section fun invr
    invl : B → A
    invl-leftInv : retract fun invl

  invr≡invl : ∀ b → invr b ≡ invl b
  invr≡invl b =            invr b   ≡⟨ sym (invl-leftInv (invr b)) ⟩
                invl (fun (invr b)) ≡⟨ cong invl (invr-rightInv b) ⟩
                invl b              ∎

  invr-leftInv : retract fun invr
  invr-leftInv a = invr≡invl (fun a) ∙ (invl-leftInv a)

  invr≡invl-leftInv : ∀ a → PathP (λ j → invr≡invl (fun a) j ≡ a) (invr-leftInv a) (invl-leftInv a)
  invr≡invl-leftInv a j i = compPath-filler' (invr≡invl (fun a)) (invl-leftInv a) (~ j) i

  invl-rightInv : section fun invl
  invl-rightInv a = sym (cong fun (invr≡invl a)) ∙ (invr-rightInv a)

  invr≡invl-rightInv : ∀ a → PathP (λ j → fun (invr≡invl a j) ≡ a) (invr-rightInv a) (invl-rightInv a)
  invr≡invl-rightInv a j i = compPath-filler' (sym (cong fun (invr≡invl a))) (invr-rightInv a) j i


module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : BiInvEquiv A B) where
  open BiInvEquiv e

  biInvEquiv→Iso-right : Iso A B
  Iso.fun biInvEquiv→Iso-right      = fun
  Iso.inv biInvEquiv→Iso-right      = invr
  Iso.rightInv biInvEquiv→Iso-right = invr-rightInv
  Iso.leftInv biInvEquiv→Iso-right  = invr-leftInv

  biInvEquiv→Iso-left : Iso A B
  Iso.fun biInvEquiv→Iso-left      = fun
  Iso.inv biInvEquiv→Iso-left      = invl
  Iso.rightInv biInvEquiv→Iso-left = invl-rightInv
  Iso.leftInv biInvEquiv→Iso-left  = invl-leftInv

  biInvEquiv→Equiv-right biInvEquiv→Equiv-left : A ≃ B
  biInvEquiv→Equiv-right = fun , isoToIsEquiv biInvEquiv→Iso-right
  biInvEquiv→Equiv-left  = fun , isoToIsEquiv biInvEquiv→Iso-left

  -- since Iso.rightInv ends up getting modified during iso→HAEquiv, in some sense biInvEquiv→Iso-left
  --  is the most natural choice for forming a HAEquiv from a BiInvEquiv
  biInvEquiv→HAEquiv : HAEquiv A B
  biInvEquiv→HAEquiv = iso→HAEquiv biInvEquiv→Iso-left


module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (i : Iso A B) where
  open Iso i

  iso→BiInvEquiv : BiInvEquiv A B
  BiInvEquiv.fun iso→BiInvEquiv           = fun
  BiInvEquiv.invr iso→BiInvEquiv          = inv
  BiInvEquiv.invr-rightInv iso→BiInvEquiv = rightInv
  BiInvEquiv.invl iso→BiInvEquiv          = inv
  BiInvEquiv.invl-leftInv iso→BiInvEquiv  = leftInv


-- composition of bi-invertible maps

open BiInvEquiv

idBiInv : BiInvEquiv A A
idBiInv = biInvEquiv (λ a → a) _ (λ _ → refl) _ (λ _ → refl)

compBiInv : BiInvEquiv A B → BiInvEquiv B C → BiInvEquiv A C
compBiInv f g .fun  = g .fun ∘ f .fun
compBiInv f g .invr = f .invr ∘ g .invr
compBiInv f g .invr-rightInv b = cong (g .fun)  (f .invr-rightInv (g .invr b)) ∙ g .invr-rightInv b
compBiInv f g .invl = f .invl ∘ g .invl
compBiInv f g .invl-leftInv  a = cong (f .invl) (g .invl-leftInv (f .fun  a))  ∙ f .invl-leftInv  a

compBiInvIdL : (bi : BiInvEquiv A B) → compBiInv idBiInv bi ≡ bi
compBiInvIdL bi i .fun = bi .fun
compBiInvIdL bi i .invr = bi .invr
compBiInvIdL bi i .invr-rightInv b = lUnit (bi .invr-rightInv b) (~ i)
compBiInvIdL bi i .invl = bi .invl
compBiInvIdL bi i .invl-leftInv  a = rUnit (bi .invl-leftInv  a) (~ i)


-- dependent bi-invertible maps

record BiInvOver {ℓ ℓ'}
  {A : Type ℓ} {B : Type ℓ'}
  (bi : BiInvEquiv A B)
  (P : A → Type ℓ'') (Q : B → Type ℓ''')
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  no-eta-equality
  constructor biinvover
  field
    fun  : mapOver (bi .fun ) P Q
    invr : mapOver (bi .invr) Q P
    invr-rightInv : sectionOver (bi .invr-rightInv) fun invr
    invl : mapOver (bi .invl) Q P
    invl-leftInv  : retractOver (bi .invl-leftInv ) fun invl

record isBiInvOver {ℓ ℓ'}
  {A : Type ℓ} {B : Type ℓ'}
  (bi : BiInvEquiv A B)
  (P : A → Type ℓ'') (Q : B → Type ℓ''')
  (fun : mapOver (bi .fun) P Q)
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  no-eta-equality
  constructor isbiinvover
  field
    invr : mapOver (bi .invr) Q P
    invr-rightInv : sectionOver (bi .invr-rightInv) fun invr
    invl : mapOver (bi .invl) Q P
    invl-leftInv  : retractOver (bi .invl-leftInv ) fun invl

open BiInvOver
open isBiInvOver

isBiInvOver→BiInvOver :
  {bi : BiInvEquiv A B}
  {fun : mapOver (bi .fun) P Q}
  → isBiInvOver bi P Q fun
  → BiInvOver bi P Q
isBiInvOver→BiInvOver {fun = fun} bi .fun = fun
isBiInvOver→BiInvOver {fun = fun} bi .invr = bi .invr
isBiInvOver→BiInvOver {fun = fun} bi .invr-rightInv = bi .invr-rightInv
isBiInvOver→BiInvOver {fun = fun} bi .invl = bi .invl
isBiInvOver→BiInvOver {fun = fun} bi .invl-leftInv  = bi .invl-leftInv

BiInvOver→isBiInvOver :
  {bi : BiInvEquiv A B}
  → (bi' : BiInvOver bi P Q)
  → isBiInvOver bi P Q (bi' .fun)
BiInvOver→isBiInvOver bi .invr = bi .invr
BiInvOver→isBiInvOver bi .invr-rightInv = bi .invr-rightInv
BiInvOver→isBiInvOver bi .invl = bi .invl
BiInvOver→isBiInvOver bi .invl-leftInv  = bi .invl-leftInv


-- composition of dependent bi-invertible maps

compBiInvOver :
  {ℓA ℓB ℓC ℓP ℓQ ℓR : Level}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  {P : A → Type ℓP} {Q : B → Type ℓQ} {R : C → Type ℓR}
  {bi₁ : BiInvEquiv A B} {bi₂ : BiInvEquiv B C}
  → BiInvOver bi₁ P Q → BiInvOver bi₂ Q R
  → BiInvOver (compBiInv bi₁ bi₂) P R
compBiInvOver {A = A} {B} {C} {P} {Q} {R} {bi₁} {bi₂} bi₁' bi₂' = w
  where
  w : BiInvOver _ _ _
  w .fun _ = bi₂' .fun _ ∘ bi₁' .fun _
  w .invl _ = bi₁' .invl _ ∘ bi₂' .invl _
  w .invr-rightInv b q i =
    comp
    (λ j → R (compPath-filler (cong (bi₂ .fun) (bi₁ .invr-rightInv _)) (bi₂ .invr-rightInv b) j i))
    (λ j → λ
      { (i = i0) → w .fun _ (w .invr _ q)
      ; (i = i1) → bi₂' .invr-rightInv _ q j })
    (bi₂' .fun _ (bi₁' .invr-rightInv _ (bi₂' .invr _ q) i))
  w .invr _ = bi₁' .invr _ ∘ bi₂' .invr _
  w .invl-leftInv a p i =
    comp
    (λ j → P (compPath-filler (cong (bi₁ .invl) (bi₂ .invl-leftInv _)) (bi₁ .invl-leftInv a) j i))
    (λ j → λ
      { (i = i0) → w .invl _ (w .fun _ p)
      ; (i = i1) → bi₁' .invl-leftInv _ p j })
    (bi₁' .invl _ (bi₂' .invl-leftInv _ (bi₁' .fun _ p) i))


-- construct dependent bi-invertible maps from equivalences

fiberBiInv→BiInvOver :
  {ℓA ℓP ℓQ : Level}
  {A : Type ℓA}
  {P : A → Type ℓP} {Q : A → Type ℓQ}
  → ((a : A) → BiInvEquiv (P a) (Q a))
  → BiInvOver idBiInv P Q
fiberBiInv→BiInvOver bi .fun a  = bi a .fun
fiberBiInv→BiInvOver bi .invr a = bi a .invr
fiberBiInv→BiInvOver bi .invr-rightInv a = bi a .invr-rightInv
fiberBiInv→BiInvOver bi .invl a = bi a .invl
fiberBiInv→BiInvOver bi .invl-leftInv  a = bi a .invl-leftInv

pullbackBiInvOver :
  {ℓA ℓB ℓP : Level}
  {A : Type ℓA}{B : Type ℓB}
  {P : B → Type ℓP}
  (bi : BiInvEquiv A B)
  → BiInvOver bi (P ∘ bi .fun) P
pullbackBiInvOver {A = A} {B} {P} bi = w
  where
  u : IsoOver _ _ P
  u = pullbackIsoOver (bi .fun) (biInvEquiv→HAEquiv bi .snd)

  open IsoOver

  w : BiInvOver _ _ _
  w .fun  a = idfun _
  w .invr b = subst P (sym (bi .invr-rightInv b))
  w .invr-rightInv b p i = subst-filler P (sym (bi .invr-rightInv b)) p (~ i)
  w .invl = u .inv
  w .invl-leftInv = u .leftInv


-- Since there is no regularity for transport (also no-eta-equality),
-- we have to fix one field manually to make it invariant under transportation.
liftBiInv :
  (bi : BiInvEquiv A B)
  → ((a : A) → BiInvEquiv (P a) (Q (bi .fun a)))
  → BiInvOver bi P Q
liftBiInv {P = P} {Q = Q} bi bi' =
  isBiInvOver→BiInvOver
    (transport (λ i → isBiInvOver (compBiInvIdL bi i) P Q (λ a x → bi' a .fun x))
      (BiInvOver→isBiInvOver (compBiInvOver (fiberBiInv→BiInvOver bi') (pullbackBiInvOver bi))))


equivOver→BiInvOver :
  (bi : BiInvEquiv A B)
  (f : mapOver (bi .fun) P Q)
  → isEquivOver {P = P} {Q = Q} f
  → BiInvOver bi P Q
equivOver→BiInvOver {P = P} {Q = Q} bi f equiv = w
  where
  bi' = liftBiInv {Q = Q} bi (λ a → iso→BiInvEquiv (equivToIso (_ , equiv a)))

  -- no-eta-equality for Iso, so we have to fill in fields manually
  w : BiInvOver bi P Q
  w .fun  = bi' .fun
  w .invr = bi' .invr
  w .invr-rightInv = bi' .invr-rightInv
  w .invl = bi' .invl
  w .invl-leftInv  = bi' .invl-leftInv
