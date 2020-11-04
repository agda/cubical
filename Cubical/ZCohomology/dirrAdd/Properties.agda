{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.dirrAdd.Properties where

open import Cubical.ZCohomology.Base
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to path-assoc)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_)
open import Cubical.Data.Nat hiding (+-comm ; +-assoc)
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3 ; map2 to trMap2)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup

open import Cubical.ZCohomology.KcompPrelims

open Iso renaming (inv to inv')
open GroupStr renaming (_+_ to comp ; _-_ to subtr)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    A' : Pointed ℓ

infixr 34 _+ₖ_
infixr 34 _+ₕ_

-- Some important lemmas concerning connectedness
is2ConnectedKn : (n : ℕ) → isConnected 2 (coHomK (suc n))
is2ConnectedKn zero = ∣ ∣ base ∣ ∣
                    , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                        (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
                          (toPropElim (λ _ → isOfHLevelTrunc 2 _ _) refl))
is2ConnectedKn (suc n) = ∣ ∣ north ∣ ∣
                       , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                           (trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isOfHLevelTrunc 2 _ _))
                             (suspToPropElim (ptSn (suc n)) (λ _ → isOfHLevelTrunc 2 _ _) refl))

isConnectedKn : (n : ℕ) → isConnected (2 + n) (coHomK (suc n))
isConnectedKn n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (2 + n) 1)) (sphereConnected (suc n))

-- The following lemmas are frequently used for truncation elimination
private
  wedgeConHLev : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (coHomK (2 + n))
  wedgeConHLev n = subst (λ x → isOfHLevel x (coHomK (2 + n)))
                         (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                         (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (4 + n)))
  wedgeConHLev' : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (typ (Ω (coHomK-ptd (3 + n))))
  wedgeConHLev' n = subst (λ x → isOfHLevel x (typ (Ω (coHomK-ptd (3 + n)))))
                          (sym (+-suc (2 + n) (suc n) ∙ +-suc (3 + n) n))
                          (isOfHLevelPlus' {n = n} (4 + n) (isOfHLevelTrunc (5 + n) _ _))

-- Addition in the Eilenberg-Maclane spaces is uniquely determined if we require it to have left- and right-unit laws,
-- such that these agree on 0. In particular, any h-structure (see http://ericfinster.github.io/files/emhott.pdf) is unique.
genAddId : (n : ℕ) → (comp1 comp2 : coHomK (suc n) → coHomK (suc n) → coHomK (suc n))
         → (rUnit1 : (x : _) → comp1 x (coHom-pt (suc n)) ≡ x)
         → (lUnit1 : (x : _) → comp1 (coHom-pt (suc n)) x ≡ x)
         → (rUnit2 : (x : _) → comp2 x (coHom-pt (suc n)) ≡ x)
         → (lUnit2 : (x : _) → comp2 (coHom-pt (suc n)) x ≡ x)
         → (unId1 : rUnit1 (coHom-pt (suc n)) ≡ lUnit1 (coHom-pt (suc n)))
         → (unId2 : rUnit2 (coHom-pt (suc n)) ≡ lUnit2 (coHom-pt (suc n)))
         → (x y : _) → comp1 x y ≡ comp2 x y
genAddId n comp1 comp2 rUnit1 lUnit1 rUnit2 lUnit2 unId1 unId2 =
  elim2 (λ _ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
        (wedgeConSn _ _
        (λ _ _ → help _ _)
        (λ x → lUnit1 ∣ x ∣ ∙ sym (lUnit2 ∣ x ∣))
        (λ x → rUnit1 ∣ x ∣ ∙ sym (rUnit2 ∣ x ∣))
        (cong₂ (_∙_) unId1 (cong sym unId2)) .fst)
  where
  help : isOfHLevel (2 + (n + suc n)) (coHomK (suc n))
  help = subst (λ x → isOfHLevel x (coHomK (suc n))) (+-suc n (2 + n) ∙ +-suc (suc n) (suc n))
               (isOfHLevelPlus n (isOfHLevelTrunc (3 + n)))

-- Induction principles for cohomology groups
-- If we want to show a proposition about some x : Hⁿ(A), it suffices to show it under the
-- assumption that x = ∣f∣₂ and that f is pointed
coHomPointedElim : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → Type ℓ'}
                 → ((x : coHom (suc n) A) → isProp (B x))
                 → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
                 → (x : coHom (suc n) A) → B x
coHomPointedElim {ℓ' = ℓ'} {A = A} n a isprop indp =
  sElim (λ _ → isOfHLevelSuc 1 (isprop _))
         λ f → helper n isprop indp f (f a) refl
  where
  helper :  (n : ℕ) {B : coHom (suc n) A → Type ℓ'}
         → ((x : coHom (suc n) A) → isProp (B x))
         → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
         → (f : A → coHomK (suc n))
         → (x : coHomK (suc n))
         → f a ≡ x → B ∣ f ∣₂
  -- pattern matching a bit extra to avoid isOfHLevelPlus'
  helper zero isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ λ _ → isprop _))
           (toPropElim (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc zero) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ λ _ → isprop _))
           (suspToPropElim base (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc zero)) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc (suc n))) isprop ind f =
    trElim (λ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))

coHomPointedElim2 : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (x y : coHom (suc n) A) → B x y
coHomPointedElim2 {ℓ' = ℓ'} {A = A} n a isprop indp = sElim2 (λ _ _ → isOfHLevelSuc 1 (isprop _ _))
                                                   λ f g → helper n a isprop indp f g (f a) (g a) refl refl
  where
  helper : (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (f g : A → coHomK (suc n))
                 → (x y : coHomK (suc n))
                 → f a ≡ x → g a ≡ y
                 → B ∣ f ∣₂ ∣ g ∣₂
  helper zero a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ2 λ _ _ → isprop _ _))
          (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc zero) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 base (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc zero)) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc (suc n))) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))


{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                  (A : Type ℓ) →
                  (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₂
  module coHomRed+1 where
  helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
  helpLemma {C = C} = isoToPath (iso map1
                                     map2
                                     (λ b → linvPf b)
                                     (λ _  → refl))
    where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
    map1 f = map1' , refl
      module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)

    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
      where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
      helper (inl x) = refl
      helper (inr tt) = sym snd
coHomRed+1Equiv (suc zero) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK 1 , ∣ base ∣)} i ∥₂
coHomRed+1Equiv (suc (suc n)) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK (2 + n) , ∣ north ∣)} i ∥₂

-----------

Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

---------- Algebra/Group stuff --------

0ₖ : (n : ℕ) → coHomK n
0ₖ = coHom-pt

-- addition for n ≥ 2 (with additional paths from wedgeConSn)
preAdd : (n : ℕ) → Σ[ f ∈ (S₊ (2 + n) → S₊ (2 + n) → coHomK (2 + n)) ] _
preAdd n =
  wedgeConSn _ _
             (λ _ _ → wedgeConHLev n)
             ∣_∣
             ∣_∣
             refl

-- addition for n = 1
wedgeMapS¹ : S¹ → S¹ → S¹
wedgeMapS¹ base y = y
wedgeMapS¹ (loop i) base = loop i
wedgeMapS¹ (loop i) (loop j) =
  hcomp (λ k → λ { (i = i0) → loop j
                  ; (i = i1) → loop (j ∧ k)
                  ; (j = i0) → loop i
                  ; (j = i1) → loop (i ∧ k)})
        (loop (i ∨ j))

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = sym (rUnit refl)
Kn→ΩKn+10ₖ (suc zero) i j = ∣ (rCancel (merid base) i j) ∣
Kn→ΩKn+10ₖ (suc (suc n)) i j = ∣ (rCancel (merid north) i j) ∣

_+ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_+ₖ_ {n = zero} x y = x ℤ+ y
_+ₖ_ {n = suc zero} = trMap2 wedgeMapS¹
_+ₖ_ {n = suc (suc n)} = trRec (isOfHLevelΠ (4 + n) λ _ → isOfHLevelTrunc (4 + n))
                            λ x → trRec (isOfHLevelTrunc (4 + n)) λ y → preAdd n .fst x y

isEquiv+ : (n : ℕ) → (x : coHomK (suc n)) → isEquiv (_+ₖ_ {n = (suc n)} x)
isEquiv+ zero =
  trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropIsEquiv _))
         (toPropElim (λ _ → isPropIsEquiv _)
                     (subst isEquiv (sym help) (idIsEquiv _)))
  where
  help : _+ₖ_ {n = 1} (coHom-pt 1) ≡ idfun _
  help = funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
                λ _ → refl)
isEquiv+ (suc n) =
  trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropIsEquiv _))
         (suspToPropElim (ptSn (suc n)) (λ _ → isPropIsEquiv _)
         (subst isEquiv (sym help) (idIsEquiv _)))
  where
  help : _+ₖ_ {n = (2 + n)} (coHom-pt (2 + n)) ≡ idfun _
  help = funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _) λ _ → refl)

Kₙ≃Kₙ : (n : ℕ) (x : coHomK (suc n)) → coHomK (suc n) ≃ coHomK (suc n)
Kₙ≃Kₙ n x = _ , isEquiv+ n x

-ₖ_ : {n : ℕ} →  coHomK n → coHomK n
-ₖ_ {n = zero} x = 0 - x
-ₖ_ {n = suc n} x = invEq (Kₙ≃Kₙ n x) (coHom-pt (suc n))

_-ₖ_ : {n : ℕ} → coHomK n → coHomK n → coHomK n
_-ₖ_ {n = n} x y = _+ₖ_ {n = n} x (-ₖ_ {n = n} y)

+ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
+ₖ-syntax n = _+ₖ_ {n = n}

-ₖ-syntax : (n : ℕ) → coHomK n → coHomK n
-ₖ-syntax n = -ₖ_ {n = n}

-'ₖ-syntax : (n : ℕ) → coHomK n → coHomK n → coHomK n
-'ₖ-syntax n = _-ₖ_ {n = n}

syntax +ₖ-syntax n x y = x +[ n ]ₖ y
syntax -ₖ-syntax n x = -[ n ]ₖ x
syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

commₖ : (n : ℕ) → (x y : coHomK n) → x +[ n ]ₖ y ≡ y +[ n ]ₖ x
commₖ zero = +-comm
commₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _
          (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ {base → refl ; (loop i) j → ∣ loop i ∣})
          (λ {base → refl ; (loop i) j → ∣ loop i ∣})
          refl .fst)
commₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _
                    (λ x y → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                    (λ x → preAdd n .snd .fst x ∙ sym (preAdd n .snd .snd x))
                    (λ x → preAdd n .snd .snd x ∙ sym (preAdd n .snd .fst x))
                    refl
                    .fst)

rCancelₖ : (n : ℕ) → (x : coHomK n) → x -[ n ]ₖ x ≡ coHom-pt n
rCancelₖ zero x = +-comm x (pos 0 - x) ∙ minusPlus x 0
rCancelₖ (suc n) x = retEq (Kₙ≃Kₙ n x) (coHom-pt _)

lCancelₖ : (n : ℕ) → (x : coHomK n) → (-[ n ]ₖ x) +[ n ]ₖ x ≡ coHom-pt n
lCancelₖ zero x = minusPlus x 0
lCancelₖ (suc n) x = commₖ (suc n) _ _ ∙ rCancelₖ (suc n) x

rUnitₖ : (n : ℕ) → (x : coHomK n) → x +[ n ]ₖ coHom-pt n ≡ x 
rUnitₖ zero x = refl
rUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
rUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → preAdd n .snd .snd x

lUnitₖ : (n : ℕ) → (x : coHomK n) → coHom-pt n +[ n ]ₖ x ≡ x 
lUnitₖ zero x = sym (pos0+ x) 
lUnitₖ (suc zero) =
  trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
         λ {base → refl
         ; (loop i) → refl}
lUnitₖ (suc (suc n)) =
  trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → refl

lUnitₖ'≡rUnitₖ' : (n : ℕ) → lUnitₖ n (coHom-pt n) ≡ rUnitₖ n (coHom-pt n)
lUnitₖ'≡rUnitₖ' zero = isSetInt _ _ _ _
lUnitₖ'≡rUnitₖ' (suc zero) = refl
lUnitₖ'≡rUnitₖ' (suc (suc n)) = refl

assocₖ : (n : ℕ) → (x y z : coHomK n) → x +[ n ]ₖ (y +[ n ]ₖ z) ≡ (x +[ n ]ₖ y) +[ n ]ₖ z
assocₖ zero = +-assoc
assocₖ (suc zero) =
  trElim3 (λ _ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
          λ x → wedgeConSn _ _
                (λ _ _ → isOfHLevelTrunc 3 _ _)
                (λ y i → rUnitₖ 1 ∣ x ∣ (~ i) +ₖ ∣ y ∣)
                (λ z → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ z ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ z ∣)))
                (tihi x) .fst
  where
  tihi : (x : S¹) → cong (∣ x ∣ +ₖ_) (rUnitₖ 1 ∣ base ∣) ∙ sym (rUnitₖ 1 (∣ x ∣ +ₖ ∣ base ∣)) ≡ (cong (_+ₖ ∣ base ∣) (sym (rUnitₖ 1 ∣ x ∣)))
  tihi = toPropElim (λ _ → isOfHLevelTrunc 3 _ _ _ _)
                    (sym (lUnit refl))
assocₖ (suc (suc n)) = 
  trElim3 (λ _ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
          λ x → wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                           (λ z i → preAdd n .snd .snd x (~ i) +ₖ ∣ z ∣)
                           (λ y → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ y ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ y ∣)))
                           (tihi x) .fst
  where
  tihi : (x : S₊ (2 + n)) → cong (∣ x ∣ +ₖ_) (rUnitₖ (2 + n) ∣ north ∣) ∙ sym (rUnitₖ (2 + n) (∣ x ∣ +ₖ ∣ north ∣))
                          ≡ cong (_+ₖ ∣ north ∣) (sym (preAdd n .snd .snd x))
  tihi = sphereElim (suc n) (λ _ → isOfHLevelTrunc (4 + n) _ _ _ _)
                            (sym (lUnit (sym (rUnitₖ (2 + n) (∣ north ∣ +ₖ ∣ north ∣)))))

private
  tooThick4hcomps : ∀ {ℓ} {A : Type ℓ} {a : A} (p : a ≡ a) (r : refl ≡ p)
                 → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r
  tooThick4hcomps p = J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

Kn→ΩKn+1-hom : (n : ℕ) (x y : coHomK n) → Kn→ΩKn+1 n (x +[ n ]ₖ y) ≡ Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y
Kn→ΩKn+1-hom zero x y = (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop (x ℤ+ y) i ∣)) (~ j))
                      ∙∙ (λ j i → ∣ intLoop-hom x y (~ j) i ∣)
                      ∙∙ (congFunct ∣_∣ (intLoop x) (intLoop y)
                        ∙ cong₂ _∙_ (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop x i ∣)) j)
                                     λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i) (inS (∣ intLoop y i ∣)) j)
Kn→ΩKn+1-hom (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
        (wedgeConSn _ _
                    (λ _ _ → isOfHLevelTrunc 4 _ _ _ _ )
                    (λ x → lUnit _ ∙ cong (_∙ Kn→ΩKn+1 1 ∣ x ∣) (sym (Kn→ΩKn+10ₖ 1)))
                    (λ x → cong (Kn→ΩKn+1 1) (rUnitₖ 1 ∣ x ∣) ∙∙ rUnit _ ∙∙ cong (Kn→ΩKn+1 1 ∣ x ∣ ∙_) (sym (Kn→ΩKn+10ₖ 1)))
                    (sym (tooThick4hcomps (Kn→ΩKn+1 1 ∣ base ∣) (sym (Kn→ΩKn+10ₖ 1)))) .fst)
Kn→ΩKn+1-hom (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
                        (λ x → lUnit _ ∙ cong (_∙ Kn→ΩKn+1 (suc (suc n)) ∣ x ∣) (sym (Kn→ΩKn+10ₖ (2 + n))))
                        (λ y → cong (Kn→ΩKn+1 (suc (suc n))) (preAdd n .snd .snd y) ∙∙ rUnit _ ∙∙ cong (Kn→ΩKn+1 (suc (suc n)) ∣ y ∣ ∙_) (sym (Kn→ΩKn+10ₖ (2 + n))))
                        (sym (tooThick4hcomps (Kn→ΩKn+1 (suc (suc n)) ∣ north ∣) (sym (Kn→ΩKn+10ₖ (2 + n))))) .fst)

ΩKn+1→Kn-hom : (n : ℕ) (x y : typ (Ω (coHomK-ptd (suc n)))) → ΩKn+1→Kn n (x ∙ y) ≡ ΩKn+1→Kn n x +[ n ]ₖ (ΩKn+1→Kn n y)
ΩKn+1→Kn-hom zero x y =
    (λ i → winding (congFunct (trRec isGroupoidS¹ (λ a → a)) x y i))
  ∙ winding-hom (cong (trRec isGroupoidS¹ (λ a → a)) x) (cong (trRec isGroupoidS¹ (λ a → a)) y)
ΩKn+1→Kn-hom (suc n) x y =
  let
  xId = rightInv (Iso-Kn-ΩKn+1 (1 + n)) x
  yId = rightInv (Iso-Kn-ΩKn+1 (1 + n)) y
  in   cong₂ (λ x y → ΩKn+1→Kn (1 + n) (x ∙ y)) (sym xId) (sym yId)
    ∙∙ cong (ΩKn+1→Kn (1 + n)) (sym (Kn→ΩKn+1-hom (suc n) (ΩKn+1→Kn (1 + n) x) (ΩKn+1→Kn (1 + n) y)))
    ∙∙ leftInv (Iso-Kn-ΩKn+1 (1 + n)) (ΩKn+1→Kn (1 + n) x +ₖ ΩKn+1→Kn (1 + n) y)

ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
ΩKn+1→Kn-refl zero = refl
ΩKn+1→Kn-refl (suc zero) = refl
ΩKn+1→Kn-refl (suc (suc zero)) = refl
ΩKn+1→Kn-refl (suc (suc (suc zero))) = refl
ΩKn+1→Kn-refl (suc (suc (suc (suc zero)))) = refl
ΩKn+1→Kn-refl (suc (suc (suc (suc (suc n))))) = refl

-0ₖ : {n : ℕ} → -[ n ]ₖ (0ₖ n) ≡ (0ₖ n)
-0ₖ {n = zero} = refl
-0ₖ {n = suc zero} = refl
-0ₖ {n = suc (suc n)} = refl

isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p



abstract
  isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A → isOfHLevel (suc n) (typ A) → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
  isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
      ((λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
   ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
   ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
   ∙∙ (λ i j → (Iso.leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

  isCommΩK1 : (n : ℕ) → isComm∙ ((Ω^ n) (coHomK-ptd 1))
  isCommΩK1 zero = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK1 (suc n) = Eckmann-Hilton n

  open Iso renaming (inv to inv')
  ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , Iso.fun e (pt A))
  ptdIso→comm {A = (A , a)} {B = B} e comm p q =
         sym (rightInv (congIso e) (p ∙ q))
      ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                              ∙∙ (comm (inv' (congIso e) p) (inv' (congIso e) q))
                              ∙∙ (sym (invCongFunct e q p))))
      ∙∙ rightInv (congIso e) (q ∙ p)

  isCommΩK : (n : ℕ) → isComm∙ (coHomK-ptd n)
  isCommΩK zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
  isCommΩK (suc zero) = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
  isCommΩK (suc (suc n)) = subst isComm∙ (λ i → coHomK (2 + n) , ΩKn+1→Kn-refl (2 + n) i) (ptdIso→comm {A = (_ , _)} (invIso (Iso-Kn-ΩKn+1 (2 + n))) (Eckmann-Hilton 0))

-- alternative proof
isCommΩK' : (n : ℕ) → isComm∙ (coHomK-ptd n)
isCommΩK' zero p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK' (suc zero) = isCommA→isCommTrunc 2 comm-ΩS¹ isGroupoidS¹
isCommΩK' (suc (suc n)) =
  WedgeConnectivity.extension
    (suc n) (suc n)
    (_ , refl) (isConnectedPath (2 + n) (isConnectedKn (1 + n)) _ _)
    (_ , refl) (isConnectedPath (2 + n) (isConnectedKn (1 + n)) _ _)
    (λ p q → _ , subst (λ x → isOfHLevel x (p ∙ q ≡ q ∙ p)) (+-suc n (suc n))
                        (isOfHLevelPlus n (isOfHLevelTrunc (4 + n) _ _ _ _)))
    (λ p → sym (rUnit p) ∙ lUnit p)
    (λ p → sym (lUnit p) ∙ rUnit p)
    refl

-distrₖ : (n : ℕ) (x y : coHomK n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
-distrₖ zero x y = GroupLemmas.invDistr intGroup x y ∙ +-comm (0 - y) (0 - x)
-distrₖ (suc zero) =
  elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelTrunc 3 _ _)
          (λ x → sym (lUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (λ x → cong (λ x → -[ 1 ]ₖ x) (rUnitₖ 1 ∣ x ∣) ∙ sym (rUnitₖ 1 (-[ 1 ]ₖ ∣ x ∣)))
          (sym (rUnit refl)) .fst)
-distrₖ (suc (suc n)) =
  elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
        (wedgeConSn _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev n) _ _)
                        (λ x → sym (lUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (λ x → cong (λ x → -[ (2 + n) ]ₖ x) (rUnitₖ (2 + n) ∣ x ∣ ) ∙ sym (rUnitₖ (2 + n) (-[ (2 + n) ]ₖ ∣ x ∣)))
                        (sym (rUnit refl)) .fst)

---- Group structure of cohomology groups ---

_+ₕ_ : {n : ℕ} → coHom n A → coHom n A → coHom n A
_+ₕ_ {n = n} = sRec2 § λ a b → ∣ (λ x → a x +[ n ]ₖ b x) ∣₂

-ₕ_  : {n : ℕ} → coHom n A → coHom n A
-ₕ_  {n = n} = sRec § λ a → ∣ (λ x → -[ n ]ₖ a x) ∣₂

_-ₕ_  : {n : ℕ} → coHom n A → coHom n A → coHom n A
_-ₕ_  {n = n} x y = _+ₕ_ {n = n} x (-ₕ_ {n = n} y)

+ₕ-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
+ₕ-syntax n = _+ₕ_ {n = n}

-ₕ-syntax : (n : ℕ) → coHom n A → coHom n A
-ₕ-syntax n = -ₕ_ {n = n}

-ₕ'-syntax : (n : ℕ) → coHom n A → coHom n A → coHom n A
-ₕ'-syntax n = _-ₕ_ {n = n}

syntax +ₕ-syntax n x y = x +[ n ]ₕ y
syntax -ₕ-syntax n x = -[ n ]ₕ x
syntax -ₕ'-syntax n x y = x -[ n ]ₕ y

0ₕ : (n : ℕ) → coHom n A
0ₕ n = ∣ (λ _ → (0ₖ n)) ∣₂

rUnitₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (0ₕ n) ≡ x
rUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                λ a i → ∣ funExt (λ x → rUnitₖ n (a x)) i ∣₂

lUnitₕ : (n : ℕ) (x : coHom n A) → (0ₕ n) +[ n ]ₕ x ≡ x
lUnitₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                  λ a i → ∣ funExt (λ x → lUnitₖ n (a x)) i ∣₂

rCancelₕ : (n : ℕ) (x : coHom n A) → x +[ n ]ₕ (-[ n ]ₕ x) ≡ 0ₕ n
rCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → rCancelₖ n (a x)) i ∣₂

lCancelₕ : (n : ℕ) (x : coHom n A) → (-[ n ]ₕ x) +[ n ]ₕ x  ≡ 0ₕ n
lCancelₕ n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
                 λ a i → ∣ funExt (λ x → lCancelₖ n (a x)) i ∣₂

assocₕ : (n : ℕ) (x y z : coHom n A) → ((x +[ n ]ₕ y) +[ n ]ₕ z) ≡ (x +[ n ]ₕ (y +[ n ]ₕ z))
assocₕ n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
               λ a b c i → ∣ funExt (λ x → assocₖ n (a x) (b x) (c x)) (~ i) ∣₂

commₕ : (n : ℕ) (x y : coHom n A) → (x +[ n ]ₕ y) ≡ (y +[ n ]ₕ x)
commₕ n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
                        λ a b i → ∣ funExt (λ x → commₖ n (a x) (b x)) i ∣₂

-ₖ-ₖ : (n : ℕ) (x : coHomK n) → (-[ n ]ₖ (-[ n ]ₖ x)) ≡ x
-ₖ-ₖ n x = (sym (lUnitₖ n (-[ n ]ₖ (-[ n ]ₖ x))) ∙∙ cong (λ y → y +[ n ]ₖ (-[ n ]ₖ (-[ n ]ₖ x))) (sym (rCancelₖ n x)) ∙∙ sym (assocₖ n _ _ _))
              ∙∙ cong (λ y → (x +[ n ]ₖ y)) help
              ∙∙ (assocₖ n _ _ _ ∙∙ cong (λ y → y +[ n ]ₖ x) (rCancelₖ n x) ∙∙ lUnitₖ n x)
  where
  help : ((-[ n ]ₖ x) -[ n ]ₖ (-[ n ]ₖ x)) ≡ ((-[ n ]ₖ x) +[ n ]ₖ x)
  help = rCancelₖ n (-[ n ]ₖ x) ∙ sym (lCancelₖ n x)

-- Proof that rUnitₖ and lUnitₖ agree on 0ₖ. Needed for Mayer-Vietoris.
{-
private
  rUnitlUnitGen : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {b : B} (e : Iso A (b ≡ b))
                  (0A : A)
                  (0fun : fun e 0A ≡ refl)
                → Path (inv' e (fun e 0A ∙ fun e 0A) ≡ 0A)
                       (cong (inv' e) (cong (_∙ fun e 0A) 0fun) ∙∙ cong (inv' e) (sym (lUnit (fun e 0A))) ∙∙ Iso.leftInv e 0A)
                       (cong (inv' e) (cong (fun e 0A ∙_) 0fun) ∙∙ cong (inv' e) (sym (rUnit (fun e 0A))) ∙∙ Iso.leftInv e 0A)
  rUnitlUnitGen e 0A 0fun =
      (λ i → cong (inv' e) (cong (_∙ fun e 0A) 0fun) ∙∙ rUnit (cong (inv' e) (sym (lUnit (fun e 0A)))) i ∙∙ Iso.leftInv e 0A)
    ∙ ((λ i → (λ j → inv' e (0fun (~ i ∧ j) ∙ 0fun (j ∧ i)))
            ∙∙ ((λ j → inv' e (0fun (~ i ∨ j) ∙ 0fun i))
            ∙∙ cong (inv' e) (sym (lUnit (0fun i)))
            ∙∙ λ j → inv' e (0fun (i ∧ (~ j))))
            ∙∙ Iso.leftInv e 0A)
    ∙∙ (λ i → (λ j → inv' e (fun e 0A ∙ 0fun j))
            ∙∙ (λ j → inv' e (0fun (j ∧ ~ i) ∙ refl))
            ∙∙ cong (inv' e) (sym (rUnit (0fun (~ i))))
            ∙∙ (λ j → inv' e (0fun (~ i ∧ ~ j)))
            ∙∙ Iso.leftInv e 0A)
    ∙∙ λ i → cong (inv' e) (cong (fun e 0A ∙_) 0fun)
           ∙∙ rUnit (cong (inv' e) (sym (rUnit (fun e 0A)))) (~ i)
           ∙∙ Iso.leftInv e 0A)

rUnitlUnit0 : (n : ℕ) → rUnitₖ n (0ₖ n) ≡ lUnitₖ n (0ₖ n)
rUnitlUnit0 0 = refl
rUnitlUnit0 (suc zero) = refl
rUnitlUnit0 (suc (suc n)) = sym (rUnitlUnitGen (Iso-Kn-ΩKn+1 (2 + n)) (0ₖ (2 + n)) (Kn→ΩKn+10ₖ (2 + n)))
-}

-- Group structure of reduced cohomology groups (in progress - might need K to compute properly first) ---

+ₕ∙ : {A : Pointed ℓ} (n : ℕ) → coHomRed n A → coHomRed n A → coHomRed n A
+ₕ∙ zero = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ zero ]ₖ b x) , (λ i → (pa i +[ zero ]ₖ pb i)) ∣₂ }
+ₕ∙ (suc zero) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ 1 ]ₖ b x) , (λ i → pa i +[ 1 ]ₖ pb i) ∙ lUnitₖ 1 (0ₖ 1) ∣₂ }
+ₕ∙ (suc (suc n)) = sRec2 § λ { (a , pa) (b , pb) → ∣ (λ x → a x +[ (2 + n) ]ₖ b x) , (λ i → pa i +[ (2 + n) ]ₖ pb i) ∙ lUnitₖ (2 + n) (0ₖ (2 + n)) ∣₂ }

open IsSemigroup
open IsMonoid
open GroupStr
open GroupHom

coHomGr : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Group {ℓ}
coHomGr n A = coHom n A , coHomGrnA
  where
  coHomGrnA : GroupStr (coHom n A)
  0g coHomGrnA = 0ₕ n
  GroupStr._+_ coHomGrnA = λ x y → x +[ n ]ₕ y
  - coHomGrnA = λ x → -[ n ]ₕ x
  isGroup coHomGrnA = helper
    where
    abstract
      helper : IsGroup (0ₕ n) (λ x y → x +[ n ]ₕ y) (λ x → -[ n ]ₕ x)
      helper = makeIsGroup § (λ x y z → sym (assocₕ n x y z)) (rUnitₕ n) (lUnitₕ n) (rCancelₕ n) (lCancelₕ n)

×coHomGr : (n : ℕ) (A : Type ℓ) (B : Type ℓ') → Group
×coHomGr n A B = dirProd (coHomGr n A) (coHomGr n B)

coHomFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : ℕ) (f : A → B) → coHom n B → coHom n A
coHomFun n f = sRec § λ β → ∣ β ∘ f ∣₂

-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma n m f' x y =
    isHom f' x (-[ n ]ₕ y)
  ∙ cong (λ y → (fun f' x) +[ m ]ₕ y) (morphMinus _ _ f' y)

--- the loopspace of Kₙ is commutative regardless of base

addIso : (n : ℕ) (x : coHomK n) → Iso (coHomK n) (coHomK n)
fun (addIso n x) y = y +[ n ]ₖ x
inv' (addIso n x) y = y -[ n ]ₖ x
rightInv (addIso n x) y = sym (assocₖ n _ _ _) ∙∙ cong (λ x → y +[ n ]ₖ x) (lCancelₖ n x) ∙∙ rUnitₖ n y
leftInv (addIso n x) y = sym (assocₖ n _ _ _) ∙∙ cong (λ x → y +[ n ]ₖ x) (rCancelₖ n x) ∙∙ rUnitₖ n y

isCommΩK-based : (n : ℕ) (x : coHomK n) → isComm∙ (coHomK n , x)
isCommΩK-based zero x p q = isSetInt _ _ (p ∙ q) (q ∙ p)
isCommΩK-based (suc zero) x =
  subst isComm∙ (λ i → coHomK 1 , lUnitₖ 1 x i)
                (ptdIso→comm {A = (_ , 0ₖ 1)} (addIso 1 x)
                              (isCommΩK 1))
isCommΩK-based (suc (suc n)) x =
  subst isComm∙ (λ i → coHomK (suc (suc n)) , lUnitₖ (suc (suc n)) x i)
                (ptdIso→comm {A = (_ , 0ₖ (suc (suc n)))} (addIso (suc (suc n)) x)
                              (isCommΩK (suc (suc n))))

-- ---
-- -- hidden versions of cohom stuff using the "lock" hack. The locked versions can be used when proving things.
-- -- Swapping "key" for "tt*" will then give computing functions.

-- Unit' : Type₀
-- Unit' = lockUnit {ℓ-zero}

-- lock : ∀ {ℓ} {A : Type ℓ} → Unit' → A → A
-- lock unlock = λ x → x

-- module lockedCohom (key : Unit') where
--   +K : (n : ℕ) → coHomK n → coHomK n → coHomK n
--   +K n = lock key (_+ₖ_ {n = n})

--   -K : (n : ℕ) → coHomK n → coHomK n
--   -K n = lock key (-ₖ_ {n = n})

--   -Kbin : (n : ℕ) → coHomK n → coHomK n → coHomK n
--   -Kbin n = lock key (_-ₖ_ {n = n})

--   rUnitK : (n : ℕ) (x : coHomK n) → +K n x (0ₖ n) ≡ x
--   rUnitK n x = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (0ₖ n) ≡ x
--     pm unlock = rUnitₖ n x

--   lUnitK : (n : ℕ) (x : coHomK n) → +K n (0ₖ n) x ≡ x
--   lUnitK n x = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (0ₖ n) x ≡ x
--     pm unlock = lUnitₖ n x

--   rCancelK : (n : ℕ) (x : coHomK n) → +K n x (-K n x) ≡ 0ₖ n
--   rCancelK n x = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x (lock t (-ₖ_ {n = n}) x) ≡ 0ₖ n
--     pm unlock = rCancelₖ n x

--   lCancelK : (n : ℕ) (x : coHomK n) → +K n (-K n x) x ≡ 0ₖ n
--   lCancelK n x = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (-ₖ_ {n = n}) x) x ≡ 0ₖ n
--     pm unlock = lCancelₖ n x

--   -cancelRK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n y x) x ≡ y
--   -cancelRK n x y = pm key
--     where
--     pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) y x) x ≡ y
--     pm unlock = -cancelRₖ n x y

--   -cancelLK : (n : ℕ) (x y : coHomK n) → -Kbin n (+K n x y) x ≡ y
--   -cancelLK n x y = pm key
--     where
--     pm : (t : Unit') → lock t (_-ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) x ≡ y
--     pm unlock = -cancelLₖ n x y

--   -+cancelK : (n : ℕ) (x y : coHomK n) → +K n (-Kbin n x y) y ≡ x
--   -+cancelK n x y = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_-ₖ_ {n = n}) x y) y ≡ x
--     pm unlock = -+cancelₖ n x y

--   cancelK : (n : ℕ) (x : coHomK n) → -Kbin n x x ≡ 0ₖ n
--   cancelK n x = pm key
--     where
--     pm : (t : Unit') → (lock t (_-ₖ_ {n = n}) x x) ≡ 0ₖ n
--     pm unlock = cancelₖ n x

--   assocK : (n : ℕ) (x y z : coHomK n) → +K n (+K n x y) z ≡ +K n x (+K n y z)
--   assocK n x y z = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) (lock t (_+ₖ_ {n = n}) x y) z
--                      ≡ lock t (_+ₖ_ {n = n}) x (lock t (_+ₖ_ {n = n}) y z)
--     pm unlock = assocₖ n x y z

--   commK : (n : ℕ) (x y : coHomK n) → +K n x y ≡ +K n y x
--   commK n x y = pm key
--     where
--     pm : (t : Unit') → lock t (_+ₖ_ {n = n}) x y ≡ lock t (_+ₖ_ {n = n}) y x
--     pm unlock = commₖ n x y

--   -- cohom

--   +H : (n : ℕ) (x y : coHom n A) → coHom n A
--   +H n = sRec2 § λ a b → ∣ (λ x → +K n (a x) (b x)) ∣₂

--   -H : (n : ℕ) (x : coHom n A) → coHom n A
--   -H n = sRec § λ a → ∣ (λ x → -K n (a x)) ∣₂

--   -Hbin : (n : ℕ) → coHom n A → coHom n A → coHom n A
--   -Hbin n = sRec2 § λ a b → ∣ (λ x → -Kbin n (a x) (b x)) ∣₂

--   rUnitH : (n : ℕ) (x : coHom n A) → +H n x (0ₕ n) ≡ x
--   rUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
--                   λ a i → ∣ funExt (λ x → rUnitK n (a x)) i ∣₂

--   lUnitH : (n : ℕ) (x : coHom n A) → +H n (0ₕ n) x ≡ x
--   lUnitH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
--                     λ a i → ∣ funExt (λ x → lUnitK n (a x)) i ∣₂

--   rCancelH : (n : ℕ) (x : coHom n A) → +H n x (-H n x) ≡ 0ₕ n
--   rCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
--                    λ a i → ∣ funExt (λ x → rCancelK n (a x)) i ∣₂

--   lCancelH : (n : ℕ) (x : coHom n A) → +H n (-H n x) x  ≡ 0ₕ n
--   lCancelH n = sElim (λ _ → isOfHLevelPath 1 (§ _ _))
--                    λ a i → ∣ funExt (λ x → lCancelK n (a x)) i ∣₂

--   assocH : (n : ℕ) (x y z : coHom n A) → (+H n (+H n x y) z) ≡ (+H n x (+H n y z))
--   assocH n = elim3 (λ _ _ _ → isOfHLevelPath 1 (§ _ _))
--                  λ a b c i → ∣ funExt (λ x → assocK n (a x) (b x) (c x)) i ∣₂

--   commH : (n : ℕ) (x y : coHom n A) → (+H n x y) ≡ (+H n y x)
--   commH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
--                           λ a b i → ∣ funExt (λ x → commK n (a x) (b x)) i ∣₂

--   -cancelRH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n y x) x ≡ y
--   -cancelRH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
--                         λ a b i → ∣ (λ x → -cancelRK n (a x) (b x) i) ∣₂

--   -cancelLH : (n : ℕ) (x y : coHom n A) → -Hbin n (+H n x y) x ≡ y
--   -cancelLH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
--                         λ a b i → ∣ (λ x → -cancelLK n (a x) (b x) i) ∣₂

--   -+cancelH : (n : ℕ) (x y : coHom n A) → +H n (-Hbin n x y) y ≡ x
--   -+cancelH n = sElim2 (λ _ _ → isOfHLevelPath 1 (§ _ _))
--                         λ a b i → ∣ (λ x → -+cancelK n (a x) (b x) i) ∣₂


-- +K→∙ : (key : Unit') (n : ℕ) (a b : coHomK n) → Kn→ΩKn+1 n (lockedCohom.+K key n a b) ≡ Kn→ΩKn+1 n a ∙ Kn→ΩKn+1 n b
-- +K→∙ unlock = +ₖ→∙

-- +H≡+ₕ : (key : Unit') (n : ℕ) → lockedCohom.+H key {A = A} n ≡ _+ₕ_ {n = n}
-- +H≡+ₕ unlock _ = refl

-- rUnitlUnit0K : (key : Unit') (n : ℕ) → lockedCohom.rUnitK key n (0ₖ n) ≡ lockedCohom.lUnitK key n (0ₖ n)
-- rUnitlUnit0K unlock = rUnitlUnit0


-- of
auxGr : ∀ {ℓ} (A : Pointed ℓ) → Group
fst (auxGr A) = ∥ typ (Ω A) ∥₂
0g (snd (auxGr A)) = ∣ refl ∣₂
GroupStr._+_ (snd (auxGr A)) =
  sRec (isSetΠ (λ _ → §)) λ p → sRec § λ q → ∣ p ∙ q ∣₂
- snd (auxGr A) = sRec § λ p → ∣ sym p ∣₂
is-set (isSemigroup (IsGroup.isMonoid (isGroup (snd (auxGr A))))) = §
IsSemigroup.assoc (isSemigroup (IsGroup.isMonoid (isGroup (snd (auxGr A))))) =
  elim3 (λ _ _ _ → isOfHLevelPath 2 § _ _) λ p q r → cong ∣_∣₂ (path-assoc p q r) 
identity (IsGroup.isMonoid (isGroup (snd (auxGr A)))) =
  sElim (λ _ → isSet× (isOfHLevelPath 2 § _ _) (isOfHLevelPath 2 § _ _))
        λ p → (cong ∣_∣₂ (sym (rUnit p))) , (cong ∣_∣₂ (sym (lUnit p)))
IsGroup.inverse (isGroup (snd (auxGr A))) =
  sElim (λ _ → isSet× (isOfHLevelPath 2 § _ _) (isOfHLevelPath 2 § _ _))
        λ p → (cong ∣_∣₂ (rCancel p)) , (cong ∣_∣₂ (lCancel p))
