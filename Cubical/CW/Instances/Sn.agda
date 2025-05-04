{-# OPTIONS --cubical --lossy-unification #-}
module Cubical.CW.Instances.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary

open import Cubical.CW.Base

open Iso

-- Defining family of types
module Sgen (n : ℕ) where
  Sfam : (m : ℕ) → Trichotomyᵗ m (suc n) → Type
  Sfam zero p = ⊥
  Sfam (suc m) (lt x) = Unit
  Sfam (suc m) (eq x) = S₊ n
  Sfam (suc m) (gt x) = S₊ n

  Sfam∙ : (m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) → Sfam (suc m) s
  Sfam∙ m (lt x) = tt
  Sfam∙ m (eq x) = ptSn n
  Sfam∙ m (gt x) = ptSn n

Sfam : (n : ℕ) → ℕ → Type
Sfam n m = Sgen.Sfam n m (m ≟ᵗ suc n)

Sfam∙ : (n m : ℕ) → Sfam n (suc m)
Sfam∙ n m = Sgen.Sfam∙ n m (suc m ≟ᵗ suc n)

-- Cells of Sⁿ
ScardGen : (n m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) → ℕ
ScardGen zero zero s = 2
ScardGen zero (suc m) s = 0
ScardGen (suc n) zero s = 1
ScardGen (suc n) (suc m) (lt x) = 0
ScardGen (suc n) (suc m) (eq x) = 1
ScardGen (suc n) (suc m) (gt x) = 0

Scard : (n : ℕ) → ℕ → ℕ
Scard n m = ScardGen n m (suc m ≟ᵗ suc n)

-- Attaching maps
SαGen : (n m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) (q : Trichotomyᵗ m (suc n))
  → Fin (ScardGen n m s) × S⁻ m → Sgen.Sfam n m q
SαGen n (suc m) s q _ = Sgen.Sfam∙ n m q

Sα : (n m : ℕ) → Fin (Scard n m) × S⁻ m → Sfam n m
Sα n m t = SαGen n m (suc m ≟ᵗ suc n) (m ≟ᵗ suc n) t

-- Characterisation of trivial cells
¬Scard : (n m : ℕ) → n <ᵗ m → ¬ Fin (Scard n m)
¬Scard n m = ¬ScardGen n m (suc m ≟ᵗ suc n)
  where
  ¬ScardGen : (n m : ℕ) (p : _) → n <ᵗ m → ¬ Fin (ScardGen n m p)
  ¬ScardGen zero (suc m) p q = ¬Fin0
  ¬ScardGen (suc n) (suc m) (lt x) q = snd
  ¬ScardGen (suc n) (suc m) (eq x) q =
    λ _ → ¬m<ᵗm (subst (n <ᵗ_) (cong (predℕ ∘ predℕ) x) q)
  ¬ScardGen (suc n) (suc m) (gt x) q = snd

¬Scard' : (n : ℕ) → ¬ Fin (Scard (suc (suc n)) (suc n))
¬Scard' n x with (n ≟ᵗ suc n)
... | eq x₁ = ¬m<ᵗm (subst (n <ᵗ_) (sym x₁) <ᵗsucm)

-- S⁰ ≃ Bool
Sfam0 : (m : ℕ) (p : _) → Sgen.Sfam zero (suc m) p ≃ Bool
Sfam0 m (eq x) = idEquiv _
Sfam0 m (gt x) = idEquiv _

-- 0-skel of Sⁿ⁺¹ is contractible
SfamContr : (n : ℕ) (p : _) → isContr (Sgen.Sfam (suc n) (suc zero) p)
fst (SfamContr n p) = Sgen.Sfam∙ (suc n) zero p
snd (SfamContr n (lt x)) y = refl
snd (SfamContr n (eq x)) y = ⊥.rec (snotz (sym (cong predℕ x)))

isContrSfamGen : (n m : ℕ) (s : m <ᵗ n) (q : _) → isContr (Sgen.Sfam n (suc m) q)
fst (isContrSfamGen n m s q) = Sgen.Sfam∙ n m q
snd (isContrSfamGen n m s (lt x)) y = refl
snd (isContrSfamGen n m s (eq x)) y = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym (cong predℕ x)) s))
snd (isContrSfamGen n m s (gt x)) y = ⊥.rec (¬m<ᵗm (<ᵗ-trans x s))

isPushoutSuspSphereIso : (n m : ℕ) (x : n ≡ m) (q : _)
  → Iso (Susp (S₊ m))
         (Pushout {A = Fin 1 × S₊ m} (λ _ → Sgen.Sfam∙ (suc n) m q) fst)
fun (isPushoutSuspSphereIso n m e s) north =
  inl (Sgen.Sfam∙ (suc n) m s)
fun (isPushoutSuspSphereIso n m e s) south = inr fzero
fun (isPushoutSuspSphereIso n m e s) (merid a i) = push (fzero , a) i
inv (isPushoutSuspSphereIso n m e s) (inl x) = north
inv (isPushoutSuspSphereIso n m e s) (inr x) = south
inv (isPushoutSuspSphereIso n m e s) (push a i) = merid (snd a) i
rightInv (isPushoutSuspSphereIso n m e s) (inl x) i =
  inl (isContrSfamGen (suc n) m (subst (_<ᵗ suc n) e <ᵗsucm) s .snd x i)
rightInv (isPushoutSuspSphereIso n m e s) (inr (zero , tt)) j = inr fzero
rightInv (isPushoutSuspSphereIso n m e s) (push ((zero , tt) , a) i) = help i
  where
  ee = subst (_<ᵗ suc n) e <ᵗsucm
  help : Square {A = Pushout {A = Fin 1 × S₊ m}
                      (λ _ → Sgen.Sfam∙ (suc n) m s) fst}
          (λ i₁ → inl (isContrSfamGen (suc n) m ee s .snd
                         (Sgen.Sfam∙ (suc n) m s) i₁))
          refl
          (push (fzero , a)) (push (fzero , a))
  help = (λ i j → inl (isProp→isSet
                        (isContr→isProp (isContrSfamGen (suc n) m ee s)) _ _
                          (isContrSfamGen (suc n) m ee s .snd
                           (Sgen.Sfam∙ (suc n) m s)) refl i j))
       ◁ λ i j → push (fzero , a) i
leftInv (isPushoutSuspSphereIso n m e s) north = refl
leftInv (isPushoutSuspSphereIso n m e s) south = refl
leftInv (isPushoutSuspSphereIso n m e s) (merid a i) = refl

SfamGenTopElement : (n m : ℕ) → (n <ᵗ m) → (q : _) → S₊ n ≃ Sgen.Sfam n m q
SfamGenTopElement n (suc m) p (lt x) = ⊥.rec (¬squeeze (x , p))
SfamGenTopElement n (suc m) p (eq x) = idEquiv _
SfamGenTopElement n (suc m) p (gt x) = idEquiv _

-- improved iso between Susp Sⁿ and Sⁿ⁺¹ used here
SuspSphere→Sphere : (n : ℕ) → Susp (S₊ n) → S₊ (suc n)
SuspSphere→Sphere n north = ptSn (suc n)
SuspSphere→Sphere zero south = base
SuspSphere→Sphere (suc n) south = south
SuspSphere→Sphere zero (merid t i) = SuspBool→S¹ (merid t i)
SuspSphere→Sphere (suc n) (merid a i) = merid a i

IsoSucSphereSusp' : (n : ℕ) → Iso (S₊ (suc n)) (Susp (S₊ n))
fun (IsoSucSphereSusp' n) = fun (IsoSucSphereSusp n)
inv (IsoSucSphereSusp' n) = SuspSphere→Sphere n
rightInv (IsoSucSphereSusp' zero) north = refl
rightInv (IsoSucSphereSusp' zero) south = SuspBool→S¹→SuspBool south
rightInv (IsoSucSphereSusp' zero) (merid a i) = SuspBool→S¹→SuspBool (merid a i)
rightInv (IsoSucSphereSusp' (suc n)) north = refl
rightInv (IsoSucSphereSusp' (suc n)) south = refl
rightInv (IsoSucSphereSusp' (suc n)) (merid a i) = refl
leftInv (IsoSucSphereSusp' zero) base = S¹→SuspBool→S¹ base
leftInv (IsoSucSphereSusp' zero) (loop i) = S¹→SuspBool→S¹ (loop i)
leftInv (IsoSucSphereSusp' (suc n)) north = refl
leftInv (IsoSucSphereSusp' (suc n)) south = refl
leftInv (IsoSucSphereSusp' (suc n)) (merid a i) = refl

-- Our family Sfam satisfies the pushout property (i.e. is a CW complex)
SαEqGen : (n m : ℕ) (p : Trichotomyᵗ (suc m) (suc n)) (q : _)
  → (Sgen.Sfam n (suc m) p) ≃ Pushout (SαGen n m p q) fst
SαEqGen zero zero p q =
  compEquiv (Sfam0 0 p)
    (compEquiv (isoToEquiv Iso-Bool-Fin2)
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _)))
SαEqGen (suc n) zero p q =
  compEquiv (isContr→Equiv (SfamContr n p) (flast , (λ {(zero , tt) → refl})))
    (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
SαEqGen (suc n) (suc m) (lt x) q =
  invEquiv (isContr→≃Unit ((inl (isContrSfamGen (suc n) m (<ᵗ-trans x <ᵗsucm) q .fst))
    , λ { (inl t) i → inl (isContrSfamGen (suc n) m (<ᵗ-trans x <ᵗsucm) q .snd t i)}))
SαEqGen zero (suc m) (eq x) q = ⊥.rec (snotz (cong predℕ x))
SαEqGen (suc n) (suc m) (eq x) q =
  isoToEquiv (compIso (IsoSucSphereSusp' n)
    (compIso (congSuspIso (substIso S₊ (cong (predℕ ∘ predℕ) (sym x))))
             (isPushoutSuspSphereIso n m (cong (predℕ ∘ predℕ) (sym x)) q)))
SαEqGen zero (suc m) (gt x) (eq x₁) = isoToEquiv (PushoutEmptyFam (λ()) λ())
SαEqGen zero (suc m) (gt x) (gt x₁) = isoToEquiv (PushoutEmptyFam (λ()) λ())
SαEqGen (suc n) (suc m) (gt x) q =
  compEquiv (SfamGenTopElement (suc n) (suc m) x q) (isoToEquiv (PushoutEmptyFam (λ()) λ()))

invEqSαEqGen∙ : (n m : ℕ) (p : Trichotomyᵗ (suc (suc m)) (suc n)) (q : _)
  → invEq (SαEqGen n (suc m) p q) (inl (Sgen.Sfam∙ n m q))
   ≡ Sgen.Sfam∙ n (suc m) p
invEqSαEqGen∙ (suc n) m (lt x) (lt x₁) = refl
invEqSαEqGen∙ n m (lt x) (eq x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ n) x₁ x))
invEqSαEqGen∙ (suc n) (suc m) (lt x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x x₁))
invEqSαEqGen∙ (suc n) m (eq x) (lt x₁) = refl
invEqSαEqGen∙ n m (eq x) (eq x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc m)) (x₁ ∙ sym x) <ᵗsucm))
invEqSαEqGen∙ n m (eq x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc m) (sym x) x₁))
invEqSαEqGen∙ (suc n) m (gt x) (lt x₁) = ⊥.rec (¬squeeze (x , x₁))
invEqSαEqGen∙ zero m (gt x) (eq x₁) = refl
invEqSαEqGen∙ (suc n) m (gt x) (eq x₁) = refl
invEqSαEqGen∙ zero m (gt x) (gt x₁) = refl
invEqSαEqGen∙ (suc n) m (gt x) (gt x₁) = refl

SαEq : (n m : ℕ) → (Sfam n (suc m)) ≃ Pushout (Sα n m) fst
SαEq n m = SαEqGen n m (suc m ≟ᵗ suc n) (m ≟ᵗ suc n)

-- Finally: Sⁿ as a CW skeleton
Sˢᵏᵉˡ : (n : ℕ) → CWskel ℓ-zero
fst (Sˢᵏᵉˡ n) = Sfam n
fst (snd (Sˢᵏᵉˡ n)) = Scard n
fst (snd (snd (Sˢᵏᵉˡ n))) = Sα n
fst (snd (snd (snd (Sˢᵏᵉˡ n)))) = λ{()}
snd (snd (snd (snd (Sˢᵏᵉˡ n)))) = SαEq n

-- Proof that our CW structure converges to Sⁿ as a plain type
SfamTopElement : (n : ℕ) → S₊ n ≃ (Sfam n (suc n))
SfamTopElement n = SfamGenTopElement n (suc n) <ᵗsucm (suc n ≟ᵗ suc n)

SˢᵏᵉˡConverges : (n : ℕ) (k : ℕ)
  → isEquiv (invEq (SαEq n (k +ℕ suc n)) ∘ inl)
SˢᵏᵉˡConverges n k =
  compEquiv (inl , h n _ (<→<ᵗ (k , refl)))
            (invEquiv (SαEq n (k +ℕ suc n))) .snd
  where
  h : (n m : ℕ) → n <ᵗ m
    → isEquiv {A = Sfam n m} {B = Pushout (Sα n m) fst} inl
  h n (suc m) p with (m ≟ᵗ n)
  ... | lt x = ⊥.rec (¬squeeze (x , p))
  ... | eq x = isoToIsEquiv (PushoutEmptyFam (¬Scard n (suc m) p ∘ fst)
                            (¬Scard n (suc m) p))
  ... | gt x = isoToIsEquiv (PushoutEmptyFam (¬Scard n (suc m) p ∘ fst)
                            (¬Scard n (suc m) p))

isCWSphere : (n : ℕ) → isCW (S₊ n)
fst (isCWSphere n) = Sˢᵏᵉˡ n
snd (isCWSphere n) =
  compEquiv (SfamTopElement n)
    (isoToEquiv (converges→ColimIso (suc n) (SˢᵏᵉˡConverges n)))

isFinCWSphere : (n : ℕ) → isFinCW (S₊ n)
fst (isFinCWSphere n) = suc n
fst (fst (snd (isFinCWSphere n))) = Sˢᵏᵉˡ n .fst
fst (snd (fst (snd (isFinCWSphere n)))) = Sˢᵏᵉˡ n .snd
snd (snd (fst (snd (isFinCWSphere n)))) = SˢᵏᵉˡConverges n
snd (snd (isFinCWSphere n)) = isCWSphere n .snd

-- Sⁿ as a CW complex
Sᶜʷ : (n : ℕ) → CW ℓ-zero
fst (Sᶜʷ n) = S₊ n
snd (Sᶜʷ n) = ∣ isCWSphere n ∣₁

Sᶠⁱⁿᶜʷ : (n : ℕ) → finCW ℓ-zero
fst (Sᶠⁱⁿᶜʷ n) = S₊ n
snd (Sᶠⁱⁿᶜʷ n) = ∣ isFinCWSphere n ∣₁
