{-# OPTIONS --lossy-unification #-}
{-
CW structure on spheres
-}
module Cubical.CW.Instances.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import Cubical.Relation.Nullary

open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Properties
open import Cubical.CW.Approximation

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

Sn→SfamGen : ∀ {n k : ℕ} (p : Trichotomyᵗ k (suc n))
  → 0 <ᵗ k → S₊ n → Sgen.Sfam n k p
Sn→SfamGen {n = n} {suc k} (lt x₁) _ x = tt
Sn→SfamGen {n = n} {suc k} (eq x₁) _ x = x
Sn→SfamGen {n = n} {suc k} (gt x₁) _ x = x

Sn→SfamGen∙ : ∀ {n k : ℕ} (p : Trichotomyᵗ (suc k) (suc n))
  → Sn→SfamGen p tt (ptSn n) ≡ Sgen.Sfam∙ n k p
Sn→SfamGen∙ (lt x) = refl
Sn→SfamGen∙ (eq x) = refl
Sn→SfamGen∙ (gt x) = refl

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

isContrSfamGen : (n m : ℕ) (s : m <ᵗ n) (q : _)
  → isContr (Sgen.Sfam n (suc m) q)
fst (isContrSfamGen n m s q) = Sgen.Sfam∙ n m q
snd (isContrSfamGen n m s (lt x)) y = refl
snd (isContrSfamGen n m s (eq x)) y =
  ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym (cong predℕ x)) s))
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
rightInv (IsoSucSphereSusp' zero) (merid a i) =
  SuspBool→S¹→SuspBool (merid a i)
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
SαEqGen (suc n) (suc m) (lt x) q = invEquiv
  (isContr→≃Unit ((inl (isContrSfamGen (suc n) m (<ᵗ-trans x <ᵗsucm) q .fst))
  , λ { (inl t) i → inl (isContrSfamGen (suc n) m (<ᵗ-trans x <ᵗsucm) q .snd
                           t i)}))
SαEqGen zero (suc m) (eq x) q = ⊥.rec (snotz (cong predℕ x))
SαEqGen (suc n) (suc m) (eq x) q =
  isoToEquiv (compIso (IsoSucSphereSusp' n)
    (compIso (congSuspIso (substIso S₊ (cong (predℕ ∘ predℕ) (sym x))))
             (isPushoutSuspSphereIso n m (cong (predℕ ∘ predℕ) (sym x)) q)))
SαEqGen zero (suc m) (gt x) (eq x₁) = isoToEquiv (PushoutEmptyFam (λ()) λ())
SαEqGen zero (suc m) (gt x) (gt x₁) = isoToEquiv (PushoutEmptyFam (λ()) λ())
SαEqGen (suc n) (suc m) (gt x) q =
  compEquiv (SfamGenTopElement (suc n) (suc m) x q)
            (isoToEquiv (PushoutEmptyFam (λ()) λ()))

invEqSαEqGen∙ : (n m : ℕ) (p : Trichotomyᵗ (suc (suc m)) (suc n)) (q : _)
  → invEq (SαEqGen n (suc m) p q) (inl (Sgen.Sfam∙ n m q))
   ≡ Sgen.Sfam∙ n (suc m) p
invEqSαEqGen∙ (suc n) m (lt x) (lt x₁) = refl
invEqSαEqGen∙ n m (lt x) (eq x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ n) x₁ x))
invEqSαEqGen∙ (suc n) (suc m) (lt x) (gt x₁) =
  ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x x₁))
invEqSαEqGen∙ (suc n) m (eq x) (lt x₁) = refl
invEqSαEqGen∙ n m (eq x) (eq x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc m)) (x₁ ∙ sym x) <ᵗsucm))
invEqSαEqGen∙ n m (eq x) (gt x₁) =
  ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc m) (sym x) x₁))
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

hasCWskelSphere : (n : ℕ) → hasCWskel (S₊ n)
fst (hasCWskelSphere n) = Sˢᵏᵉˡ n
snd (hasCWskelSphere n) =
  compEquiv (SfamTopElement n)
    (isoToEquiv (converges→ColimIso (suc n) (SˢᵏᵉˡConverges n)))

hasFinCWskelSphere : (n : ℕ) → hasFinCWskel (S₊ n)
fst (hasFinCWskelSphere n) = suc n
fst (fst (snd (hasFinCWskelSphere n))) = Sˢᵏᵉˡ n .fst
fst (snd (fst (snd (hasFinCWskelSphere n)))) = Sˢᵏᵉˡ n .snd
snd (snd (fst (snd (hasFinCWskelSphere n)))) = SˢᵏᵉˡConverges n
snd (snd (hasFinCWskelSphere n)) = hasCWskelSphere n .snd

-- Sⁿ as a CW complex
Sᶜʷ : (n : ℕ) → CW ℓ-zero
fst (Sᶜʷ n) = S₊ n
snd (Sᶜʷ n) = ∣ hasCWskelSphere n ∣₁

Sᶠⁱⁿᶜʷ : (n : ℕ) → finCW ℓ-zero
fst (Sᶠⁱⁿᶜʷ n) = S₊ n
snd (Sᶠⁱⁿᶜʷ n) = ∣ hasFinCWskelSphere n ∣₁


--- cellular approximations of maps from spheres into CW complexes
module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (f : S₊ n → fst X (suc n))
  (f₀ : f (ptSn n) ≡ CWskel∙ X x₀ n) where
  private
    <ᵗ→0<ᵗ : {n m : ℕ} → n <ᵗ m → 0 <ᵗ m
    <ᵗ→0<ᵗ {n} {suc m} _ = tt

  cellMapSˢᵏᵉˡFunGenGen : ∀ k → (p : _) → Sgen.Sfam n k p → fst X k
  cellMapSˢᵏᵉˡFunGenGen (suc k) (lt x₁) x = CWskel∙ X x₀ k
  cellMapSˢᵏᵉˡFunGenGen (suc k) (eq x₁) x = subst (fst X) (sym x₁) (f x)
  cellMapSˢᵏᵉˡFunGenGen (suc k) (gt x₁) x =
    CW↪ X k (cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n) (Sn→SfamGen _ (<ᵗ→0<ᵗ x₁) x))

  cellMapSˢᵏᵉˡFunGenGen∙ : ∀ k → (p : _)
    → cellMapSˢᵏᵉˡFunGenGen (suc k) p (Sgen.Sfam∙ n k p) ≡ CWskel∙ X x₀ k
  cellMapSˢᵏᵉˡFunGenGen∙ k (lt x) = refl
  cellMapSˢᵏᵉˡFunGenGen∙ k (eq x) =
    cong₂ (λ p q → subst (fst X) p q) (isSetℕ _ _ _ _) f₀ ∙ H _ (cong predℕ x)
    where
    H : (n : ℕ) (x : k ≡ n)
      → subst (fst X) (cong suc (sym x)) (CWskel∙ X x₀ n) ≡ CWskel∙ X x₀ k
    H = J> transportRefl _
  cellMapSˢᵏᵉˡFunGenGen∙ (suc k) (gt x) =
    cong (CW↪ X (suc k))
      (cong (cellMapSˢᵏᵉˡFunGenGen (suc k) (Trichotomyᵗ-suc (k ≟ᵗ n)))
            (Sn→SfamGen∙ (Trichotomyᵗ-suc (k ≟ᵗ n)))
      ∙ cellMapSˢᵏᵉˡFunGenGen∙ k (suc k ≟ᵗ suc n))

  cellMapSˢᵏᵉˡFunGenComm : (k : ℕ) (p : _) (q : _) (x : _)
    → cellMapSˢᵏᵉˡFunGenGen (suc k) p (invEq (SαEqGen n k p q) (inl x))
    ≡ CW↪ X k (cellMapSˢᵏᵉˡFunGenGen k q x)
  cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (lt x₂) x = refl
  cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (eq x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (subst (suc k <ᵗ_) (cong predℕ (sym x₂)) x₁))
  cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x₁ x₂))
  cellMapSˢᵏᵉˡFunGenComm (suc k) (eq x₁) (lt x₂) x =
    cong (subst (fst X) (sym x₁) ∘ f) (invEqSαEqGen∙ n k _ _)
    ∙ cellMapSˢᵏᵉˡFunGenGen∙ (suc k) (eq x₁)
  cellMapSˢᵏᵉˡFunGenComm k (eq x₁) (eq x₂) x =
    ⊥.rec (falseDichotomies.eq-eq (refl , sym (x₁ ∙ sym x₂)))
  cellMapSˢᵏᵉˡFunGenComm k (eq x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn {n} (subst (suc (suc n) <ᵗ_) x₁ x₂))
  cellMapSˢᵏᵉˡFunGenComm k (gt x₁) (lt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
  cellMapSˢᵏᵉˡFunGenComm (suc k) (gt x₁) (eq x₂) x with (k ≟ᵗ n)
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x₂) x₃))
  ... | eq x₃ = cong (CW↪ X (suc k))
    (cong (subst (fst X) (cong suc (sym x₃))) (cong f (lem n x x₁ x₂))
    ∙ cong (λ p → subst (fst X) p (f x))
      (isSetℕ _ _ (cong suc (sym x₃)) (sym x₂)))
    where
    lem : (n : ℕ) (x : _) (x₁ : _) (x₂ : _)
      → invEq (SαEqGen n (suc k) (gt x₁) (eq x₂)) (inl x) ≡ x
    lem zero x x₁ x₂ = refl
    lem (suc n) x x₁ x₂ = refl
  ... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (cong predℕ  x₂) x₃))
  cellMapSˢᵏᵉˡFunGenComm (suc k) (gt x₁) (gt x₂) x with k ≟ᵗ n
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₂ x₃))
  ... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₂))
  ... | gt x₃ =
    cong (CW↪ X (suc k))
       (cong (CW↪ X k ∘ cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n))
         (cong (λ w → Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ w)
           (invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x))) (isProp<ᵗ x₃ x₂)
       ∙ cong (Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ x₂))
          (lem n k x₁ x₂ x (k ≟ᵗ suc n)))
      ∙ cellMapSˢᵏᵉˡFunGenComm k (gt x₂) (k ≟ᵗ suc n) _)
      where
      lem : (n k : ℕ) (x₁ : _) (x₂ : _) (x : _) (w : _)
        → invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x) ≡
                         invEq (SαEqGen n k (gt x₂) w)
                         (inl (Sn→SfamGen w (<ᵗ→0<ᵗ x₂) x))
      lem n k x₁ x₂ x (lt x₃) = ⊥.rec (¬squeeze (x₂ , x₃))
      lem zero (suc k) x₁ x₂ x (eq x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (eq x₃) = refl
      lem zero (suc k) x₁ x₂ x (gt x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (gt x₃) = refl

  cellMapSˢᵏᵉˡ : cellMap (Sˢᵏᵉˡ n) X
  SequenceMap.map cellMapSˢᵏᵉˡ k = cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n)
  SequenceMap.comm cellMapSˢᵏᵉˡ k x =
    sym (cellMapSˢᵏᵉˡFunGenComm k (suc k ≟ᵗ suc n) (k ≟ᵗ suc n) x)

approxSphereMap∙ : ∀ {ℓ} (Xsk : CWskel ℓ) → (x₀ : fst Xsk (suc zero)) (n : ℕ)
  (f : S₊∙ (suc n) →∙ (realise Xsk , incl x₀))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ (fst Xsk (suc (suc n)) , CWskel∙ Xsk x₀ (suc n)) ]
      (incl∙ Xsk x₀ ∘∙ f' ≡ f)
approxSphereMap∙ Xsk x₀ n f =
  PT.rec squash₁
     (λ F → TR.rec squash₁
              (λ fp → ∣ ((λ x → F x .fst .fst)
                       , sym (cong fst fp))
       , ΣPathP ((funExt (λ x → F x .fst .snd))
       , (SQ' _ _ _ _ _ _ _ _ (cong snd fp))) ∣₁)
     (F (ptSn (suc n)) .snd refl))
     approxSphereMap
  where
  SQ' : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y)
        (z : A) (q : y ≡ z) (w : A) (r : x ≡ w) (t :  w ≡ z)
    → Square (p ∙ q) t r refl → Square (sym r ∙ p) (sym q) t refl
  SQ' x = J> (J> (J> λ t s → sym (rUnit refl)
        ◁ λ i j → (rUnit refl ◁ s) (~ j) i))

  approxSphereMap : ∥ ((x : S₊ (suc n))
    → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
                ((p : ptSn (suc n) ≡ x)
              → hLevelTrunc 1 (PathP (λ i
                → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                  ((CWskel∙ Xsk x₀ (suc n))
                 , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb))) ∥₁
  approxSphereMap = sphereToTrunc (suc (suc n))
    {λ x → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
                ((p : ptSn (suc n) ≡ x)
     → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                  ((CWskel∙ Xsk x₀ (suc n))
                 , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb) )}
      λ a → TR.rec (isOfHLevelTrunc (suc (suc n)))
      (λ fa → ∣ fa
      , (λ p → J (λ a p → (fa : fiber (CW↪∞ Xsk (suc (suc n))) (fst f a))
       → hLevelTrunc 1
           (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
           (CWskel∙ Xsk x₀ (suc n)
           , CWskel∞∙Id Xsk x₀ (suc n) ∙ (λ i → snd f (~ i))) fa))
                  (λ fa → isConnectedPathP 1 (isConnectedSubtr' n 2
                           (isConnected-CW↪∞ (suc (suc n))
                             Xsk (fst f (ptSn (suc n))))) _ _ .fst) p fa) ∣ₕ)
      (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f a) .fst)

module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (faprx : S₊∙ n →∙ (fst X (suc n) , CWskel∙ X x₀ n))
  (f : S₊∙ n →∙ (realise X , incl x₀))
  (faprx≡ : (x : _) → incl {n = suc n} (fst faprx x) ≡ fst f x) where

  cellMapSˢᵏᵉˡImproved : cellMap (Sˢᵏᵉˡ n) X
  cellMapSˢᵏᵉˡImproved = cellMapSˢᵏᵉˡ X n x₀ (fst faprx) (snd faprx)

  isApproxCellMapSˢᵏᵉˡImproved : realiseSequenceMap cellMapSˢᵏᵉˡImproved
           ≡ fst f ∘ invEq (hasCWskelSphere n .snd)
  isApproxCellMapSˢᵏᵉˡImproved =
    funExt λ x → cong (realiseSequenceMap cellMapSˢᵏᵉˡImproved)
                       (sym (secEq (hasCWskelSphere n .snd) x))
                ∙ lem _
    where
    lem : (x : _)
      → realiseSequenceMap cellMapSˢᵏᵉˡImproved (fst (hasCWskelSphere n .snd) x)
       ≡ fst f x
    lem x with (n ≟ᵗ n)
    ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
    ... | eq x₁ = cong (incl {n = suc n})
                  (cong (λ p → subst (fst X) p (fst faprx x))
                   (isSetℕ _ _ _ refl)
                ∙ transportRefl (fst faprx x)) ∙ faprx≡ x
    ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

  finCellApproxSˢᵏᵉˡImproved : (k : ℕ)
    → finCellApprox (Sˢᵏᵉˡ n) X (fst f ∘ invEq (hasCWskelSphere n .snd)) k
  FinSequenceMap.fmap (fst (finCellApproxSˢᵏᵉˡImproved k)) =
    SequenceMap.map cellMapSˢᵏᵉˡImproved ∘ fst
  FinSequenceMap.fcomm (fst (finCellApproxSˢᵏᵉˡImproved k)) =
    SequenceMap.comm cellMapSˢᵏᵉˡImproved ∘ fst
  snd (finCellApproxSˢᵏᵉˡImproved k) = →FinSeqColimHomotopy _ _
    (funExt⁻ isApproxCellMapSˢᵏᵉˡImproved ∘ FinSeqColim→Colim k ∘ (fincl flast))

-- cellMapSˢᵏᵉˡ preserves ∙Π (homotopy group addition)
cellMapSˢᵏᵉˡ∙Π : ∀ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (faprx gaprx : S₊∙ (suc n) →∙ (fst X (suc (suc n)) , CWskel∙ X x₀ (suc n)))
  (f : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (faprx≡ : incl∙ X x₀ ∘∙ faprx ≡ f)
  (g : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (gaprx≡ : incl∙ X x₀ ∘∙ gaprx ≡ g)
  → realiseCellMap (cellMapSˢᵏᵉˡImproved X (suc n) x₀ (∙Π faprx gaprx) (∙Π f g)
      (λ x → funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x
            ∙ λ i → ∙Π (faprx≡ i) (gaprx≡ i) .fst x))
    ≡ (∙Π f g .fst ∘ invEq (hasCWskelSphere (suc n) .snd))
cellMapSˢᵏᵉˡ∙Π X n x₀ faprx gaprx =
  J> (J> funExt λ x → cong h (sym (secEq (hasCWskelSphere (suc n) .snd) x))
                     ∙ main _
                     ∙ cong (∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx) .fst)
                         (retEq (SfamTopElement (suc n)) _))
  where
  h = realiseCellMap (cellMapSˢᵏᵉˡImproved X (suc n) x₀
      (∙Π faprx gaprx) (∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx))
      (λ x → (funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x) ∙ refl))

  main : (x : Sgen.Sfam (suc n) (suc (suc n)) (suc (suc n) ≟ᵗ suc (suc n)))
       → h (incl {n = suc (suc n)} x)
       ≡ ∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx) .fst
             (invEq (SfamTopElement (suc n)) x)
  main with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = λ x
    → cong (incl {n = suc (suc n)})
         (cong (λ p → subst (fst X) p (fst (∙Π faprx gaprx) x)) (isSetℕ _ _ _ refl)
          ∙ transportRefl _)
      ∙ funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x
  ... | gt x = ⊥.rec (¬m<ᵗm x)
