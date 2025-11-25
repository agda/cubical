
{-
This file contains:
1. Definition of the multplication Sⁿ × Sᵐ → Sⁿ⁺ᵐ
2. The fact that the multiplication induces an equivalence Sⁿ ∧ Sᵐ ≃ Sⁿ⁺ᵐ
3. The fact that the multiplication induces an equivalence Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹
4. The algebraic properties of this map
-}

module Cubical.HITs.Sn.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding (elim)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma

open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S2
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Loopspace

open Iso

open PlusBis


---- Sphere multiplication
-- auxiliary function
sphereFun↑ : {n m k : ℕ}
  → (f : S₊ n → S₊ m → S₊ k)
  → S₊ (suc n) → S₊ m → S₊ (suc k)
sphereFun↑ {n = zero} {m = m} f base y = ptSn _
sphereFun↑ {n = zero} {m = m} f (loop i) y = σS (f false y) i
sphereFun↑ {n = suc n} {m = m} f north y = ptSn _
sphereFun↑ {n = suc n} {m = m} f south y = ptSn _
sphereFun↑ {n = suc n} {m = m} f (merid a i) y = σS (f a y) i

-- sphere multiplication
_⌣S_ : {n m : ℕ} → S₊ n → S₊ m → S₊ (n + m)
_⌣S_ {n = zero} {m = m} false y = y
_⌣S_ {n = zero} {m = m} true y = ptSn m
_⌣S_ {n = suc n} {m = m} = sphereFun↑ (_⌣S_ {n = n})

-- Left- and right-unit laws
IdR⌣S : {n m : ℕ} (y : S₊ m)
  → Path (S₊ (n + m)) (ptSn n ⌣S y) (ptSn (n + m))
IdR⌣S {n = zero} {m = m} y = refl
IdR⌣S {n = suc zero} {m = m} y = refl
IdR⌣S {n = suc (suc n)} {m = m} y = refl

IdL⌣S : {n m : ℕ} (x : S₊ n)
  → Path (S₊ (n + m)) (x ⌣S (ptSn m)) (ptSn (n + m))
IdL⌣S {n = zero} false = refl
IdL⌣S {n = zero} true = refl
IdL⌣S {n = suc zero} base = refl
IdL⌣S {n = suc zero} {zero} (loop i) j = base
IdL⌣S {n = suc zero} {suc m} (loop i) j = rCancel (merid (ptSn (suc m))) j i
IdL⌣S {n = suc (suc n)} {m} north j = north
IdL⌣S {n = suc (suc n)} {m} south j = north
IdL⌣S {n = suc (suc n)} {m} (merid a i) j =
  (cong σS (IdL⌣S a)
  ∙ rCancel (merid (ptSn _))) j i

IdL⌣S≡IdR⌣S : (n m : ℕ)
  → IdL⌣S {n = n} {m = m} (ptSn n) ≡ IdR⌣S (ptSn m)
IdL⌣S≡IdR⌣S zero m = refl
IdL⌣S≡IdR⌣S (suc zero) m = refl
IdL⌣S≡IdR⌣S (suc (suc n)) m = refl

-- Multiplication induced on smash products of spheres
⋀S∙ : (n m : ℕ) → S₊∙ n ⋀∙ S₊∙ m →∙ S₊∙ (n + m)
fst (⋀S∙ n m) (inl x) = ptSn _
fst (⋀S∙ n m) (inr x) = (fst x) ⌣S (snd x)
fst (⋀S∙ n m) (push (inl x) i) = IdL⌣S x (~ i)
fst (⋀S∙ n m) (push (inr x) i) = IdR⌣S x (~ i)
fst (⋀S∙ n m) (push (push a i₁) i) = IdL⌣S≡IdR⌣S n m i₁ (~ i)
snd (⋀S∙ n m) = refl

⋀S : (n m : ℕ) → S₊∙ n ⋀ S₊∙ m → S₊ (n + m)
⋀S n m = fst (⋀S∙ n m)

-- Proof that it is an equivalence
⋀S-base : (m : ℕ)
  → Iso (S₊∙ zero ⋀ S₊∙ m) (S₊ m)
fun (⋀S-base m) = ⋀S zero m
inv (⋀S-base m) x = inr (false , x)
rightInv (⋀S-base m) x = refl
leftInv (⋀S-base m) =
  ⋀-fun≡ _ _
    (sym (push (inl false)))
    (λ { (false , y) → refl
       ; (true , y) → sym (push (inl false)) ∙ push (inr y)})
     (λ { false i j → push (inl false) (i ∨ ~ j)
        ; true → compPath-filler (sym (push (inl false))) (push (inl true))
        ▷ cong (sym (push (inl false)) ∙_)
                (λ i → push (push tt i) )})
        λ x → compPath-filler (sym (push (inl false))) (push (inr x))
{-
Proof that ⋀S respects suspension, i.e. that the following diagram commutes
                ⋀S
Sⁿ⁺¹ ∧ Sᵐ ---------------> Sⁿ⁺ᵐ⁺¹
|                          |
|                          |
v                          v
Σ (Sⁿ ∧ Sᵐ)  -----------> Σ Sⁿ⁺ᵐ
                Σ(⋀S)
-}

⋀S-ind : (n m : ℕ) (x : _)
  → ⋀S (suc n) m x
   ≡ Iso.inv (IsoSucSphereSusp (n + m))
      (suspFun (⋀S n m) (Iso.fun SuspSmashCommIso
        (((Iso.fun (IsoSucSphereSusp n) , IsoSucSphereSusp∙' n)
      ⋀→ idfun∙ (S₊∙ m)) x)))
⋀S-ind zero m = ⋀-fun≡ _ _
  (sym (IsoSucSphereSusp∙ m))
    (λ x → main m (fst x) (snd x))
    (mainₗ m)
    mainᵣ
  where
  F' :  (m : ℕ) → Susp ((Bool , true) ⋀ S₊∙ m) → _
  F' m = inv (IsoSucSphereSusp (zero + m)) ∘ suspFun (⋀S zero m)

  F : (m : ℕ) → Susp∙ Bool ⋀ S₊∙ m → _
  F m = F' m ∘ fun SuspSmashCommIso

  G : (m : ℕ) → _ → _
  G m = _⋀→_ {A = S₊∙ 1} {B = S₊∙ m}
         (fun (IsoSucSphereSusp zero) , (λ _ → north))
         (idfun∙ (S₊∙ m))

  main : (m : ℕ) (x : S¹) (y : S₊ m)
    → x ⌣S y
    ≡ F m (inr (S¹→SuspBool x , y))
  main m base y = sym (IsoSucSphereSusp∙ m)
  main zero (loop i) false j =
    ((cong-∙ (λ x → F zero (inr (x , false)))
             (merid false) (sym (merid true)))
    ∙ sym (rUnit loop)) (~ j) i
  main zero (loop i) true j =
    F zero (inr (rCancel (merid true) (~ j) i , false))
  main (suc m) (loop i) y j =
    cong-∙ (λ x → F (suc m) (inr (x , y)))
           (merid false) (sym (merid true)) (~ j) i

  mainₗ : (m : ℕ) (x : S¹)
    → PathP (λ i → IdL⌣S {m = m} x (~ i)
            ≡ F m (G m (push (inl x) i)))
             (sym (IsoSucSphereSusp∙ m))
             (main m x (ptSn m))
  mainₗ zero =
    toPropElim (λ _ → isOfHLevelPathP' 1 (isGroupoidS¹ _ _) _ _)
     (flipSquare (cong (cong (F zero)) (rUnit (push (inl north)))))
  mainₗ (suc m) x = flipSquare (help x
    ▷ (cong (cong (F (suc m))) (rUnit (push (inl (S¹→SuspBool x))))))
    where
    help : (x : S¹)
      → PathP (λ i → north ≡ main (suc m) x (ptSn (suc m)) i)
           (sym (IdL⌣S {n = 1} x))
           (cong (F (suc m)) (push (inl (S¹→SuspBool x))))
    help base = refl
    help (loop i) j k =
      hcomp (λ r
        → λ {(i = i0) → north
            ; (i = i1) → F' (suc m)
                           (merid-fill
                            {A = Bool , true}
                            {B = S₊∙ (suc m)} true (~ r) k j)
            ; (j = i0) → rCancel-filler (merid (ptSn (suc m))) r (~ k) i
            ; (j = i1) → F (suc m)
                           (push (inl (compPath-filler
                             (merid false) (sym (merid true)) r i)) k)
            ; (k = i0) → north
            ; (k = i1) → cong-∙∙-filler
                            (λ x₁ → F (suc m) (inr (x₁ , ptSn (suc m))))
                            refl (merid false) (sym (merid true)) r (~ j) i})
       (F' (suc m) (merid-fill {A = Bool , true} {B = S₊∙ (suc m)} false k i j))
  mainᵣ : (x : S₊ m)
    → PathP (λ i → ptSn (suc m) ≡ F m (G m (push (inr x) i)))
             (sym (IsoSucSphereSusp∙ m))
             (sym (IsoSucSphereSusp∙ m))
  mainᵣ x = flipSquare ((λ i j → (IsoSucSphereSusp∙ m) (~ i))
                       ▷ cong (cong (F m)) (rUnit (push (inr x))))
⋀S-ind (suc n) m = ⋀-fun≡ _ _ refl
  (λ x → h (fst x) (snd x))
  hₗ
  λ x → flipSquare (cong (cong (suspFun (⋀S (suc n) m)
                              ∘ fun SuspSmashCommIso))
                    (rUnit (push (inr x))))
  where
  h : (x : S₊ (suc (suc n))) (y : S₊ m)
    → (x ⌣S y)
    ≡ suspFun (⋀S (suc n) m)
       (SuspL→Susp⋀ (inr (idfun (Susp (S₊ (suc n))) x , y)))
  h north y = refl
  h south y = merid (ptSn _)
  h (merid a i) y j = compPath-filler
           (merid (a ⌣S y)) (sym (merid (ptSn (suc (n + m))))) (~ j) i

  hₗ-lem : (x : Susp (S₊ (suc n)))
    → PathP (λ i → north ≡ h x (ptSn m) i)
             (sym (IdL⌣S x))
             (cong (suspFun (⋀S (suc n) m)
                  ∘ fun SuspSmashCommIso)
                   (push (inl x)))
  hₗ-lem north = refl
  hₗ-lem south i j = merid (ptSn (suc (n + m))) (i ∧ j)
  hₗ-lem (merid a i) j k = help j k i
    where
    help : Cube (sym (cong σS
                  (IdL⌣S {n = suc n} {m = m} a)
                 ∙ rCancel (merid (ptSn (suc n + m)))))
                (λ k i → suspFun (⋀S (suc n) m)
                           (SuspL→Susp⋀ (push (inl (merid a i)) k)))
                (λ j i → north)
                (λ j i → compPath-filler
                           (merid (a ⌣S ptSn m))
                           (sym (merid (ptSn (suc (n + m))))) (~ j) i)
                (λ j k → north)
                λ j k → merid (ptSn (suc (n + m))) (j ∧ k)
    help j k i =
      hcomp (λ r
        → λ {(i = i0) → north
            ; (i = i1) → merid (ptSn (suc (n + m))) (j ∧ k)
            ; (j = i0) → compPath-filler'
                           (cong σS
                            (IdL⌣S {n = suc n} {m = m} a))
                           (rCancel (merid (ptSn (suc n + m)))) r (~ k) i
            ; (j = i1) → suspFun (⋀S (suc n) m)
                           (merid-fill a k i r)
            ; (k = i0) → north
            ; (k = i1) → compPath-filler
                           (merid (IdL⌣S a (~ r)))
                           (sym (merid (ptSn (suc (n + m))))) (~ j) i})
         (hcomp (λ r → λ {(i = i0) → north
                        ; (i = i1) → merid (ptSn (suc (n + m))) ((j ∨ ~ r) ∧ k)
                        ; (j = i0) → rCancel-filler (merid (ptSn _)) r (~ k) i
                        ; (j = i1) → merid (ptSn (suc (n + m))) (i ∧ k)
                        ; (k = i0) → north
                        ; (k = i1) → compPath-filler
                                       (merid (ptSn _))
                                       (sym (merid (ptSn (suc (n + m)))))
                                       (~ j ∧ r) i})
                  (merid (ptSn (suc (n + m))) (i ∧ k)))

  hₗ : (x : Susp (S₊ (suc n)))
    → PathP (λ i → IdL⌣S x (~ i)
      ≡ inv (IsoSucSphereSusp (suc n + m))
         (suspFun (⋀S (suc n) m)
          (fun SuspSmashCommIso
           (((fun (IsoSucSphereSusp (suc n)) , IsoSucSphereSusp∙' (suc n)) ⋀→
             idfun∙ (S₊∙ m))
            (push (inl x) i))))) refl (h x (ptSn m))
  hₗ x =
    flipSquare
       ((hₗ-lem x
      ▷ sym (cong (cong (inv (IsoSucSphereSusp (suc n + m))
                  ∘ suspFun (⋀S (suc n) m)
                  ∘ fun SuspSmashCommIso))
                  (sym (rUnit (push (inl x)))))))


isEquiv-⋀S : (n m : ℕ) → isEquiv (⋀S n m)
isEquiv-⋀S zero m = isoToIsEquiv (⋀S-base m)
isEquiv-⋀S (suc n) m =
  subst isEquiv (sym (funExt (⋀S-ind n m)))
    (snd (helpEq (isEquiv-⋀S n m)))
  where
  r = isoToEquiv (IsoSucSphereSusp n)

  helpEq : isEquiv (⋀S n m) → (S₊∙ (suc n) ⋀ S₊∙ m) ≃ S₊ (suc n + m)
  helpEq iseq =
    compEquiv
     (compEquiv
       (compEquiv
         (⋀≃ (r , IsoSucSphereSusp∙' n) (idEquiv (S₊ m) , refl))
         (isoToEquiv SuspSmashCommIso))
       (isoToEquiv
         (congSuspIso (equivToIso (⋀S n m , iseq)))))
      (isoToEquiv (invIso (IsoSucSphereSusp (n + m))))

SphereSmashIso : (n m : ℕ) → Iso (S₊∙ n ⋀ S₊∙ m) (S₊ (n + m))
SphereSmashIso n m = equivToIso (⋀S n m , isEquiv-⋀S n m)

-- Proof that the pinch map Sⁿ * Sᵐ → Sⁿ⁺ᵐ⁺¹ is an equivalence
join→Sphere : (n m : ℕ)
  → join (S₊ n) (S₊ m) → S₊ (suc (n + m))
join→Sphere n m (inl x) = ptSn _
join→Sphere n m (inr x) = ptSn _
join→Sphere n m (push a b i) = σS (a ⌣S b) i

join→Sphere∙ : (n m : ℕ)
  → join∙ (S₊∙ n) (S₊∙ m) →∙ S₊∙ (suc (n + m))
fst (join→Sphere∙ n m) = join→Sphere n m
snd (join→Sphere∙ n m) = refl

joinSphereIso' : (n m : ℕ)
  → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
joinSphereIso' n m =
  compIso (invIso (SmashJoinIso {A = S₊∙ n} {B = S₊∙ m}))
   (compIso (congSuspIso (SphereSmashIso n m))
    (invIso (IsoSucSphereSusp (n + m))))

-- The inverse function is not definitionally pointed. Let's change this
sphere→Join : (n m : ℕ)
  → S₊ (suc (n + m)) → join (S₊ n) (S₊ m)
sphere→Join zero zero = Iso.inv (joinSphereIso' 0 0)
sphere→Join zero (suc m) north = inl true
sphere→Join zero (suc m) south = inl true
sphere→Join zero (suc m) (merid a i) =
  (push true (ptSn (suc m))
  ∙ cong (Iso.inv (joinSphereIso' zero (suc m))) (merid a)) i
sphere→Join (suc n) m north = inl (ptSn (suc n))
sphere→Join (suc n) m south = inl (ptSn (suc n))
sphere→Join (suc n) m (merid a i) =
    (push (ptSn (suc n)) (ptSn m)
  ∙ cong (Iso.inv (joinSphereIso' (suc n) m)) (merid a)) i

join→Sphere≡ : (n m : ℕ) (x : _)
  → join→Sphere n m x ≡ joinSphereIso' n m .Iso.fun x
join→Sphere≡ zero zero (inl x) = refl
join→Sphere≡ zero (suc m) (inl x) = refl
join→Sphere≡ (suc n) m (inl x) = refl
join→Sphere≡ zero zero (inr x) = refl
join→Sphere≡ zero (suc m) (inr x) = merid (ptSn (suc m))
join→Sphere≡ (suc n) zero (inr x) = merid (ptSn (suc n + zero))
join→Sphere≡ (suc n) (suc m) (inr x) = merid (ptSn (suc n + suc m))
join→Sphere≡ zero zero (push false false i) j = loop i
join→Sphere≡ zero zero (push false true i) j = base
join→Sphere≡ zero zero (push true b i) j = base
join→Sphere≡ zero (suc m) (push a b i) j =
  compPath-filler
    (merid (a ⌣S b)) (sym (merid (ptSn (suc m)))) (~ j) i
join→Sphere≡ (suc n) zero (push a b i) j =
  compPath-filler
    (merid (a ⌣S b)) (sym (merid (ptSn (suc n + zero)))) (~ j) i
join→Sphere≡ (suc n) (suc m) (push a b i) j =
  compPath-filler
    (merid (a ⌣S b)) (sym (merid (ptSn (suc n + suc m)))) (~ j) i

sphere→Join≡ : (n m : ℕ) (x : _)
  → sphere→Join n m x ≡ joinSphereIso' n m .Iso.inv x
sphere→Join≡ zero zero x = refl
sphere→Join≡ zero (suc m) north = push true (pt (S₊∙ (suc m)))
sphere→Join≡ zero (suc m) south = refl
sphere→Join≡ zero (suc m) (merid a i) j =
  compPath-filler' (push true (pt (S₊∙ (suc m))))
                   (cong (joinSphereIso' zero (suc m) .Iso.inv) (merid a)) (~ j) i
sphere→Join≡ (suc n) m north = push (ptSn (suc n)) (pt (S₊∙ m))
sphere→Join≡ (suc n) m south = refl
sphere→Join≡ (suc n) m (merid a i) j =
  compPath-filler' (push (ptSn (suc n)) (pt (S₊∙ m)))
                   (cong (joinSphereIso' (suc n) m .Iso.inv) (merid a)) (~ j) i

-- Todo: integrate with Sn.Properties IsoSphereJoin
IsoSphereJoin : (n m : ℕ)
  → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
fun (IsoSphereJoin n m) = join→Sphere n m
inv (IsoSphereJoin n m) = sphere→Join n m
rightInv (IsoSphereJoin n m) x =
  (λ i → join→Sphere≡ n m (sphere→Join≡ n m x i) i)
  ∙ joinSphereIso' n m .Iso.rightInv x
leftInv (IsoSphereJoin n m) x =
  (λ i → sphere→Join≡ n m (join→Sphere≡ n m x i) i)
  ∙ joinSphereIso' n m .Iso.leftInv x

joinSphereEquiv∙ : (n m : ℕ) → join∙ (S₊∙ n) (S₊∙ m) ≃∙ S₊∙ (suc (n + m))
fst (joinSphereEquiv∙ n m) = isoToEquiv (IsoSphereJoin n m)
snd (joinSphereEquiv∙ n m) = refl

IsoSphereJoinPres∙ : (n m : ℕ)
  → Iso.fun (IsoSphereJoin n m) (inl (ptSn n)) ≡ ptSn (suc (n + m))
IsoSphereJoinPres∙ n m = refl

IsoSphereJoin⁻Pres∙ : (n m : ℕ)
  → Iso.inv (IsoSphereJoin n m) (ptSn (suc (n + m))) ≡ inl (ptSn n)
IsoSphereJoin⁻Pres∙ zero zero = push true true ⁻¹
IsoSphereJoin⁻Pres∙ zero (suc m) = refl
IsoSphereJoin⁻Pres∙ (suc n) m = refl

-- Associativity ⌣S
-- Preliminary lemma
⌣S-false : {n : ℕ} (x : S₊ n) → PathP (λ i → S₊ (+-comm n zero i)) (x ⌣S false) x
⌣S-false {n = zero} false = refl
⌣S-false {n = zero} true = refl
⌣S-false {n = suc zero} base = refl
⌣S-false {n = suc zero} (loop i) = refl
⌣S-false {n = suc (suc n)} north i = north
⌣S-false {n = suc (suc n)} south i = merid (ptSn (suc (+-zero n i))) i
⌣S-false {n = suc (suc n)} (merid a i) j =
  hcomp (λ k → λ {(i = i0) → north
                 ; (i = i1) → merid (ptSn (suc (+-zero n j))) (j ∨ ~ k)
                 ; (j = i1) → merid a i})
        (merid (⌣S-false a j) i)

assoc⌣S : {n m l : ℕ} (x : S₊ n) (y : S₊ m) (z : S₊ l)
  → PathP (λ i → S₊ (+-assoc n m l i))
           (x ⌣S (y ⌣S z)) ((x ⌣S y) ⌣S z)
assoc⌣S {n = zero} {m = m} false y z = refl
assoc⌣S {n = zero} {m = m} true y z = sym (IdR⌣S z)
assoc⌣S {n = suc zero} {m = m} base y z = sym (IdR⌣S z)
assoc⌣S {n = suc zero} {m = m} (loop i) y z j = help m y j i
  where
  help : (m : ℕ) (y : S₊ m)
    → Square (σS (y ⌣S z)) (cong (λ w → sphereFun↑ _⌣S_ w z) (σS y))
                (sym (IdR⌣S z)) (sym (IdR⌣S z))
  help zero false = refl
  help zero true = σS∙
  help (suc m) y =
      rUnit (σS (y ⌣S z))
    ∙ cong (σS (y ⌣S z) ∙_)
           (cong sym ((sym σS∙)
                ∙ congS σS (sym (IdR⌣S z))))
    ∙ sym (cong-∙ (λ k → sphereFun↑ _⌣S_ k z)
           (merid y)
           (sym (merid (ptSn (suc m)))))
assoc⌣S {n = suc (suc n)} {m = m} north y z k = north
assoc⌣S {n = suc (suc n)} {m = m} south y z k = north
assoc⌣S {n = suc (suc n)} {m = m} {l} (merid a i) y z j =
  help m y (assoc⌣S a y z) j i
  where
  help : (m : ℕ) (y : S₊ m)
    → PathP (λ i₁ → S₊ (suc (+-assoc n m l i₁)))
             (a ⌣S (y ⌣S z))
             ((a ⌣S y) ⌣S z)
    → SquareP (λ j i → S₊ (+-assoc (suc (suc n)) m l j))
              (σS (a ⌣S (y ⌣S z)))
              (λ i → (merid a i ⌣S y) ⌣S z)
              (λ _ → north) (λ _ → north)
  help zero false _ =
      (λ i j → σ (S₊∙ (suc (+-assoc n zero l i))) (lem i) j)
    ▷ rUnit _
     ∙ cong₂ _∙_ (congS σS (λ _ → (a ⌣S false) ⌣S z))
                 (cong sym (sym σS∙
                 ∙ congS σS
                     (sym (IdR⌣S z))))
     ∙ sym (cong-∙ (_⌣S z)
           (merid (a ⌣S false))
           (sym (merid (ptSn (suc (n + zero))))))
    where
    lem : PathP (λ i → S₊ (suc (+-assoc n zero l i)))
                (a ⌣S z) ((a ⌣S false) ⌣S z)
    lem = toPathP ((λ i → subst (S₊ ∘ suc)
                            (isSetℕ _ _ (+-assoc n zero l)
                                         (λ j → +-zero n (~ j) + l) i)
                            (a ⌣S z))
                  ∙ fromPathP (λ i → ⌣S-false a (~ i) ⌣S z))
  help zero true _ =
    (congS σS (IdL⌣S a) ∙ σS∙)
    ◁ (λ i j → north)
    ▷ (cong (cong (_⌣S z))
           (sym σS∙
         ∙ congS σS (sym (IdL⌣S a))))
  help (suc m) y q =
      (λ i j → σS (q i) j)
    ▷ (rUnit _
     ∙ cong₂ _∙_ refl
             (cong sym (sym σS∙ ∙ cong σS (sym (IdR⌣S z))))
     ∙ sym (cong-∙ (_⌣S z) (merid (a ⌣S y))
           (sym (merid (ptSn (suc (n + suc m)))))))

-- Goal: graded commutativity

-- To state it: we'll need iterated negations
-S^ : {k : ℕ} (n : ℕ) → S₊ k → S₊ k
-S^ zero x = x
-S^ (suc n) x = invSphere (-S^ n x)

-- The folowing is an explicit definition of -S^ (n · m) which is
-- often easier to reason about
-S^-expl : {k : ℕ} (n m : ℕ)
  → isEvenT n ⊎ isOddT n
  → isEvenT m ⊎ isOddT m
  → S₊ k → S₊ k
-S^-expl {k = zero} n m (inl x₁) q x = x
-S^-expl {k = zero} n m (inr x₁) (inl x₂) x = x
-S^-expl {k = zero} n m (inr x₁) (inr x₂) false = true
-S^-expl {k = zero} n m (inr x₁) (inr x₂) true = false
-S^-expl {k = suc zero} n m p q base = base
-S^-expl {k = suc zero} n m (inl x) q (loop i) = loop i
-S^-expl {k = suc zero} n m (inr x) (inl x₁) (loop i) = loop i
-S^-expl {k = suc zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-S^-expl {k = suc (suc k)} n m p q north = north
-S^-expl {k = suc (suc k)} n m p q south = north
-S^-expl {k = suc (suc k)} n m (inl x) q (merid a i) = σS a i
-S^-expl {k = suc (suc k)} n m (inr x) (inl x₁) (merid a i) = σS a i
-S^-expl {k = suc (suc k)} n m (inr x) (inr x₁) (merid a i) = σS a (~ i)

--  invSphere commutes with S^
invSphere-S^ : {k : ℕ} (n : ℕ) (x : S₊ k)
  → invSphere (-S^ n x) ≡ -S^ n (invSphere x)
invSphere-S^ zero x = refl
invSphere-S^ (suc n) x = cong invSphere (invSphere-S^ n x)

-S^² : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ n (-S^ n x) ≡ x
-S^² zero x = refl
-S^² (suc n) x =
  cong invSphere (sym (invSphere-S^ n (-S^ n x)))
  ∙ invSphere² _ (-S^ n (-S^ n x))
  ∙ -S^² n x

-S^Iso : {k : ℕ} (n : ℕ) → Iso (S₊ k) (S₊ k)
fun (-S^Iso n) = -S^ n
inv (-S^Iso n) = -S^ n
rightInv (-S^Iso n) = -S^² n
leftInv (-S^Iso n) = -S^² n

-S^-comp : {k : ℕ} (n m : ℕ) (x : S₊ k)
  → -S^ n (-S^ m x) ≡ -S^ (n + m) x
-S^-comp zero m x = refl
-S^-comp (suc n) m x = cong invSphere (-S^-comp n m x)

-S^·2 : {k : ℕ} (n : ℕ) (x : S₊ k) → -S^ (n + n) x ≡ x
-S^·2 zero x = refl
-S^·2 (suc n) x =
    cong invSphere (λ i → -S^ (+-comm n (suc n) i) x)
  ∙ invSphere² _ (-S^ (n + n) x)
  ∙ -S^·2 n x

-- technical transport lemma
private
  -S^-transp : {k : ℕ} (m : ℕ) (p : k ≡ m) (n : ℕ) (x : S₊ k)
    → subst S₊ p (-S^ n x) ≡ -S^ n (subst S₊ p x)
  -S^-transp =
    J> λ n x → transportRefl _
              ∙ sym (cong (-S^ n) (transportRefl x))

-- Iterated path inversion
sym^ : ∀ {ℓ} {A : Type ℓ} {x : A} (n : ℕ) → x ≡ x → x ≡ x
sym^ zero p = p
sym^ (suc n) p = sym (sym^ n p)

-- Interaction between -S^ and sym^
σS-S^ : {k : ℕ} (n : ℕ) (x : S₊ (suc k))
  → σS (-S^ n x) ≡ sym^ n (σS x)
σS-S^ {k = k} zero x = refl
σS-S^ {k = k} (suc n) x =
  σ-invSphere k _ ∙ cong sym (σS-S^ n x)

sphereFun↑-subst : {n m : ℕ} (k' k : ℕ) (p : k' ≡ k)
  → (f : S₊ n → S₊ m → S₊ k') (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → subst S₊ p (f x y)) x y
   ≡ subst S₊ (cong suc p) (sphereFun↑ f x y)
sphereFun↑-subst k' = J> λ f x y
  → (λ i → sphereFun↑ (λ x₁ y₁ → transportRefl (f x₁ y₁) i) x y)
   ∙ sym (transportRefl _)

sphereFun↑-invSphere : {n m k : ℕ}
  → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → invSphere' (f x y)) x y
   ≡ invSphere' (sphereFun↑ (λ x y → (f x y)) x y)
sphereFun↑-invSphere {n = n} {m = m} {k = k} f north y = refl
sphereFun↑-invSphere {n = n} {m = m} {k = k} f south y = refl
sphereFun↑-invSphere {n = n} {m = m} {k = k} f (merid a i) y j =
  lem k (f a y) j i
  where
  lem : (k : ℕ) (x : S₊ (suc k))
    → (σS (invSphere' x)) ≡ (cong invSphere' (σS x))
  lem k x =
    sym (cong-∙ invSphere' (merid x) (sym (merid (ptSn _)))
      ∙∙ cong (cong invSphere' (merid x) ∙_)
          (rCancel (merid (ptSn _)))
      ∙∙ (sym (rUnit _)
        ∙ sym (σ-invSphere k x)
        ∙ cong (σ (S₊∙ (suc k)))
           (sym (invSphere'≡ x))))

sphereFun↑^ : {n m k : ℕ} (l : ℕ)
  → (f : S₊ (suc n) → S₊ (suc m) → S₊ (suc k)) (x : S₊ _) (y : S₊ _)
  → sphereFun↑ (λ x y → -S^ l (f x y)) x y
   ≡ -S^ l (sphereFun↑ (λ x y → (f x y)) x y)
sphereFun↑^ zero f x y = refl
sphereFun↑^ (suc l) f x y =
    (λ i → sphereFun↑ (λ x₁ y₁ → invSphere'≡ (-S^ l (f x₁ y₁)) (~ i)) x y)
  ∙ sphereFun↑-invSphere (λ x₁ y₁ → (-S^ l (f x₁ y₁))) x y
  ∙ invSphere'≡ ((sphereFun↑ (λ x₁ y₁ → -S^ l (f x₁ y₁)) x y))
  ∙ cong invSphere (sphereFun↑^ l f x y)

S^-even : {k : ℕ} (n : ℕ) (x : S₊ k) → isEvenT n → -S^ n x ≡ x
S^-even zero x p = refl
S^-even (suc (suc n)) x p = invSphere² _ (-S^ n x) ∙ S^-even n x p

private
  move-transp-S^ : {k : ℕ} (n : ℕ) (p : k ≡ n) (m : ℕ)
    → (x : S₊ k) (y : S₊ n)
    → subst S₊ p (-S^ m x) ≡ y
    → subst S₊ (sym p) (-S^ m y) ≡ x
  move-transp-S^ =
    J> λ m x → J> transportRefl _
    ∙ cong (-S^ m) (transportRefl _)
    ∙ -S^² m x

  master-lem : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (coh : refl ≡ p)
    (q : p ≡ p)
    → Cube (λ j k → coh j (~ k)) (λ j k → coh j (~ k))
            (λ i k → q k i) (λ i k → q i (~ k))
            (λ j k → coh (~ k) j) λ j k → coh (~ k) j
  master-lem = J> λ q → λ i j k → sym≡flipSquare q j (~ k) i

  comm⌣S₁ : {m : ℕ} → (x : S¹) (y : S₊ (suc m))
    → (x ⌣S y)
     ≡ subst S₊ (+-comm (suc m) 1)
                (-S^ (suc m) (y ⌣S x))
  comm⌣S₁ {m = zero} x y =
      (main x y ∙ invSphere'≡ (y ⌣S x))
    ∙ sym (transportRefl (invSusp (y ⌣S x)))
    where
    pp-main : (x : S¹) → PathP (λ i → IdL⌣S {m = 1} x i
            ≡ IdL⌣S {m = 1} x i) (cong (x ⌣S_) loop) (sym (σS x))
    pp-main base i j = rCancel (merid base) (~ i) (~ j)
    pp-main (loop k) i j =
      master-lem _ (sym (rCancel (merid base)))
                   (λ j k → σS (loop j) k) k i j

    pp-help : (x : S¹) → PathP (λ i → IdL⌣S {m = 1} x i
            ≡ IdL⌣S {m = 1} x i)
                     (cong (x ⌣S_) loop) (cong invSphere' (σS x))
    pp-help x = pp-main x
      ▷ (rUnit _
      ∙∙ cong (sym (σS x) ∙_) (sym (rCancel (merid base)))
      ∙∙ sym (cong-∙ invSphere' (merid x) (sym (merid base))))

    main : (x y : S¹) → (x ⌣S y) ≡ invSphere' (y ⌣S x)
    main x base = IdL⌣S {m = 1} x
    main x (loop i) = flipSquare (pp-help x) i
  comm⌣S₁ {m = suc m} x y =
      (main-lem x y
     ∙ sym (transportRefl (invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
    ∙ sym (compSubstℕ {A = S₊} (cong suc (sym (+-comm (suc m) 1)))
                                (+-comm (suc (suc m)) 1) refl
       {x = invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)}))
    ∙ cong (subst S₊ (+-comm (suc (suc m)) 1))
        (cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
          (sym (S^-lem (suc m) (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)))
        ∙ -S^-transp _ (cong suc (sym (+-comm (suc m) 1)))
           (suc (suc m) + suc m)
           (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
        ∙ sym (-S^-comp (suc (suc m)) (suc m)
           (subst S₊ (cong suc (sym (+-comm (suc m) 1)))
             (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))))
    ∙ cong (subst S₊ (+-comm (suc (suc m)) 1)
         ∘ -S^ (suc (suc m)))
         ((sym (-S^-transp _ (cong suc (sym (+-comm (suc m) 1))) (suc m)
               (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x))
         ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) 1))))
               (sym (sphereFun↑^ (suc m)
                (λ x₂ x₃ →  (x₃ ⌣S x₂)) y x))
         ∙ sym (sphereFun↑-subst _ _ (sym (+-comm (suc m) 1))
           (λ x₂ x₃ →  (-S^ (suc m) (x₃ ⌣S x₂))) y x))
         ∙ cong (λ (s : S₊ (suc m) → S¹ → S₊ (suc m + 1))
                  → sphereFun↑ s y x)
                 (refl
               ∙ sym (funExt λ x → funExt λ y
               → sym (move-transp-S^ _ (+-comm (suc m) 1)
               (suc m) (x ⌣S y) (y ⌣S x)
                (sym (comm⌣S₁ y x)))
               ∙ refl)))
    where
    S^-lem : {k : ℕ} (m : ℕ) (x : S₊ k)
      → -S^ (suc m + m) x ≡ invSphere' x
    S^-lem m x =
         sym (invSphere'≡ (-S^ (m + m) x))
       ∙ cong invSphere' (-S^·2 m x)

    ⌣S-south : (x : S¹) → x ⌣S south ≡ north
    ⌣S-south base = refl
    ⌣S-south (loop i) j =
      (cong σS (sym (merid (ptSn (suc m))) )
      ∙ rCancel (merid (ptSn _))) j i

    PathP-main : (x : S¹) (a : S₊ (suc m))
      → PathP (λ i → IdL⌣S x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
          (sym (σS (x ⌣S a)))
    PathP-main base a j i = rCancel (merid north) (~ j) (~ i)
    PathP-main (loop k) a j i =
      hcomp (λ r → λ {(i = i0) → rCancel (merid north) j k
                     ; (i = i1) → compPath-filler'
                                   (cong σS (sym (merid (ptSn (suc m)))))
                                   (rCancel (merid north)) r j k
                     ; (j = i0) → σS (compPath-filler (merid a)
                                        (sym (merid (ptSn (suc m)))) (~ r) i) k
                     ; (j = i1) → σS (σS a k) (~ i)
                     ; (k = i0) → rCancel (merid north) (~ j) (~ i)
                     ; (k = i1) → rCancel (merid north) (~ j) (~ i)})
            (master-lem _ (sym (rCancel (merid north)))
             (λ i k → σS (loop i ⌣S a) k) k j i)

    pp : (x : S¹) (a : S₊ (suc m))
      → PathP (λ i → IdL⌣S x i ≡ ⌣S-south x i) (cong (x ⌣S_) (merid a))
          (cong invSphere' (σS (x ⌣S a)))
    pp x a = PathP-main x a
        ▷ (rUnit _
       ∙∙ cong (sym (σS (x ⌣S a)) ∙_) (sym (rCancel (merid north)))
       ∙∙ sym (cong-∙ invSphere' (merid (x ⌣S a)) (sym (merid north))))

    main-lem : (x : S¹) (y : S₊ (2 + m))
      → (x ⌣S y)
        ≡ invSphere' (sphereFun↑ (λ x₂ x₃ → x₃ ⌣S x₂) y x)
    main-lem x north = IdL⌣S x
    main-lem x south = ⌣S-south x
    main-lem x (merid a i) j = pp x a j i

  comm⌣S-lem : {n m : ℕ}
    → ((x : S₊ (suc n)) (y : S₊ (suc (suc m)))
       → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc n))
                              (-S^ (suc (suc m) · (suc n)) (y ⌣S x)))
    → (((x : S₊ (suc m)) (y : S₊ (suc (suc n)))
       → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc n)) (suc m))
                              (-S^ ((suc (suc n)) · (suc m)) (y ⌣S x))))
    → (((x : S₊ (suc n)) (y : S₊ (suc m))
       → (y ⌣S x) ≡ subst S₊ (sym (+-comm (suc m) (suc n)))
                              (-S^ ((suc n) · (suc m)) (x ⌣S y))))
    → (x : S₊ (suc (suc n))) (y : S₊ (suc (suc m)))
    → (x ⌣S y) ≡ subst S₊ (+-comm (suc (suc m)) (suc (suc n)))
                           (-S^ (suc (suc m) · (suc (suc n))) (y ⌣S x))
  comm⌣S-lem {n = n} {m = m} ind1 ind2 ind3 x y =
       cong (λ (s : S₊ (suc n) → S₊ (suc (suc m))
            → S₊ ((suc n) + (suc (suc m)))) → sphereFun↑ s x y)
            (funExt (λ x → funExt λ y
            → ind1 x y))
    ∙ (sphereFun↑-subst _ _ (+-comm (suc (suc m)) (suc n))
                            (λ x y → -S^ (suc (suc m) · suc n) (y ⌣S x)) x y
    ∙ cong (subst S₊ (cong suc (+-comm (suc (suc m)) (suc n))))
        (sphereFun↑^ (suc (suc m) · suc n)  (λ x y → y ⌣S x) x y
        ∙ cong (-S^ (suc (suc m) · suc n))
           (cong (λ (s : S₊ (suc n) → S₊ (suc (suc m))
                  → S₊ ((suc (suc m)) + (suc n))) → sphereFun↑ s x y)
             (funExt (λ x → funExt λ y →
              cong (λ (s : S₊ (suc m) → S₊ (suc n) → S₊ ((suc m) + (suc n)))
                    → sphereFun↑ s y x)
               (funExt λ x
                      → funExt λ y
                       → ind3 y x)
            ∙ sphereFun↑-subst _ _ (sym (+-comm (suc m) (suc n)))
                (λ x y → -S^ (suc n · suc m) (y ⌣S x)) y x
            ∙ cong (subst S₊ (cong suc (sym (+-comm (suc m) (suc n)))))
                   (sphereFun↑^ (suc n · suc m) (λ x y → (y ⌣S x)) y x)))
            ∙ sphereFun↑-subst _ _  (sym (cong suc (+-comm (suc m) (suc n))))
                ((λ x₁ x₂ →
                 (-S^ (suc n · suc m)
                      (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁)))) x y
            ∙ cong (subst S₊ (sym (cong (suc ∘ suc) (+-comm (suc m) (suc n)))))
                     ((sphereFun↑^ (suc n · suc m)
                       ((λ x₁ x₂ → (sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁))) x y
                    ∙ cong (-S^ (suc n · suc m)) (lem₃ x y)))))
    ∙ big-lem (suc n) (suc m)
        _ (λ i → suc (suc (+-comm (suc m) (suc n) (~ i))))
        _ (λ i → suc (+-comm (suc (suc m)) (suc n) i)) _
        (sym (+-comm (suc (suc m)) (suc (suc n))))
        (λ i → suc (+-comm (suc (suc n)) (suc m) i))
        (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
    ∙ sym (cong (subst S₊ (+-comm (suc (suc m)) (suc (suc n))))
           (cong (-S^ (suc (suc m) · suc (suc n)))
            ((λ i → sphereFun↑ (λ x y → ind2 x y i) y x)
           ∙ sphereFun↑-subst _ _
               (+-comm (suc (suc n)) (suc m))
                 (λ x y → -S^ (suc (suc n) · suc m) (y ⌣S x)) y x
           ∙ cong (subst S₊ (cong suc (+-comm (suc (suc n)) (suc m))))
              (sphereFun↑^ (suc (suc n) · suc m) (λ x y → y ⌣S x) y x)))))
      where
      ℕ-p : (n m : ℕ)
        → (suc m · suc n + suc n · m)
         ≡ (m + m) + ((n · m + n · m) + (suc n))
      ℕ-p n m =
        cong suc (cong (_+ (m + n · m)) (cong (n +_) (·-comm m (suc n)))
               ∙ sym (+-assoc n (m + n · m) _)
               ∙ +-comm n _
               ∙ cong (_+ n) (+-assoc (m + n · m) m (n · m)
                           ∙ cong (_+ (n · m))
                                (sym (+-assoc m (n · m) m)
                              ∙ cong (m +_) (+-comm (n · m) m)
                              ∙ +-assoc m m (n · m))
                              ∙ sym (+-assoc (m + m) (n · m) (n · m))))
        ∙ sym (+-suc (m + m + (n · m + n · m)) n)
        ∙ sym (+-assoc (m + m) (n · m + n · m) (suc n))

      ℕ-p2 : (n m : ℕ) → suc m · n + n · m + 1 ≡ (((n · m) + (n · m)) + (suc n))
      ℕ-p2 n m = (λ _ → ((n + m · n) + n · m) + 1)
        ∙ cong (_+ 1) (sym (+-assoc n (m · n) (n · m))
                      ∙ (λ i → +-comm n ((·-comm m n i) + n · m) i))
        ∙ sym (+-assoc (n · m + n · m) n 1)
        ∙ cong (n · m + n · m +_) (+-comm n 1)

      big-lem : (n m : ℕ) {x : ℕ} (y : ℕ) (p : x ≡ y) (z : ℕ) (s : y ≡ z)
                (d : ℕ) (r : z ≡ d) (t : x ≡ d)
         (a : S₊ x)
        → subst S₊ s (-S^ (suc m · n) (subst S₊ p (-S^ (n · m) (invSphere' a))))
        ≡ subst S₊ (sym r)
            (-S^ (suc m · suc n)
             (subst S₊ t (-S^ (suc n · m) a)))
      big-lem n m =
        J> (J> (J> λ t a
        → transportRefl _
        ∙ cong (-S^ (n + m · n)) (transportRefl _)
        ∙ sym (transportRefl _
             ∙ cong (-S^ (suc m · suc n))
                    ((λ i → subst S₊ (isSetℕ _ _ t refl i) (-S^ (m + n · m) a))
                 ∙ transportRefl (-S^ (m + n · m) a) )
             ∙ -S^-comp (suc m · suc n) (suc n · m) a
             ∙ ((funExt⁻ (cong -S^ (ℕ-p n m)) a
               ∙ (sym (-S^-comp (m + m) _ a)
                ∙ -S^·2 m (-S^ (n · m + n · m + suc n) a))
               ∙ funExt⁻ (cong -S^ (sym (ℕ-p2 n m))) a)
              ∙ sym (-S^-comp (suc m · n + n · m) 1 a)
              ∙ cong (-S^ (suc m · n + n · m))
                 (sym (invSphere'≡ a)))
             ∙ sym (-S^-comp (suc m · n) (n · m) (invSphere' a)) )))

      lem₁ : (x :  S₊ (2 + n))
        → sphereFun↑ (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x north ≡ north
      lem₁ north = refl
      lem₁ south = refl
      lem₁ (merid a i) j = rCancel (merid north) j i

      lem₂ : (x :  S₊ (2 + n))
        → sphereFun↑ (λ x₂ x₃
          → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x south
          ≡ north
      lem₂ north = refl
      lem₂ south = refl
      lem₂ (merid a i) j = rCancel (merid north) j i

      lem₃ : (x : S₊ (2 + n)) (y : S₊ (2 + m))
         → (sphereFun↑ (λ x₁ x₂
            → sphereFun↑ (λ x₃ y₁ → y₁ ⌣S x₃) x₂ x₁) x y)
          ≡ invSphere' (sphereFun↑ (λ x₁ y₂ → y₂ ⌣S x₁) y x)
      lem₃ x north = lem₁ x
      lem₃ x south = lem₂ x
      lem₃ x (merid a i) j = h j i
        where
        main : (x : _) → PathP (λ i → lem₁ x i ≡ lem₂ x i)
               (cong (sphereFun↑ (λ x₂ x₃
                → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x )
                 (merid a))
               (sym (σS (x ⌣S a)))
        main north = cong sym (sym (rCancel (merid north)))
        main south = cong sym (sym (rCancel (merid north)))
        main (merid z i) j k =
          master-lem _
            (sym (rCancel (merid north)))
            (cong (λ x → σS (x ⌣S a)) (merid z)) i j k

        h : PathP (λ i → lem₁ x i ≡ lem₂ x i)
                  (cong (sphereFun↑
                   (λ x₂ x₃ → sphereFun↑ (λ x₄ y₁ → y₁ ⌣S x₄) x₃ x₂) x)
                    (merid a)) (cong invSphere' (σS (x ⌣S a)))
        h = main x
          ▷ ((rUnit _ ∙ cong (sym (σS (x ⌣S a)) ∙_)
              (sym (rCancel (merid north))))
             ∙ sym (cong-∙ invSphere'
                (merid (x ⌣S a)) (sym (merid (ptSn _)))))

  comm⌣S₀ : (x : Bool) (m : ℕ) (y : S₊ m)
    → PathP (λ i → S₊ (+-zero m (~ i))) (x ⌣S y) (y ⌣S x)
  comm⌣S₀ false =
    elim+2 (λ { false → refl ; true → refl})
           (λ { base → refl ; (loop i) → refl})
      ind
    where
    ind : (n : ℕ) →
        ((y : S₊ (suc n)) →
         PathP (λ i → S₊ (suc (+-zero n (~ i)))) y (y ⌣S false)) →
        (y : Susp (S₊ (suc n))) →
        PathP (λ i → Susp (S₊ (suc (+-zero n (~ i))))) y (y ⌣S false)
    ind n p north i = north
    ind n p south i = merid (ptSn (suc (+-zero n (~ i)))) (~ i)
    ind n p (merid a j) i =
      comp (λ k → Susp (S₊ (suc (+-zero n (~ i ∨ ~ k)))))
           (λ r →
           λ {(i = i0) → merid a j
            ; (i = i1) →
              σ (S₊∙ (suc (+-zero n (~ r)))) (p a r) j
            ; (j = i0) → north
            ; (j = i1) → merid (ptSn (suc (+-zero n (~ i ∨ ~ r)))) (~ i)})
           (compPath-filler (merid a) (sym (merid (ptSn _))) i j)
  comm⌣S₀ true m y = (λ i → ptSn (+-zero m (~ i))) ▷ (sym (IdL⌣S y))

-- Graded commutativity
comm⌣S : {n m : ℕ} (x : S₊ n) (y : S₊ m)
  → (x ⌣S y) ≡ subst S₊ (+-comm m n) (-S^ (m · n) (y ⌣S x))
comm⌣S {n = zero} {m = m} x y =
  sym (fromPathP (symP {A = λ i → S₊ (+-zero m i)} ((comm⌣S₀ x m y))))
  ∙ sym (cong (subst S₊ (+-zero m))
        ((λ i → -S^ (0≡m·0 m (~ i)) (y ⌣S x))))
comm⌣S {n = suc n} {m = zero} x y =
  sym (fromPathP (comm⌣S₀ y (suc n) x))
  ∙ (λ i → subst S₊ (isSetℕ _ _
             (sym (+-comm (suc n) zero))
             (+-comm zero (suc n)) i) (y ⌣S x))
comm⌣S {n = suc zero} {m = suc m} x y =
    comm⌣S₁ x y
  ∙ cong (subst S₊ (+-comm (suc m) 1))
     λ i → -S^ (·-identityʳ (suc m) (~ i)) (y ⌣S x)
comm⌣S {n = suc (suc n)} {m = suc zero} x y =
    sym (substSubst⁻ S₊ (+-comm 1 (suc (suc n))) (x ⌣S y))
  ∙ cong (subst S₊ (+-comm 1 (suc (suc n))))
        ((λ i → subst S₊ (isSetℕ _ _
           (sym (+-comm 1 (suc (suc n)))) (+-comm (suc (suc n)) 1) i)
           (x ⌣S y))
      ∙ (sym (sym
         (-S^-transp _ (+-comm (suc (suc n)) 1) (1 · suc (suc n))
           (-S^ (suc (suc n)) (x ⌣S y)))
            ∙ cong (subst S₊ (+-comm (suc (suc n)) 1))
               (cong (-S^ (1 · suc (suc n)))
                 (λ i → -S^ (·-identityˡ (suc (suc n)) (~ i)) (x ⌣S y))
              ∙ -S^² (1 · suc (suc n)) (x ⌣S y)))))
  ∙ sym (cong (subst S₊ (+-comm 1 (suc (suc n)))
             ∘ -S^ (1 · suc (suc n))) (comm⌣S₁ y x))
comm⌣S {n = suc (suc n)} {m = suc (suc m)} x y =
  comm⌣S-lem comm⌣S comm⌣S
    (λ x y → (sym (cong (subst S₊ (sym (+-comm (suc m) (suc n))))
               (sym (-S^-transp _ (+-comm (suc m) (suc n))
                 (suc n · suc m) (-S^ (suc m · suc n) (y ⌣S x)))
             ∙ cong (subst S₊ (+-comm (suc m) (suc n)))
                (cong (-S^ (suc n · suc m))
                    (λ i → -S^ (·-comm (suc m) (suc n) i) (y ⌣S x))
                  ∙ -S^² (suc n · suc m) (y ⌣S x) ))
            ∙ subst⁻Subst S₊ (+-comm (suc m) (suc n)) (y ⌣S x) ))
      ∙ sym (cong (subst S₊ (sym (+-comm (suc m) (suc n)))
                 ∘ -S^ (suc n · suc m))
         (comm⌣S x y))) x y

-- Additional properties in low dimension:
diag⌣ : {n : ℕ} (x : S₊ (suc n)) → x ⌣S x ≡ ptSn _
diag⌣ {n = zero} base = refl
diag⌣ {n = zero} (loop i) j = help j i
  where
  help : cong₂ _⌣S_ loop loop ≡ refl
  help = cong₂Funct _⌣S_ loop loop
       ∙ sym (rUnit _)
       ∙ rCancel (merid base)
diag⌣ {n = suc n} north = refl
diag⌣ {n = suc n} south = refl
diag⌣ {n = suc n} (merid a i) j = help j i
  where
  help : cong₂ _⌣S_ (merid a) (merid a) ≡ refl
  help = cong₂Funct _⌣S_ (merid a) (merid a)
       ∙ sym (rUnit _)
       ∙ flipSquare (cong IdL⌣S (merid a))

⌣₁,₁-distr : (a b : S¹) → (b * a) ⌣S b ≡ a ⌣S b
⌣₁,₁-distr a base = refl
⌣₁,₁-distr a (loop i) j = lem j i
  where
  lem : cong₂ (λ (b1 b2 : S¹) → (b1 * a) ⌣S b2) loop loop
     ≡ (λ i → a ⌣S loop i)
  lem = (cong₂Funct (λ (b1 b2 : S¹) → (b1 * a) ⌣S b2) loop loop
      ∙ cong₂ _∙_ (PathP→compPathR
                   (flipSquare (cong (IdL⌣S {n = 1} {1} ∘ (_* a)) loop))
                ∙ cong₂ _∙_ refl (sym (lUnit _))
                ∙ rCancel _)
                  refl
      ∙ sym (lUnit _))

⌣₁,₁-distr' : (a b : S¹) → (a * b) ⌣S b ≡ a ⌣S b
⌣₁,₁-distr' a b = cong (_⌣S b) (commS¹ a b) ∙ ⌣₁,₁-distr a b

⌣Sinvₗ : {n m : ℕ} (x : S₊ (suc n)) (y : S₊ (suc m))
  → (invSphere x) ⌣S y ≡ invSphere (x ⌣S y)
⌣Sinvₗ {n = zero} {m} base y = merid (ptSn (suc m))
⌣Sinvₗ {n = zero} {m} (loop i) y j = lem j i
  where
  lem : Square (σS y ⁻¹)
               (λ i → invSphere (loop i ⌣S y))
               (merid (ptSn (suc m))) (merid (ptSn (suc m)))
  lem = sym (cong-∙ invSphere' (merid y) (sym (merid (ptSn (suc m))))
      ∙ cong₂ _∙_ refl (rCancel _)
      ∙ sym (rUnit _))
      ◁ (λ j i → invSphere'≡ (loop i ⌣S y) j)
⌣Sinvₗ {n = suc n} {m} north y = merid (ptSn (suc (n + suc m)))
⌣Sinvₗ {n = suc n} {m} south y = merid (ptSn (suc (n + suc m)))
⌣Sinvₗ {n = suc n} {m} (merid a i) y j = lem j i
  where
  p = ptSn (suc (n + suc m))

  lem : Square (σS (a ⌣S y) ⁻¹)
               (λ i → invSphere (merid a i ⌣S y))
               (merid p) (merid p)
  lem = (sym (cong-∙ invSphere' (merid (a ⌣S y)) (sym (merid p))
      ∙ cong₂ _∙_ refl (rCancel _)
      ∙ sym (rUnit _)))
      ◁ λ j i → invSphere'≡ (merid a i ⌣S y) j

⌣Sinvᵣ : {n m : ℕ} (x : S₊ (suc n)) (y : S₊ (suc m))
      → x ⌣S (invSphere y) ≡ invSphere (x ⌣S y)
⌣Sinvᵣ {n = n} {m} x y =
    comm⌣S x (invSphere y)
  ∙ cong (subst S₊ (+-comm (suc m) (suc n)))
         (cong (-S^ (suc m · suc n)) (⌣Sinvₗ y x)
         ∙ sym (invSphere-S^ (suc m · suc n) (y ⌣S x)))
       ∙ -S^-transp _ (+-comm (suc m) (suc n)) 1
                      (-S^ (suc m · suc n) (y ⌣S x))
       ∙ cong invSphere
           (cong (subst S₊ (+-comm (suc m) (suc n)))
             (cong (-S^ (suc m · suc n)) (comm⌣S y x)
             ∙ sym (-S^-transp _ (+-comm (suc n) (suc m))
                      (suc m · suc n)
                      (-S^ (suc n · suc m) (x ⌣S y)))
             ∙ cong (subst S₊ (+-comm (suc n) (suc m)))
                    ((cong (-S^ (suc m · suc n))
                      (λ i → -S^ (·-comm (suc n) (suc m) i) (x ⌣S y)))
                   ∙ -S^² (suc m · suc n) (x ⌣S y))
                   ∙ cong (λ p → subst S₊ p (x ⌣S y))
                        (isSetℕ _ _ (+-comm (suc n) (suc m))
                                     (+-comm (suc m) (suc n) ⁻¹)))
             ∙ subst⁻Subst S₊ (+-comm (suc m) (suc n) ⁻¹) (x ⌣S y))

-- Interaction between ⌣S, SuspS¹→S² and SuspS¹→S²
SuspS¹→S²-S¹×S¹→S² : (a b : S¹)
  → SuspS¹→S² (a ⌣S b) ≡ S¹×S¹→S² a b
SuspS¹→S²-S¹×S¹→S² base b = refl
SuspS¹→S²-S¹×S¹→S² (loop i) b j = main b j i
  where
  lem : (b : _) → cong SuspS¹→S² (merid b) ≡ (λ j → S¹×S¹→S² (loop j) b)
  lem base = refl
  lem (loop i) = refl

  main : (b : _) → cong SuspS¹→S² (σS b) ≡ (λ j → S¹×S¹→S² (loop j) b)
  main b = cong-∙ SuspS¹→S² (merid b) (merid base ⁻¹)
         ∙ sym (rUnit _)
         ∙ lem b
