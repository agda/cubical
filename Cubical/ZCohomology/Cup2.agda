{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Cup2 where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties

open import Cubical.Foundations.Transport

open import Cubical.HITs.S1 hiding (encode ; decode ; _·_)
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm ; +-assoc to ℤ+-assoc) hiding (-_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level

isOfHLevelΩ→isOfHLevel :
  ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → ((x : A) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (2 + n) A
isOfHLevelΩ→isOfHLevel zero hΩ x y =
  J (λ y p → (q : x ≡ y) → p ≡ q) (hΩ x refl)
isOfHLevelΩ→isOfHLevel (suc n) hΩ x y =
  J (λ y p → (q : x ≡ y) → isOfHLevel (suc n) (p ≡ q)) (hΩ x refl)

contrMin : (n : ℕ) → isContr (coHomK-ptd (suc n) →∙ coHomK-ptd n)
fst (contrMin zero) = (λ _ → 0) , refl
snd (contrMin zero) (f , p) =
  Σ≡Prop (λ f → isSetInt _ _)
         (funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 isSetInt) _ _)
                 (toPropElim (λ _ → isSetInt _ _) (sym p))))
fst (contrMin (suc n)) = (λ _ → 0ₖ _) , refl
snd (contrMin (suc n)) f =
  ΣPathP ((funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelSuc (3 + n) (isOfHLevelTrunc (3 + n))) _ _)
         (sphereElim _ (λ _ → isOfHLevelTrunc (3 + n) _ _) (sym (snd f))))) ,
         λ i j → snd f (~ i ∨ j))

contrMin2 : (n : ℕ) → isContr (S₊∙ (suc n) →∙ coHomK-ptd n)
fst (contrMin2 zero) = (λ _ → 0) , refl
snd (contrMin2 zero) (f , p) =
  Σ≡Prop (λ f → isSetInt _ _)
         (funExt (toPropElim (λ _ → isSetInt _ _) (sym p)))
fst (contrMin2 (suc n)) = (λ _ → 0ₖ _) , refl
snd (contrMin2 (suc n)) (f , p) =
  ΣPathP ((funExt (sphereElim _ (λ _ → isOfHLevelTrunc (3 + n) _ _) (sym p)))
  , λ i j → p (~ i ∨ j))

ΩfunExtIso : (A B : Pointed₀) → Iso (typ (Ω (A →∙ B ∙))) (A →∙ Ω B)
fst (fun (ΩfunExtIso A B) p) x = funExt⁻ (cong fst p) x
snd (fun (ΩfunExtIso A B) p) i j = snd (p j) i
fst (inv' (ΩfunExtIso A B) (f , p) i) x = f x i
snd (inv' (ΩfunExtIso A B) (f , p) i) j = p j i
fst (rightInv (ΩfunExtIso A B) (f , p) i) x = f x
snd (rightInv (ΩfunExtIso A B) (f , p) i) j = p j
fst (leftInv (ΩfunExtIso A B) p i j) y = fst (p j) y
snd (leftInv (ΩfunExtIso A B) p i j) k = snd (p j) k

open import Cubical.Foundations.Univalence
pointedEquiv→Path : {A B : Pointed₀} (e : fst A ≃ fst B) → fst e (snd A) ≡ snd B → A ≡ B
fst (pointedEquiv→Path e p i) = ua e i
snd (pointedEquiv→Path {A = A} e p i) = hcomp (λ k → λ {(i = i0) → snd A ; (i = i1) → (transportRefl (fst e (snd A)) ∙ p) k}) (transp (λ j → ua e (i ∧ j)) (~ i) (snd A))

ind₂ : {A : Pointed₀} (n : ℕ) → Iso (A →∙ Ω (coHomK-ptd (suc n))) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
fst (fun (ind₂ n) (f , p) i) x = f x i
snd (fun (ind₂ n) (f , p) i) j = p j i
fst (inv' (ind₂ n) p) x = funExt⁻ (cong fst p) x
snd (inv' (ind₂ n) p) i j = snd (p j) i
rightInv (ind₂ n) p = refl
leftInv (ind₂ n) (f , p) = refl

taha : {A : Pointed₀} (n : ℕ) (f : A →∙ coHomK-ptd (suc n)) → Iso (typ A → coHomK (suc n)) (typ A → coHomK (suc n))
fun (taha n (f , p)) g a = g a +ₖ f a
inv' (taha n (f , p)) g a = g a -ₖ f a
rightInv (taha n (f , p)) g =
  funExt λ x → sym (assocₖ (suc n) (g x) (-ₖ (f x)) (f x)) ∙∙ cong (g x +ₖ_) (lCancelₖ (suc n) (f x)) ∙∙ rUnitₖ (suc n) (g x)
leftInv (taha n (f , p)) g =
  funExt λ x → sym (assocₖ (suc n) (g x) (f x) (-ₖ (f x))) ∙∙ cong (g x +ₖ_) (rCancelₖ (suc n) (f x)) ∙∙ rUnitₖ (suc n) (g x)


ind₁ : {A : Pointed₀} (n : ℕ) (f : A →∙ coHomK-ptd (suc n)) → (A →∙ coHomK-ptd (suc n) ∙) ≡ ((A →∙ coHomK-ptd (suc n) , f))
ind₁ {A  = A} n (f , p) = pointedEquiv→Path (Σ-cong-equiv (isoToEquiv (taha n (f , p))) λ g → pathToEquiv λ i → (cong ((g (snd A)) +ₖ_) p ∙ rUnitₖ (suc n) (g (snd A))) (~ i) ≡ 0ₖ (suc n))
                          (ΣPathP ((funExt (λ x → lUnitₖ (suc n) (f x)))
                          , (toPathP ((λ j → transp (λ i → lUnitₖ (suc n) (f (snd A)) i ≡ ∣ ptSn (suc n) ∣) i0
                                                   (transp
                                                    (λ i →
                                                       hcomp
                                                       (doubleComp-faces (λ _ → ∣ ptSn (suc n) ∣ +ₖ f (snd A))
                                                        (rUnitₖ (suc n) ∣ ptSn (suc n) ∣) (~ i ∧ ~ j))
                                                       (∣ ptSn (suc n) ∣ +ₖ p (~ i ∧ ~ j))
                                                       ≡ ∣ ptSn (suc n) ∣)
                                                    j λ i → hcomp
                                                       (doubleComp-faces (λ _ → ∣ ptSn (suc n) ∣ +ₖ f (snd A))
                                                        (rUnitₖ (suc n) ∣ ptSn (suc n) ∣) (i ∨ ~ j))
                                                       (∣ ptSn (suc n) ∣ +ₖ p (i ∨ ~ j))))
                                                    ∙∙ (λ j → transp (λ i → lUnitₖ (suc n) (f (snd A)) (i ∨ j) ≡ ∣ ptSn (suc n) ∣) j
                                                                      ((λ i → lUnitₖ (suc n) (f (snd A)) (~ i ∧ j)) ∙∙ (λ i → ∣ ptSn (suc n) ∣ +ₖ p i) ∙∙ (rUnitₖ (suc n) ∣ ptSn (suc n) ∣)))
                                                    ∙∙ helper n (f (snd A)) (sym p)))))
  where
  helper : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ (suc n) ≡ x) → (sym (lUnitₖ (suc n) x) ∙∙ cong (0ₖ (suc n) +ₖ_) (sym p) ∙∙ rUnitₖ (suc n) (0ₖ _)) ≡ sym p
  helper zero x =
    J (λ x p → (sym (lUnitₖ 1 x) ∙∙ cong (0ₖ 1 +ₖ_) (sym p) ∙∙ rUnitₖ 1 (0ₖ _)) ≡ sym p)
      (sym (rUnit refl))
  helper (suc n) x =
    J (λ x p → (sym (lUnitₖ (suc (suc n)) x) ∙∙ cong (0ₖ (suc (suc n)) +ₖ_) (sym p) ∙∙ rUnitₖ (suc (suc n)) (0ₖ _)) ≡ sym p)
      (sym (rUnit refl))


hlevStep₁ : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
                                    → isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
hlevStep₁ n m hlev =
  isOfHLevelΩ→isOfHLevel m λ f → subst (λ x → isOfHLevel (suc m) (typ (Ω x))) (ind₁ n f) hlev
  
hlevStep₂ : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ Ω (coHomK-ptd (suc n))) → isOfHLevel (suc m) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
hlevStep₂ n m hlev = isOfHLevelRetractFromIso (suc m) (invIso (ind₂ n)) hlev

hlevStep₃ :  {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ coHomK-ptd n) → isOfHLevel (suc m) (A →∙ Ω (coHomK-ptd (suc n)))
hlevStep₃ {A = A} n m hlev = subst (isOfHLevel (suc m)) (λ i → A →∙ pointedEquiv→Path {A = Ω (coHomK-ptd (suc n))} {B = coHomK-ptd n} (invEquiv Kn≃ΩKn+1) (ΩKn+1→Kn-refl n) (~ i)) hlev

hlevTotal : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ coHomK-ptd n) → isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
hlevTotal n m hlev = hlevStep₁ n m (hlevStep₂ n m (hlevStep₃ n m hlev))

wow : ∀ n m → isOfHLevel (2 + n) (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + m)))
wow zero m = hlevTotal m 0 (isContr→isProp (contrMin m))
wow (suc n) m = hlevTotal (suc (n + m)) (suc n) (wow n m)

wow2 : ∀ n m → isOfHLevel (2 + n) (S₊∙ (suc m) →∙ coHomK-ptd (suc (n + m)))
wow2 zero m = hlevTotal m 0 (isContr→isProp (contrMin2 m))
wow2 (suc n) m = hlevTotal (suc (n + m)) (suc n) (wow2 n m)

isOfHLevel→∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) → isOfHLevel n (fst B) → isOfHLevel n (A →∙ B)
isOfHLevel→∙ n hlev = isOfHLevelΣ n (isOfHLevelΠ n (λ _ → hlev)) λ x → isOfHLevelPath n hlev _ _


_+nice_ : ℕ → ℕ → ℕ
zero +nice y = y
suc x +nice zero = suc x
suc x +nice suc y = suc (suc (x + y))

^ₖ : {n : ℕ} (m : Int) → coHomK n → coHomK n
^ₖ {n = n} (pos zero) x = 0ₖ _
^ₖ {n = n} (pos (suc m)) x = x +ₖ ^ₖ (pos m) x
^ₖ {n = n} (negsuc zero) x = -ₖ x
^ₖ {n = n} (negsuc (suc m)) x = ^ₖ (negsuc m) x -ₖ x

^ₖ-base : {n : ℕ} (m : Int) → ^ₖ m (0ₖ n) ≡ 0ₖ n
^ₖ-base (pos zero) = refl
^ₖ-base (pos (suc n)) = cong (0ₖ _ +ₖ_) (^ₖ-base (pos n)) ∙ rUnitₖ _ (0ₖ _)
^ₖ-base {n = zero} (negsuc zero) = refl
^ₖ-base {n = suc zero} (negsuc zero) = refl
^ₖ-base {n = suc (suc k)} (negsuc zero) = refl
^ₖ-base {n = zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))
^ₖ-base {n = suc zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))
^ₖ-base {n = suc (suc k)} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))

k : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + suc m))
k zero m base = (λ _ → 0ₖ _) , refl
k zero m (loop i) = (λ x → Kn→ΩKn+1 _ x i) , (λ j → Kn→ΩKn+10ₖ _ j i)
fst (k (suc n) m north) _ = 0ₖ _
snd (k (suc n) m north) = refl
fst (k (suc n) m south) _ = 0ₖ _
snd (k (suc n) m south) = refl
fst (k (suc n) m (merid a i)) x = Kn→ΩKn+1 _ (k n m a .fst x) i
snd (k (suc n) m (merid a i)) j =
  (cong (Kn→ΩKn+1 (suc (n + suc m))) (k n m a .snd)
  ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i

open import Cubical.Foundations.Equiv.HalfAdjoint

f : Iso Int (typ ((Ω^ 2) (coHomK-ptd 2)))
f = compIso (Iso-Kn-ΩKn+1 0) (invIso (congIso (invIso (Iso-Kn-ΩKn+1 1))))

-help : {m : ℕ} (n : ℕ) → S₊ (suc m) → S₊ (suc m)
-help {m = zero} n base = base
-help {m = zero} n (loop i) = loop (~ i)
-help {m = suc m} n north = north
-help {m = suc m} n south = north
-help {m = suc m} zero (merid a i) = (merid a ∙ sym (merid (ptSn (suc m)))) i
-help {m = suc m} (suc zero) (merid a i) = (merid (ptSn (suc m)) ∙ sym (merid a)) i
-help {m = suc m} (suc (suc n)) (merid a i) = -help n (merid a i)

open import Cubical.Foundations.Path
pathalg : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ j → PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j))) (λ k → q (~ j ∧ k)) λ k → p (j ∨ k)) (sym P) (flipSquare P)
pathalg {A = A} x y = J (λ y p → (q : x ≡ y) → (P : Square p q refl refl) →
      PathP
      (λ j →
         PathP (λ i → Path A (p (i ∧ j)) (q (i ∨ ~ j)))
         (λ k₁ → q (~ j ∧ k₁)) (λ k₁ → p (j ∨ k₁)))
      (sym P) (flipSquare P))
        λ q → J (λ q P → PathP
      (λ j →
         PathP (λ i → Path A x (q (i ∨ ~ j)))
         (λ k₁ → q (~ j ∧ k₁)) refl)
      (λ i → P (~ i)) λ i j → P j i)
        refl

inst : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → sym P ≡ flipSquare P
inst x = pathalg x x refl refl

pathalg2 : ∀ {ℓ} {A : Type ℓ} (x y : A) → (p q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ i → PathP (λ j → p i ≡ q (~ i)) ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j))) ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
                   (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
                   (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p))
pathalg2 x y = J (λ y p → (q : x ≡ y) (P : Square p q refl refl)
          → PathP (λ i → PathP (λ j → p i ≡ q (~ i)) ((λ j → p (i ∨ j)) ∙ (λ j → q (~ i ∨ ~ j))) ((λ j → p (i ∧ ~ j)) ∙ (λ j → q (~ i ∧ j))))
                   (sym (rUnit p) ∙∙ P ∙∙ lUnit _)
                   (sym (lUnit (sym q)) ∙∙ (λ i j → P (~ i) (~ j)) ∙∙ rUnit (sym p)))
                 λ q → J (λ q P → PathP
      (λ i →
         (λ j → x) ∙ (λ j → q (~ i ∨ ~ j)) ≡
         (λ j → x) ∙ (λ j → q (~ i ∧ j)))
      ((λ i → rUnit refl (~ i)) ∙∙ P ∙∙ lUnit q)
      ((λ i → lUnit (λ i₁ → q (~ i₁)) (~ i)) ∙∙ (λ i j → P (~ i) (~ j))
       ∙∙ rUnit refl)) refl


inst2 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → P ≡ λ i j → P (~ i) (~ j)
inst2 x P =
  transport (λ i → doubleCompPath-filler (sym (rUnit refl)) P (lUnit refl) (~ i) ≡ doubleCompPath-filler (sym (rUnit refl))
            (λ i j → P (~ i) (~ j)) (lUnit refl) (~ i)) (pathalg2 _ _ refl refl P)

inst3 : ∀ {ℓ} {A : Type ℓ} (x : A) → (P : Square (refl {x = x}) refl refl refl) → flipSquare P ≡ λ i j → P i (~ j)
inst3 x P = sym (inst x P) ∙ sym (inst2 x (cong sym P))

inst4 : ∀ {ℓ} {A : Type ℓ} {x : A} → (P : Square (refl {x = x}) refl refl refl) → sym P ≡ cong sym P
inst4 P = inst _ _ ∙ inst3 _ P


{-
  hcomp (λ k → λ {(r = i0) → p (j ∨ ~ k) i
                 ; (r = i1) → p (~ i) j
                 ; (i = i0) → {!!}
                 ; (i = i1) → {!!}
                 ; (j = i0) → {!!}
                 ; (j = i1) → {!!}})
        {!!} -}
{-
p ((k ∧ ~ i) ∨ (~ k ∧ j)) ((k ∧ j) ∨ (~ k ∧ i))
r = i0 ⊢ p j i
r = i1 ⊢ sym p i j
i = i0 ⊢ refl j
i = i1 ⊢ refl j
j = i0 ⊢ x
j = i1 ⊢ x
-}

open import Cubical.Data.Bool
open import Cubical.Data.Empty
is-even : ℕ → Type
is-even zero = Unit
is-even (suc zero) = ⊥
is-even (suc (suc n)) = is-even n

is-odd : ℕ → Type
is-odd zero = ⊥
is-odd (suc zero) = Unit
is-odd (suc (suc x)) = is-odd x

even∨odd : (x : ℕ) → is-even x ⊎ is-odd x
even∨odd zero = inl tt
even∨odd (suc zero) = inr tt
even∨odd (suc (suc x)) = even∨odd x

prop-help : (m : ℕ) → isProp (is-even m ⊎ is-odd m)
prop-help zero (inl x) (inl x) = refl
prop-help (suc zero) (inr x) (inr x) = refl
prop-help (suc (suc m)) = prop-help m

-ₖ2 : {m : ℕ} (n : ℕ) → coHomK m → coHomK m
-ₖ2 {m = zero} zero x = x
-ₖ2 {m = zero} (suc zero) x = -ₖ x
-ₖ2 {m = zero} (suc (suc n)) x = -ₖ2 n x
-ₖ2 {m = suc m} n = trMap (-help n)


∪-help : (n m : ℕ) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-help-pt : (m : ℕ) → (a : _) → ∪-help zero m base a ≡ 0ₖ _
∪-help-pt-l : (m : ℕ) → (a : _) → ∪-help m zero a base ≡ 0ₖ _
∪-help zero zero base y = 0ₖ _
∪-help zero zero (loop i) base = 0ₖ _
∪-help zero zero (loop i) (loop j) =
  hcomp (λ k → λ {(j = i0) → 0ₖ 2
                 ; (j = i1) → ∣ merid base (~ k) ∣
                 ; (i = i0) → ∣ merid base (~ k ∧ j) ∣
                 ; (i = i1) → ∣ merid base (~ k ∧ j) ∣})
        ∣ merid (loop i) j ∣
∪-help zero (suc m) base y = 0ₖ _
∪-help zero (suc m) (loop i) north = 0ₖ _
∪-help zero (suc m) (loop i) south = 0ₖ _
∪-help zero (suc m) (loop i) (merid a j) =
  (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (sym (∪-help-pt m a) ∙∙ cong (λ x → ∪-help zero m x a) loop ∙∙ (∪-help-pt m a)) ∙∙  Kn→ΩKn+10ₖ _) i j
∪-help (suc n) zero x base = 0ₖ _
∪-help (suc n) zero north (loop i₁) = 0ₖ _
∪-help (suc n) zero south (loop i₁) = 0ₖ _
∪-help (suc n) zero (merid a i) (loop j) =
  (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (sym (∪-help-pt-l n a) ∙∙ cong (λ x → ∪-help n zero a x) loop ∙∙ ∪-help-pt-l n a) ∙∙  Kn→ΩKn+10ₖ _) i j
∪-help (suc n) (suc m) north y = 0ₖ _
∪-help (suc n) (suc m) south y = 0ₖ _
∪-help (suc n) (suc m) (merid a i) north = 0ₖ _
∪-help (suc n) (suc m) (merid a i) south = 0ₖ _
∪-help (suc n) (suc m) (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m))) (∪-help n m a b))) ∙∙ Kn→ΩKn+10ₖ _) i j
∪-help-pt zero a = refl
∪-help-pt (suc m) a = refl
∪-help-pt-l zero base = refl
∪-help-pt-l zero (loop i) = refl
∪-help-pt-l (suc m) a = refl

∪ : {n m : ℕ} → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc n + suc m)
∪ {n = n} {m = m} = trRec (subst (isOfHLevel (3 + n))
                                 (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i)))))
                                 (wow (suc n) m))
                          (main n m)
  where
  ptHelp : (n m : ℕ) (y : _) → ∪-help n m (snd (S₊∙ (suc n))) y ≡ 0ₖ _
  ptHelp zero zero y = refl
  ptHelp zero (suc m) y = refl
  ptHelp (suc n) zero base = refl
  ptHelp (suc n) zero (loop i) = refl
  ptHelp (suc n) (suc m) y = refl
  
  ∪fst : (n m : ℕ) → coHomK (suc m) → (S₊∙ (suc n) →∙ coHomK-ptd (suc (n + suc m)))
  ∪fst n m = trRec ((subst (isOfHLevel (3 + m)) (cong (λ x → S₊∙ (suc n) →∙ coHomK-ptd (suc x)) (cong suc (+-comm m n) ∙ sym (+-suc n m)))
                                 (wow2 (suc m) n))) λ y → (λ x → ∪-help n m x y) , ptHelp n m y

  main : (n m : ℕ) →  S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + suc m))
  fst (main n m x) y = fst (∪fst n m y) x
  snd (main zero zero base) = refl
  snd (main zero (suc m) base) = refl
  snd (main zero zero (loop i)) = refl
  snd (main zero (suc m) (loop i)) = refl
  snd (main (suc n) zero north) = refl
  snd (main (suc n) (suc m) north) = refl
  snd (main (suc n) zero south) = refl
  snd (main (suc n) (suc m) south) = refl
  snd (main (suc n) zero (merid a i)) = refl
  snd (main (suc n) (suc m) (merid a i)) = refl

subber : (n m : ℕ) → _
subber n m = subst coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m)))

minner : {k : ℕ} (n m : ℕ) → _
minner {k = k} n m = ((-ₖ2 {m = k} (((suc n) · (suc m)))))

minner0 : {k : ℕ} (n m : ℕ) → minner {k = k} n m (0ₖ _) ≡ 0ₖ _
minner0 {k = zero} zero zero = refl
minner0 {k = zero} (suc zero) zero = refl
minner0 {k = zero} (suc (suc n)) zero = minner0 n zero
minner0 {k = zero} zero (suc zero) = refl
minner0 {k = zero} zero (suc (suc m)) = minner0 zero m
minner0 {k = zero} (suc zero) (suc zero) = refl
minner0 {k = zero} (suc zero) (suc (suc m)) = {!!}
minner0 {k = zero} (suc (suc n)) (suc m) = {!!}
minner0 {k = suc k₁} n m = {!!}

subber-0 : {k : ℕ} (n m : ℕ) → subber n m (minner n m (0ₖ _)) ≡ 0ₖ _
subber-0 zero zero = refl
subber-0 zero (suc m) = refl
subber-0 (suc n) zero = refl
subber-0 (suc n) (suc m) = refl

anti-com-cheat : (n m : ℕ) (x : S₊ (suc n)) (y z : S₊ (suc m)) → ∪-help n m x y ≡ subber n m (minner n m (∪-help m n y x))
anti-com-cheat n m = {!!}

even-suc→odd : {n : ℕ} → is-even (suc n) → is-odd n
even-suc→odd {n = suc zero} p = tt
even-suc→odd {n = suc (suc n)} p = even-suc→odd {n = n} p

odd-suc→even : {n : ℕ} → is-odd (suc n) → is-even n
odd-suc→even {n = zero} p = tt
odd-suc→even {n = suc (suc n)} p = odd-suc→even {n = n} p

even-or-odd : {n : ℕ} → is-even n ⊎ is-odd n
even-or-odd {n = zero} = inl tt
even-or-odd {n = suc zero} = inr tt
even-or-odd {n = suc (suc n)} = even-or-odd {n = n}

miner-h : {k : ℕ} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m ⊎ is-odd m)
      → S₊ (suc k) → S₊ (suc k)
miner-h {k = zero} n m p q base = base
miner-h {k = zero} n m (inl x) q (loop i) = loop i
miner-h {k = zero} n m (inr x) (inl x₁) (loop i) = loop i
miner-h {k = zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
miner-h {k = suc k₁} n m p q north = north
miner-h {k = suc k₁} n m p q south = north
miner-h {k = suc k₁} n m (inl x) q (merid a i) = (merid a ∙ sym (merid (ptSn (suc k₁)))) i
miner-h {k = suc k₁} n m (inr x) (inl x₁) (merid a i) = (merid a ∙ sym (merid (ptSn (suc k₁)))) i
miner-h {k = suc k₁} n m (inr x) (inr x₁) (merid a i) = (merid a ∙ sym (merid (ptSn (suc k₁)))) (~ i)

miner : {k : ℕ} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m ⊎ is-odd m)
      → coHomK k → coHomK k
miner {k = zero} n m p q x = x --doesn't really make sense, but doesn't matter in practice
miner {k = suc k} n m p q = trMap (miner-h n m p q)

isEquiv-miner : {k : ℕ} → (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → Iso (S₊ (suc k)) (S₊ (suc k))
fun (isEquiv-miner {k = k} n m p q) = miner-h n m (inr p) (inr q)
inv' (isEquiv-miner {k = k} n m p q) = miner-h n m (inr p) (inr q)
rightInv (isEquiv-miner {k = zero} n m p q) base = refl
rightInv (isEquiv-miner {k = zero} n m p q) (loop i) = refl
rightInv (isEquiv-miner {k = suc k₁} n m p q) north = refl
rightInv (isEquiv-miner {k = suc k₁} n m p q) south = merid (ptSn (suc k₁))
rightInv (isEquiv-miner {k = suc k₁} n m p q) (merid a i) j = help a j i
  module _ where
  help : (a : _) → PathP (λ i → north ≡ merid (ptSn (suc k₁)) i) (cong (miner-h n m (inr p) (inr q) ∘ miner-h n m (inr p) (inr q)) (merid a)) (merid a)
  help a = compPathR→PathP (cong sym (congFunct (miner-h {k = suc k₁} n m (inr p) (inr q)) (merid a) (sym (merid (ptSn (suc k₁)))))
                       ∙∙ cong sym (cong (((sym (merid a ∙ sym (merid (ptSn (suc k₁))))) ∙_)) (rCancel (merid (ptSn (suc k₁)))) ∙ sym (rUnit _))
                       ∙∙ lUnit _)
leftInv (isEquiv-miner {k = zero} n m p q) base = refl
leftInv (isEquiv-miner {k = zero} n m p q) (loop i) = refl
leftInv (isEquiv-miner {k = suc k₁} n m p q) north = refl
leftInv (isEquiv-miner {k = suc k₁} n m p q) south = merid (ptSn (suc k₁))
leftInv (isEquiv-miner {k = suc k₁} n m p q) (merid a i) j =
  help k₁ n m p q (ptSn (suc k₁)) i0 i0 a j i


trMap-miner-Left : {k : ℕ} (n m : ℕ) → (p : is-even n) → (q : is-even m ⊎ is-odd m)
                 → Path (coHomK (suc k) → coHomK (suc k)) (trMap (miner-h {k = k} n m (inl p) q)) (idfun _)
trMap-miner-Left {k = zero} n m p q =
  funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
    λ {base → refl ; (loop i) → refl})
trMap-miner-Left {k = suc k₁} n m p q =
  funExt (trElim (λ _ → isOfHLevelPath (4 + k₁) (isOfHLevelTrunc (4 + k₁)) _ _)
     (λ {north → refl
      ; south → cong ∣_∣ (merid (ptSn (suc k₁)))
      ; (merid a i) j → ∣ compPath-filler (merid a) (sym (merid (ptSn (suc k₁)))) (~ j) i ∣}))

trMap-miner-Right : {k : ℕ} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m)
                 → Path (coHomK (suc k) → coHomK (suc k)) (trMap (miner-h {k = k} n m p (inl q))) (idfun _)
trMap-miner-Right {k = zero} n m (inl x) q = trMap-miner-Left n m x (inl q)
trMap-miner-Right {k = zero} n m (inr x) q =
  funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
    λ {base → refl ; (loop i) → refl})
trMap-miner-Right {k = suc k₁} n m (inl x) q = trMap-miner-Left n m x (inl q)
trMap-miner-Right {k = suc k₁} n m (inr x) q =
  funExt (trElim (λ _ → isOfHLevelPath (4 + k₁) (isOfHLevelTrunc (4 + k₁)) _ _)
     (λ {north → refl
      ; south → cong ∣_∣ (merid (ptSn (suc k₁)))
      ; (merid a i) j → ∣ compPath-filler (merid a) (sym (merid (ptSn (suc k₁)))) (~ j) i ∣}))


miner-leftEven : {k : ℕ} (n m : ℕ) → (p : is-even n) → (q : is-even m ⊎ is-odd m) → miner {k = k} n m (inl p) q ≡ idfun _ 
miner-leftEven {k = zero} n m p q = refl
miner-leftEven {k = suc k₁} n m p q =
  funExt (trElim (λ _ → isOfHLevelPath (3 + k₁) (isOfHLevelTrunc (3 + k₁)) _ _)
     (λ a → funExt⁻ (trMap-miner-Left n m p q) ∣ a ∣))

miner-rightEven : {k : ℕ} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m) → miner {k = k} n m p (inl q) ≡ idfun _ 
miner-rightEven {k = zero} n m p q = refl
miner-rightEven {k = suc x} n m p q =
    funExt (trElim (λ _ → isOfHLevelPath (3 + x) (isOfHLevelTrunc (3 + x)) _ _)
     (λ a → funExt⁻ (trMap-miner-Right n m p q) ∣ a ∣))

coder : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (x : coHomK (suc k)) → Type₀
coder n m p q x = 0ₖ _ ≡ x

minner-decode : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (x : coHomK (2 + k)) → 0ₖ _ ≡ x → x ≡ 0ₖ _
minner-decode {k = k} n m p q =
  trElim (λ _ → isOfHLevelΠ (4 + k) λ _ → isOfHLevelPath (4 + k) (isOfHLevelTrunc (4 + k)) _ _)
    funner
  where
  funner : (a : Susp (S₊ (suc k))) →
      0ₖ (suc (suc k)) ≡ ∣ a ∣ → ∣ a ∣ ≡ 0ₖ (suc (suc k))
  funner north = cong (miner n m (inr p) (inr q))
  funner south P = sym (cong ∣_∣ (merid (ptSn (suc k)))) ∙ cong (miner n m (inr p) (inr q)) P -- cong (miner n m (inr p) (inr q)) P ∙ cong ∣_∣ (merid (ptSn (suc k)))
  funner (merid a i) = main i
    where
    helpMe : (x : _) → transport (λ i → 0ₖ (suc (suc k)) ≡ ∣ merid a i ∣ → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k))) (cong (miner n m (inr p) (inr q))) x
                     ≡ sym (cong ∣_∣ (merid (ptSn (suc k)))) ∙ cong (miner n m (inr p) (inr q)) x
    helpMe x =
         (λ i → transport (λ i → ∣ merid a i ∣ ≡ 0ₖ _) (cong (miner n m (inr p) (inr q)) (transport (λ i → 0ₖ (suc (suc k)) ≡ ∣ merid a (~ i) ∣) x)))
      ∙∙ cong (λ x → transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k))) (cong (miner n m (inr p) (inr q)) x))
                       (λ z → transp (λ i → 0ₖ (suc (suc k)) ≡ ∣ merid a (~ i ∧ ~ z) ∣) z (compPath-filler x (λ i → ∣ merid a (~ i ∨ ~ z) ∣) z))
      ∙∙ cong (transport (λ i → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k)))) (lUnit _ ∙ cong (refl ∙_) (congFunct (miner n m (inr p) (inr q)) x (sym (cong ∣_∣ (merid a)))))
      ∙∙ (λ z → transp (λ i₁ → ∣ merid a (i₁ ∨ z) ∣ ≡ 0ₖ (suc (suc k))) z
                        ((λ i → ∣ merid a (~ i ∧ z) ∣) ∙ congFunct (miner n m (inr p) (inr q)) x (sym (cong ∣_∣ (merid a))) i1))
      ∙∙ cong (cong ∣_∣ (sym (merid a)) ∙_) (isCommΩK _ _ _)
      ∙∙ assoc∙ _ _ _
      ∙∙ cong (_∙ cong (trMap (miner-h n m (inr p) (inr q))) x)
              ((λ i → (λ i₁ → ∣ merid a (~ i₁ ∨ i) ∣) ∙ cong ∣_∣ ((λ j → merid a (i ∨ j)) ∙ sym (merid (ptSn _))))
              ∙ λ i → lUnit (cong ∣_∣ (lUnit (sym (merid (ptSn (suc k)))) (~ i))) (~ i))

    main : PathP (λ i → 0ₖ (suc (suc k)) ≡ ∣ merid a i ∣ → ∣ merid a i ∣ ≡ 0ₖ (suc (suc k))) (cong (miner n m (inr p) (inr q)))
                 λ x → sym (cong ∣_∣ (merid (ptSn (suc k)))) ∙ cong (miner n m (inr p) (inr q)) x
    main = toPathP (funExt helpMe)

minner-decodeId : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (x : coHomK (suc (suc k))) (P : 0ₖ (2 + k) ≡ x)
               → minner-decode n m p q x P ≡ sym P
minner-decodeId n m p q x = J (λ x P → minner-decode n m p q x P ≡ sym P) refl

congMinner' : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (P : 0ₖ (2 + k) ≡ 0ₖ _) → cong (trMap (miner-h n m (inr p) (inr q))) P ≡ sym P
congMinner' n m p q P = minner-decodeId n m p q (0ₖ _) P

congMinner : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (P : 0ₖ (2 + k) ≡ 0ₖ _)  → cong (miner n m (inr p) (inr q)) P ≡ sym P
congMinner = {!!}

miner≡minus : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) (x : coHomK (suc k)) → miner n m (inr p) (inr q) x ≡ -ₖ x
miner≡minus {k = k} n m p q = {!!}


cuPind : (n m : ℕ) → (f g : coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m))))
  → (fl : fst (f (0ₖ _)) ≡ (λ _ → 0ₖ _))
  → (gl : fst (g (0ₖ _)) ≡ (λ _ → 0ₖ _))
  → (fl≡gl : {!PathP fl!})
  → ((x : _) → fst (g x) (0ₖ _) ≡ 0ₖ _)
  → ((x : _) → fst (f ∣ x ∣) ≡ fst (g ∣ x ∣)) → (x : _) → fst (f x) ≡ fst (g x)
cuPind n m f g fl gl fl≡gl gid ind x = {!!} -- cong fst (help3 x) ∙ {!!}
  where
  f2 : coHomK (suc m) → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m))))
  fst (f2 y) x = fst (f ∣ x ∣) y
  snd (f2 y) = {!!}

  g2 : coHomK (suc m) → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m))))
  fst (g2 y) x = fst (g ∣ x ∣) y
  snd (g2 y) = {!!}

  g2≡f2 : (x : _) → f2 x ≡ g2 x
  g2≡f2 = {!!}

  w : (a : _) → fst (f ∣ a ∣) ≡ fst (g ∣ a ∣)
  w = ind

  f' : (x : coHomK (suc n)) → coHomK-ptd (suc m) →∙ (coHomK (suc (suc (n + m))) , fst (f x) (0ₖ _))
  f' x = (fst (f x)) , refl -- trRec (wow (suc n) m) λ a → (fst (g ∣ a ∣)) , (funExt⁻ (sym (ind a)) (0ₖ _) ∙ snd (f ∣ a ∣))

  g' : (x : coHomK (suc n)) → coHomK-ptd (suc m) →∙ (coHomK (suc (suc (n + m))) , fst (f x) (0ₖ _))
  g' x = (fst (g x)) , snd (g x) ∙ sym (snd (f x))

  g≡h2 : f' ≡ g' -- g ≡ h2
  g≡h2 = funExt (trElim {!!} λ a → ΣPathP ((ind a) , {!!}))

  t : {!!} -- (x : _) → fst (h x) ≡ fst (h2 x)
  t x = {!!}

  {-

  help3 : (x : _) → f x ≡ h x
  help3 =
    trElim (λ _ → isOfHLevelPath (3 + n) (wow (suc n) m) _ _)
      λ a → ΣPathP ((ind a) , (compPathL→PathP (sym (cong (sym (λ i → ind a i (snd (coHomK-ptd (suc m)))) ∙_) (rUnit (snd (f ∣ a ∣)))))))

  help4 : h ≡ g
  help4 = funExt (trElim {!!} λ a → ΣPathP (refl , {!!})) -}

cup∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
cup∙ n m = trRec (wow (suc n) m) (cunt n m)
  where
  cunt : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
  fst (cunt zero m base) _ = 0ₖ _
  fst (cunt zero m (loop i)) x = Kn→ΩKn+1 _ x i
  fst (cunt (suc n) m north) _ = 0ₖ _
  fst (cunt (suc n) m south) _ = 0ₖ _
  fst (cunt (suc n) m (merid a i)) x = Kn→ΩKn+1 _ (fst (cunt n m a) x) i
  snd (cunt zero m base) = refl
  snd (cunt zero m (loop i)) k = Kn→ΩKn+10ₖ _ k i
  snd (cunt (suc n) m north) = refl
  snd (cunt (suc n) m south) = refl
  snd (cunt (suc n) m (merid a i)) k = (cong (Kn→ΩKn+1 _) (snd (cunt n m a)) ∙ Kn→ΩKn+10ₖ _) k i

cup∙∙ : (n m : ℕ) → coHomK-ptd (suc n) →∙ (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m))) ∙)
fst (cup∙∙ n m) = cup∙ n m
snd (cup∙∙ zero m) = refl
snd (cup∙∙ (suc n) m) = refl

⌣ : (n m : ℕ) → coHomK (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
⌣ n m x y = fst (cup∙ n m x) y

rUnit-⌣ : (n m : ℕ) → (x : coHomK (suc n)) → ⌣ n m x (0ₖ _) ≡ 0ₖ _
rUnit-⌣  n m x = snd (cup∙ n m x)

lUnit-⌣ : (n m : ℕ) → (x : coHomK (suc m)) → ⌣ n m (0ₖ _) x ≡ 0ₖ _
lUnit-⌣ n m = funExt⁻ (cong fst (snd (cup∙∙ n m)))

-- →∙Homogeneous≡

private
  ⌣-distrFun :
    (n m : ℕ) → (x y : coHomK (suc n))
      → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (m + n)))
  fst (⌣-distrFun n m x y) z =
    ⌣ m n z (x +ₖ y)
  snd (⌣-distrFun n m x y) =
    lUnit-⌣ m n (x +ₖ y)

  ⌣-distrFun2 :
    (n m : ℕ) → (x y : coHomK (suc n))
      → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (m + n)))
  fst (⌣-distrFun2 n m x y) z =
    ⌣ m n z x +ₖ ⌣ m n z y
  snd (⌣-distrFun2 n m x y) =
    cong₂ _+ₖ_ (lUnit-⌣ m n x) (lUnit-⌣ m n y)

  coHomK-ptIso : (n : ℕ) (x : coHomK (suc n)) → coHomK-ptd (suc n) ≡ (coHomK (suc n) , x)
  coHomK-ptIso n x =
    Iso.fun (IsoΣPathTransportPathΣ (coHomK-ptd (suc n)) (coHomK (suc n) , x))
            ((isoToPath (addIso (suc n) x)) , (transportRefl (0ₖ _ +ₖ x) ∙ lUnitₖ _ x))

  ⌣-distr : (n m : ℕ) (x y : coHomK (suc n)) → ⌣-distrFun n m x y ≡ ⌣-distrFun2 n m x y
  ⌣-distr n m =
    elim2
      (λ _ _ → isOfHLevelPath (3 + n) (subst (isOfHLevel (3 + n))
                  (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (+-comm n m i))))) (wow (suc n) m)) _ _)
      (main n m)
    where
    hLevHelp : (n m : ℕ) (x y : _) → isOfHLevel (2 + n) (⌣-distrFun n m x y ≡ ⌣-distrFun2 n m x y)
    hLevHelp n m x y =
      (subst (isOfHLevel (3 + n)) (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (+-comm n m i))))) (wow (suc n) m)) _ _


    helper : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x)
          → sym (lUnitₖ _ x) ∙ cong (_+ₖ x) p ≡ sym (rUnitₖ _ x) ∙ cong (x +ₖ_) p
    helper n x = J (λ x p → sym (lUnitₖ _ x) ∙ cong (_+ₖ x) p ≡ sym (rUnitₖ _ x) ∙ cong (x +ₖ_) p)
                   (helper' n)
      where
      helper' : (n : ℕ) → (λ i → lUnitₖ (suc n) (0ₖ (suc n)) (~ i)) ∙
               (λ i → 0ₖ (suc n) +ₖ 0ₖ (suc n))
               ≡
               (λ i → rUnitₖ (suc n) (0ₖ (suc n)) (~ i)) ∙
               (λ i → 0ₖ (suc n) +ₖ 0ₖ (suc n))
      helper' zero = refl
      helper' (suc n) = refl

    p1-S¹ : (m : ℕ) (x : _) → (fst (⌣-distrFun zero m ∣ ptSn 1 ∣ ∣ x ∣))
                     ≡ (fst (⌣-distrFun2 zero m ∣ ptSn 1 ∣ ∣ x ∣))
    p1-S¹ m x = funExt λ z → sym (lUnitₖ _ (⌣ m zero z ∣ x ∣))
                    ∙ cong (_+ₖ (⌣ m zero z ∣ x ∣)) (sym (rUnit-⌣ m zero z))

    p2-S¹ : (m : ℕ) (x : _) → (fst (⌣-distrFun zero m ∣ x ∣ (0ₖ _)))
                     ≡ (fst (⌣-distrFun2 zero m ∣ x ∣ (0ₖ _)))
    p2-S¹ m x = funExt (λ z → cong (⌣ m zero z) (rUnitₖ _ ∣ x ∣)
                            ∙∙ sym (rUnitₖ _ _)
                            ∙∙ cong (⌣ m zero z ∣ x ∣ +ₖ_) (sym (rUnit-⌣ m zero z)))

    p2P-S¹ : (m : ℕ) (x : _) → PathP
        (λ i → p2-S¹ m x i (0ₖ _) ≡ 0ₖ _)
        (snd (⌣-distrFun zero m ∣ x ∣ (0ₖ _)))
        (snd (⌣-distrFun2 zero m ∣ x ∣ (0ₖ _)))
    p2P-S¹ zero x = flipSquare (sym (rUnit refl))
    p2P-S¹ (suc m) x = flipSquare (sym (rUnit refl))

    p1P-S¹ : (m : ℕ) (x : _) → PathP (λ i → p1-S¹ m x i (0ₖ _) ≡ 0ₖ _)
                                  (snd (⌣-distrFun zero m ∣ base ∣ ∣ x ∣))
                                  (snd (⌣-distrFun2 zero m ∣ base ∣ ∣ x ∣))
    p1P-S¹ zero x = flipSquare (sym (rUnit refl))
    p1P-S¹ (suc m) x = flipSquare (sym (rUnit refl))

    p1≡p2-S¹ : (m : ℕ) → p1-S¹ m base ≡ p2-S¹ m base
    p1≡p2-S¹ m i j z = helper _ (⌣ m zero z (0ₖ _)) (sym (rUnit-⌣ m zero z)) i j

    p1≡p2-S¹-0-1 : funExt⁻ (cong funExt⁻ (p1≡p2-S¹ zero)) (0ₖ _) ≡ refl
    p1≡p2-S¹-0-1 = transportRefl refl

    p1≡p2-S¹-0-suc : (m : ℕ) → funExt⁻ (cong funExt⁻ (p1≡p2-S¹ (suc m))) (0ₖ _) ≡ refl
    p1≡p2-S¹-0-suc m = transportRefl refl

    final-S¹ : (m : ℕ)
      → PathP (λ i → PathP (λ i₁ →
              p1≡p2-S¹ m (~ i) i₁ (snd (coHomK-ptd (suc m))) ≡ 0ₖ _)
           (snd (⌣-distrFun zero m ∣ ptSn 1 ∣ ∣ ptSn 1 ∣))
           (snd (⌣-distrFun2 zero m ∣ ptSn 1 ∣ ∣ ptSn 1 ∣)))
        (p2P-S¹ m (ptSn 1)) (p1P-S¹ m (ptSn 1))
    final-S¹ zero i j k =
      hcomp
        (λ r → λ {(i = i0) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (i = i1) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → p1≡p2-S¹-0-1 (~ r) (~ i) j
                 ; (k = i1) → ∣ north ∣})
            (rUnit (λ _ → ∣ north ∣) (~ k) j)
    final-S¹ (suc m) i j k =
      hcomp
        (λ r → λ {(i = i0) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (i = i1) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → p1≡p2-S¹-0-suc m (~ r) (~ i) j
                 ; (k = i1) → ∣ north ∣})
            (rUnit (λ _ → ∣ north ∣) (~ k) j)

  ----
    p1 : (n m : ℕ) (x : _) →
          (fst (⌣-distrFun (suc n) m ∣ ptSn (suc (suc n)) ∣ ∣ x ∣))
       ≡ (fst (⌣-distrFun2 (suc n) m ∣ ptSn (suc (suc n)) ∣ ∣ x ∣))
    p1 n m x = funExt (λ z → sym (lUnitₖ _ (⌣ m (suc n) z ∣ x ∣))
             ∙ cong (_+ₖ (⌣ m (suc n) z ∣ x ∣)) (sym (rUnit-⌣ m (suc n) z)))

    p2 : (n m : ℕ) (x : _) → (fst (⌣-distrFun (suc n) m ∣ x ∣ ∣ ptSn (suc (suc n)) ∣))
       ≡ (fst (⌣-distrFun2 (suc n) m ∣ x ∣ ∣ ptSn (suc (suc n)) ∣))
    p2 n m x = funExt (λ z → cong (⌣ m (suc n) z) (rUnitₖ _ ∣ x ∣)
                            ∙∙ sym (rUnitₖ _ _)
                            ∙∙ cong (⌣ m (suc n) z ∣ x ∣ +ₖ_) (sym (rUnit-⌣ m (suc n) z)))

    p2P : (n m : ℕ) (x : _) → PathP
        (λ i → p2 n m x i (snd (coHomK-ptd (suc m))) ≡
           snd (coHomK-ptd (suc (suc (m + suc n)))))
        (snd (⌣-distrFun (suc n) m ∣ x ∣ ∣ ptSn (suc (suc n)) ∣))
        (snd (⌣-distrFun2 (suc n) m ∣ x ∣ ∣ ptSn (suc (suc n)) ∣))
    p2P n zero x = flipSquare (sym (rUnit refl))
    p2P n (suc m) x = flipSquare (sym (rUnit refl))

    p1P : (n m : ℕ) (x : _) → PathP (λ i → p1 n m x i (0ₖ _) ≡ 0ₖ _)
                                  (snd (⌣-distrFun (suc n) m ∣ ptSn (suc (suc n)) ∣ ∣ x ∣))
                                  (snd (⌣-distrFun2 (suc n) m ∣ ptSn (suc (suc n)) ∣ ∣ x ∣))
    p1P n zero x = flipSquare (sym (rUnit refl))
    p1P n (suc m) x = flipSquare (sym (rUnit refl))

    p1≡p2 : (n m : ℕ) → p1 n m north ≡ p2 n m north
    p1≡p2 n m i j z = helper _ (⌣ m (suc n) z ∣ north ∣) (sym (rUnit-⌣ m (suc n) z)) i j

    p1≡p2-0-1 : (n : ℕ) → funExt⁻ (cong funExt⁻ (p1≡p2 n zero)) (0ₖ _) ≡ refl
    p1≡p2-0-1 n = transportRefl refl

    p1≡p2-0-suc : (n m : ℕ) → funExt⁻ (cong funExt⁻ (p1≡p2 n (suc m))) (0ₖ _) ≡ refl
    p1≡p2-0-suc n m = transportRefl refl


    final : (n m : ℕ) → PathP
        (λ i →
           PathP
           (λ i₁ →
              p1≡p2 n m (~ i) i₁ (snd (coHomK-ptd (suc m))) ≡
              snd (coHomK-ptd (suc (suc (m + suc n)))))
           (snd
            (⌣-distrFun (suc n) m ∣ ptSn (suc (suc n)) ∣
             ∣ ptSn (suc (suc n)) ∣))
           (snd
            (⌣-distrFun2 (suc n) m ∣ ptSn (suc (suc n)) ∣
             ∣ ptSn (suc (suc n)) ∣)))
        (p2P n m (ptSn (suc (suc n)))) (p1P n m (ptSn (suc (suc n))))
    final n zero i j k =
      comp (λ _ → coHomK (3 + n))
        (λ r → λ {(i = i0) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (i = i1) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) → p1≡p2-0-1 n (~ r) (~ i) j
                 ; (k = i1) → ∣ north ∣})
            (rUnit (λ _ → ∣ north ∣) (~ k) j)
    final n (suc m) i j k = 
      comp (λ _ → coHomK (3 + (m + suc n)))
        (λ r → λ {(i = i0) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (i = i1) → rUnit (λ _ → ∣ north ∣) (~ k) j
                 ; (j = i0) → ∣ north ∣
                 ; (j = i1) → ∣ north ∣
                 ; (k = i0) →  p1≡p2-0-suc n m (~ r) (~ i) j
                 ; (k = i1) → ∣ north ∣})
            (rUnit (λ _ → ∣ north ∣) (~ k) j)

    p1≡p2-refl : (n m : ℕ) → funExt⁻ (p1 n m north) (0ₖ _) ≡ funExt⁻ (p2 n m north) (0ₖ _)
    p1≡p2-refl n zero = refl
    p1≡p2-refl n (suc m) = refl

    main : (n m : ℕ) → (a b : S₊ (suc n)) →
        (⌣-distrFun n m ∣ a ∣ ∣ b ∣) ≡ ⌣-distrFun2 n m ∣ a ∣ ∣ b ∣
    main zero m =
      wedgeconFun zero zero
        (λ a b → hLevHelp zero m ∣ a ∣ ∣ b ∣)
        (λ x → ΣPathP (p1-S¹ m x , p1P-S¹ m x))
        (λ x → ΣPathP ((p2-S¹ m x) , (p2P-S¹ m x)))
        (cong ΣPathP (ΣPathP ((sym (p1≡p2-S¹ m)) , final-S¹ m)))
    main (suc n) m =
      wedgeconFun (suc n) (suc n)
        (λ x y → subst (λ l → isOfHLevel l ((⌣-distrFun (suc n) m ∣ x ∣ ∣ y ∣)
                                           ≡  ⌣-distrFun2 (suc n) m ∣ x ∣ ∣ y ∣))
                        (cong suc (+-suc n (2 + n)))
                        (isOfHLevelPlus {n = 3 + n} (suc n) (hLevHelp (suc n) m ∣ x ∣ ∣ y ∣)))
        (λ x → ΣPathP (p1 n m x , p1P n m x))
        (λ x → ΣPathP (p2 n m x , p2P n m x))
        (cong ΣPathP (ΣPathP (sym (p1≡p2 n m) , final n m)))

l-distr-⌣ : (n m : ℕ) (z : coHomK (suc n)) (x y : coHomK (suc m))
          → ⌣ n m z (x +ₖ y) ≡ ⌣ n m z x +ₖ ⌣ n m z y
l-distr-⌣ n m z x y = funExt⁻ (cong fst (⌣-distr m n x y)) z

rUnit-⌣≡lUnit-⌣ : (n m : ℕ) → rUnit-⌣ n m (0ₖ _) ≡ lUnit-⌣ n m (0ₖ _)
rUnit-⌣≡lUnit-⌣ zero m = refl
rUnit-⌣≡lUnit-⌣ (suc n) m = refl

hLev-pFun : (n m : ℕ) → isOfHLevel (3 + m) (coHomK-ptd (suc n) →∙ Ω (coHomK-ptd (3 + (n + m))))
hLev-pFun n m =
  subst (isOfHLevel (3 + m))
        (λ i → (coHomK-ptd (suc n) →∙ (isoToPath (Iso-Kn-ΩKn+1 (2 + (n + m))) i
                                      , transp (λ j → isoToPath (stabSpheres (suc (n + m))) (~ j ∨ i)) i refl)))
        (subst (isOfHLevel (3 + m)) (λ i → (coHomK-ptd (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
               (wow (suc m) n))

pFun : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
fst (pFun n m a) b = Kn→ΩKn+1 _ (⌣ n m a b)
snd (pFun n m a) = cong (Kn→ΩKn+1 _) (rUnit-⌣ n m a) ∙ Kn→ΩKn+10ₖ _

pFun2 : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (n + m)))
fst (pFun2 n m a) b i = ⌣ _ m (Kn→ΩKn+1 _ a i) b
snd (pFun2 n m a) i j = rUnit-⌣ _ m (Kn→ΩKn+1 _ a j) i

pFun≡ : (n m : ℕ) → (x : coHomK (suc n)) → pFun n m x ≡ pFun2 n m x
pFun≡ n m =
  trElim (λ _ → isOfHLevelPath (3 + n) (subst (isOfHLevel (3 + n))
                    (λ i → (coHomK-ptd (suc m) →∙ Ω (coHomK-ptd (3 + (+-comm m n i)))))
                    (hLev-pFun m n)) _ _)
         λ a → ΣPathP ((funExt (helper n m a)) , {!!})
  where
  pm2 : (n m : ℕ) (b : coHomK (suc m)) → S₊∙ (suc n) →∙ Ω (coHomK-ptd (3 + (n + m)))
  fst (pm2 n m b) a i = ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) b
  snd (pm2 n m b) j i = ⌣ _ m (∣ rCancel (merid (ptSn _)) j i ∣) b

  pm1 : (n m : ℕ) (b : coHomK (suc m)) → S₊∙ (suc n) →∙ Ω (coHomK-ptd (3 + (n + m)))
  fst (pm1 n m b) a = Kn→ΩKn+1 _ (⌣ n m ∣ a ∣ b)
  snd (pm1 zero m b) = Kn→ΩKn+10ₖ _
  snd (pm1 (suc n) m b) = Kn→ΩKn+10ₖ _

  pm1≡pm2 : (n m : ℕ) (b : coHomK (suc m)) → pm1 n m b ≡ pm2 n m b
  pm1≡pm2 n m = trElim {!i = i0 ⊢ help4 n zero a base j k
i = i1 ⊢ help4 n zero a base j k
j = i0 ⊢ Kn→ΩKn+1 (suc (suc (n + zero)))
         (⌣ n zero ∣ a ∣ ∣ loop i ∣) k
j = i1 ⊢ ⌣ (suc n) zero (Kn→ΩKn+1 (suc n) ∣ a ∣ k) ∣ loop i ∣
k = i0 ⊢ snd (coHomK-ptd (suc (suc (suc (n + zero)))))
k = i1 ⊢ snd (coHomK-ptd (suc (suc (suc (n + zero)))))!} {!!}
    where
    help4 : (n m : ℕ) (a : S₊ (suc n)) (b : S₊ (suc m)) → Kn→ΩKn+1 _ (⌣ n m ∣ a ∣ ∣ b ∣) ≡ (λ i → ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) ∣ b ∣)
    help4 n zero a base = cong (Kn→ΩKn+1 _) (rUnit-⌣ n zero ∣ a ∣) ∙∙ Kn→ΩKn+10ₖ _ ∙∙ λ j i → rUnit-⌣ (suc n) zero (Kn→ΩKn+1 (suc n) ∣ a ∣ i) (~ j)
    help4 zero zero base (loop i) = Kn→ΩKn+10ₖ _ ∙ λ j i → rUnit-⌣ (suc zero) zero (Kn→ΩKn+1 (suc zero) ∣ base ∣ i) (~ j)
    help4 zero zero (loop l) (loop i) j k =
      hcomp (λ r → λ {(i = i0) → {!!}
                     ; (i = i1) → {!⌣ 1 zero (congFunct ∣_∣ (merid (loop l)) (sym (merid base)) (~ r) k) ∣ loop i ∣!}
                     ; (j = i0) → Kn→ΩKn+1 (suc (suc (zero + zero))) (⌣ zero zero ∣ loop l ∣ ∣ loop i ∣) k
                     ; (j = i1) → ⌣ 1 zero (congFunct ∣_∣ (merid (loop l)) (sym (merid base)) (~ r) k) ∣ loop i ∣
                     ; (l = i0) → {!!}
                     ; (l = i1) → {!!}
                     ; (k = i0) → {!!}
                     ; (k = i1) → {!!}})
            {!!}
    help4 (suc n) zero a (loop i) j k = {!!}
    help4 n (suc m) a b = {!l = i0 ⊢ help4 zero zero base (loop i) j k
l = i1 ⊢ help4 zero zero base (loop i) j k
i = i0 ⊢ help4 zero zero (loop l) base j k
i = i1 ⊢ help4 zero zero (loop l) base j k
j = i0 ⊢ Kn→ΩKn+1 (suc (suc (zero + zero)))
         (⌣ zero zero ∣ loop l ∣ ∣ loop i ∣) k
j = i1 ⊢ ⌣ 1 zero (Kn→ΩKn+1 1 ∣ loop l ∣ k) ∣ loop i ∣
k = i0 ⊢ snd (coHomK-ptd (suc (suc (suc (zero + zero)))))
k = i1 ⊢ snd (coHomK-ptd (suc (suc (suc (zero + zero)))))!}

  helper-filler : (n m : ℕ) (a : S₊ (suc n)) (b : coHomK (suc m)) (k i j : I) → coHomK (3 + (n + m))
  helper-filler zero m a b k i j =
    hfill
      (λ r → λ {(i = i0) → 0ₖ _
               ; (i = i1) → ∣ rCancel (merid north) r (~ k) ∣
               ; (k = i0) → Kn→ΩKn+1 _ (⌣ zero m ∣ a ∣ b) i
               ; (k = i1) → ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) b})
      (inS (⌣ 1 m ∣ compPath-filler (merid a) (sym (merid base)) k i ∣ b))
      j
  helper-filler (suc n) m a b k i j =
      hfill
      (λ r → λ {(i = i0) → 0ₖ _
               ; (i = i1) → ∣ rCancel (merid north) r (~ k) ∣
               ; (k = i0) → Kn→ΩKn+1 _ (⌣ (suc n) m ∣ a ∣ b) i
               ; (k = i1) → ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) b})
      (inS (⌣ (2 + n) m ∣ compPath-filler (merid a) (sym (merid north)) k i ∣ b))
      j

  helper : (n m : ℕ) (a : _) (b : _) → Kn→ΩKn+1 _ (⌣ n m ∣ a ∣ b) ≡ λ i → ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) b
  helper zero m a b k i = helper-filler zero m a b k i i1
  helper (suc n) m a b = -- helper-filler (suc n) m a b k i i1
       rUnit _ ∙
       (cong (Kn→ΩKn+1 _ (⌣ (suc n) m ∣ a ∣ b) ∙_) (cong (cong ∣_∣) (cong sym (sym (rCancel (merid north)))))
    ∙∙ sym (congFunct (λ x → ⌣ _ m x b) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid north))))
    ∙∙ cong (cong (λ x → ⌣ _ m x b)) (sym (congFunct ∣_∣ (merid a) (sym (merid north)))))
  helper3 : ∀ {A B : Type} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z)
    → PathP (λ i → PathP (λ j → f x ≡ f (q j))
                          (cong f p)
                          (congFunct f p q i))
            (λ i j → f (compPath-filler p q i j)) (compPath-filler (cong f p) (cong f q))
  helper3 = {!!}
  -- Coherence paths should be easy, but Agda gets cranky
  {-
  helper2 : (n m : ℕ) (a : _) → PathP
      (λ i → funExt (helper n m a) i (0ₖ _) ≡ refl)
      (snd (pFun n m ∣ a ∣ₕ)) (snd (pFun2 n m ∣ a ∣ₕ))
  helper2 zero m a i j k = {!!}
  helper2 (suc n) m a i j k = ?
 
    hcomp
      (λ r → λ {(i = i0) → rUnit-⌣ _ m (∣ merid a k ∣) j
               ; (i = i1) → {!help4 r j k!}
               ; (j = i0) → compPath-filler (rUnit _)
                                       (cong (Kn→ΩKn+1 _ (⌣ (suc n) m ∣ a ∣ (0ₖ _)) ∙_) (cong (cong ∣_∣) (cong sym (sym (rCancel (merid north)))))
                                    ∙∙ sym (congFunct (λ x → ⌣ _ m x (0ₖ _)) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid north))))
                                    ∙∙ cong (cong (λ x → ⌣ _ m x (0ₖ _))) (sym (congFunct ∣_∣ (merid a) (sym (merid north)))))
                                    r i k
               ; (j = i1) → 0ₖ _
               ; (k = i0) → 0ₖ _
               ; (k = i1) → 0ₖ _})
              {!!}
    where
    help4 : Cube (λ j k → {!rUnit (cong (rUnit-⌣ (suc (suc n)) m) (cong ∣_∣ (merid a)))!}) (λ j k → rUnit-⌣ _ m (∣ (merid a ∙ sym (merid north)) k ∣) j)
                      (λ r k → (cong (Kn→ΩKn+1 _ (⌣ (suc n) m ∣ a ∣ (0ₖ _)) ∙_) (cong (cong ∣_∣) (cong sym (sym (rCancel (merid north)))))
                                    ∙∙ sym (congFunct (λ x → ⌣ _ m x (0ₖ _)) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid north))))
                                    ∙∙ cong (cong (λ x → ⌣ _ m x (0ₖ _))) (sym (congFunct ∣_∣ (merid a) (sym (merid north))))) r k)
                      (λ r k → 0ₖ _)
                      (λ r k → 0ₖ _)
                      λ r k → 0ₖ _
    help4 = {!!} -}

s : (n m : ℕ) (a : _) (b : _) → Kn→ΩKn+1 _ (⌣ n m ∣ a ∣ ∣ b ∣) ≡ λ i → ⌣ _ m (Kn→ΩKn+1 _ ∣ a ∣ i) ∣ b ∣
s zero m = {!!}
s (suc n) zero a b = {!⌣  ? ∣ a ∣ ∣ b ∣!}
s (suc n) (suc m) a b = refl -- (λ k i → ⌣ (2 + n) (suc m) ∣ merid a i ∣ ∣ b ∣)
                     ∙∙ rUnit _
                     ∙∙ (λ r → cong ((λ z → ⌣ (2 + n) (suc m) z ∣ b ∣)) (cong ∣_∣ (merid a)) ∙ λ i → ∣ (rCancel (merid north)) (~ r) (~ i) ∣)
                     ∙∙ sym (congFunct ((λ z → ⌣ (2 + n) (suc m) z ∣ b ∣)) (cong ∣_∣ (merid a)) (cong ∣_∣ (sym (merid (ptSn _)))))
                     ∙∙ cong (cong (λ z → ⌣ (2 + n) (suc m) z ∣ b ∣)) λ k i → cong-∙ ∣_∣ (merid a) (sym (merid (ptSn _))) (~ k) i

assocer : (n m k : ℕ) → coHomK (suc n)
  →  coHomK-ptd (suc m)
  →∙ (coHomK-ptd (suc k)
  →∙ coHomK-ptd (2 + (n + (1 + (m + k)))) ∙) -- x ⌣ (y ⌣ z)
fst (fst (assocer n m k x) y) z = ⌣ n (suc (m + k)) x (⌣ m k y z)
snd (fst (assocer n m k x) y) = cong (⌣ n (suc (m + k)) x) (rUnit-⌣ m k y) ∙ rUnit-⌣ n (suc (m + k)) x
snd (assocer n m k x) =
  ΣPathP ((funExt (λ z → cong (⌣ n (suc (m + k)) x) (lUnit-⌣ m k z)
                         ∙ rUnit-⌣ n (suc (m + k)) x))
        , helper n m x)
  where
  helper : (n m : _) (x : _) →
           PathP (λ i → funExt (λ z → (λ i₁ → ⌣ n (suc (m + k)) x (lUnit-⌣ m k z i₁))
                       ∙ rUnit-⌣ n (suc (m + k)) x) i (0ₖ _) ≡ 0ₖ _)
      ((λ i → ⌣ n (suc (m + k)) x (rUnit-⌣ m k (0ₖ _) i)) ∙ rUnit-⌣ n (suc (m + k)) x)
      refl
  helper zero zero x i j = lUnit (rUnit-⌣ zero (suc (zero + k)) x) (~ i ∨ ~ j) (i ∨ j)
  helper zero (suc m) x i j = lUnit (rUnit-⌣ zero (suc (suc m + k)) x) (~ i ∨ ~ j) (i ∨ j)
  helper (suc n) zero x i j = lUnit (rUnit-⌣ (suc n) (suc (zero + k)) x) (~ i ∨ ~ j) (i ∨ j)
  helper (suc n) (suc m) x i j = lUnit (rUnit-⌣ (suc n) (suc ((suc m) + k)) x) (~ i ∨ ~ j) (i ∨ j)

assoc2-sub : (n m k : ℕ) → _ → _
assoc2-sub n m k = subst coHomK (cong (2 +_) (cong suc (sym (+-assoc n m k)) ∙ sym (+-suc n (m + k))))

assoc2-sub-0 : (m k : ℕ) → assoc2-sub 0 m k ≡ idfun _
assoc2-sub-0 m k i x =
  transp (λ j → coHomK
    (isSetℕ _ _ (cong (2 +_) (cong suc (sym (+-assoc zero m k))
                             ∙ sym (+-suc zero (m + k)))) refl i j)) i x

assocer2' : (n m k : ℕ)
         → coHomK (suc n)
         → coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd (3 + (n + m + k)) ∙)
fst (fst (assocer2' n m k x) y) z = ⌣ _ k (⌣ n m x y) z
snd (fst (assocer2' n m k x) y) = rUnit-⌣ _ k (⌣ n m x y)
snd (assocer2' n m k x) =
  ΣPathP (funExt (λ z → (cong (λ w → ⌣ _ k w z) (rUnit-⌣ n m x) ∙ lUnit-⌣ _ k z))
       , helper n x)
    where
    helper : (n : ℕ) (x : _)
      → PathP (λ i → funExt (λ z i₁ → (((λ i₂ → ⌣ (suc (n + m)) k (rUnit-⌣ n m x i₂) z)
                ∙ lUnit-⌣ (suc (n + m)) k z) i₁)) i (0ₖ _) ≡ 0ₖ _)
        (λ i → (rUnit-⌣ (suc (n + m)) k (⌣ n m x (snd (coHomK-ptd (suc m)))) i))
        refl
    helper zero x i j =
        (hcomp (λ r → λ {(i = i0) → rUnit-⌣ (suc (zero + m)) k (⌣ zero m x (0ₖ _)) j
                        ; (i = i1) → 0ₖ _
                        ; (j = i1) → 0ₖ _})
               (rUnit-⌣ (suc (zero + m)) k (rUnit-⌣ zero m x i) j))
    helper (suc n) x i j =
        (hcomp (λ r → λ {(i = i0) → rUnit-⌣ (suc ((suc n) + m)) k (⌣ (suc n) m x (0ₖ _)) j
                        ; (i = i1) → 0ₖ _
                        ; (j = i1) → 0ₖ _})
               (rUnit-⌣ (suc ((suc n) + m)) k (rUnit-⌣ (suc n) m x i) j))
{-
assoc-⌣' : (n m k : ℕ) → (x : coHomK (suc n))
         → PathP (λ i → coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd (2 + (+-suc n (m + k) ∙ cong suc (+-assoc n m k)) i) ∙))
                  (assocer n m k x)
                  (assocer2' n m k x)
assoc-⌣' n m k = trElim {!!} ?
  where
  assocMain : (n m k : ℕ) → (x : coHomK (suc n))
               → PathP (λ i → coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd (2 + (+-suc n (m + k) ∙ cong suc (+-assoc n m k)) i) ∙))
                  (assocer n m k x)
                  (assocer2' n m k x)
  assocMain n m k = ?
-}

assocer2 : (n m k : ℕ)
         → coHomK (suc n)
         → coHomK-ptd (suc m) →∙ (coHomK-ptd (suc k) →∙ coHomK-ptd (2 + (n + (1 + (m + k)))) ∙) -- (x ⌣ y) ⌣ z
fst (fst (assocer2 n m k x) y) z = (assoc2-sub n m k) (⌣ _ k (⌣ n m x y) z)
snd (fst (assocer2 n m k x) y) =
  cong (assoc2-sub n m k) (rUnit-⌣ _ k (⌣ n m x y))
snd (assocer2 n m k x) =
  ΣPathP (funExt (λ z → cong (assoc2-sub n m k) (cong (λ w → ⌣ _ k w z) (rUnit-⌣ n m x) ∙ lUnit-⌣ _ k z))
       , helper n x)
  where
  helper : (n : ℕ) (x : _)
    → PathP (λ i → funExt (λ z i₁ → assoc2-sub n m k (((λ i₂ → ⌣ (suc (n + m)) k (rUnit-⌣ n m x i₂) z)
              ∙ lUnit-⌣ (suc (n + m)) k z) i₁)) i (0ₖ _) ≡ 0ₖ _)
      (λ i → assoc2-sub n m k (rUnit-⌣ (suc (n + m)) k (⌣ n m x (snd (coHomK-ptd (suc m)))) i))
      refl
  helper zero x i j =
    assoc2-sub zero m k
      (hcomp (λ r → λ {(i = i0) → rUnit-⌣ (suc (zero + m)) k (⌣ zero m x (0ₖ _)) j
                      ; (i = i1) → 0ₖ _
                      ; (j = i1) → 0ₖ _})
             (rUnit-⌣ (suc (zero + m)) k (rUnit-⌣ zero m x i) j))
  helper (suc n) x i j =
    assoc2-sub (suc n) m k
      (hcomp (λ r → λ {(i = i0) → rUnit-⌣ (suc ((suc n) + m)) k (⌣ (suc n) m x (0ₖ _)) j
                      ; (i = i1) → 0ₖ _
                      ; (j = i1) → 0ₖ _})
             (rUnit-⌣ (suc ((suc n) + m)) k (rUnit-⌣ (suc n) m x i) j))

open import Cubical.Foundations.Pointed.Homogeneous

assoc-⌣ : (n m k : ℕ) → (x : coHomK (suc n)) → assocer n m k x ≡ assocer2 n m k x 
assoc-⌣ n m k =
  trElim {!!} {!!}
    where
    funId : (n m k : ℕ) (a : S₊ (suc n)) (b : _) (c : _) → fst (fst (assocer n m k ∣ a ∣) b) c ≡ fst (fst (assocer2 n m k ∣ a ∣) b) c
    funId zero m k a b c = w a b c ∙ sym (funExt⁻ (assoc2-sub-0 m k) _) -- sym (funExt⁻ (assoc2-sub-0 zero zero) _)
      where
      w : (a : S¹) (b : _) (c : _) → ⌣ zero _ ∣ a ∣ (⌣ _ _ b c) ≡ ⌣ _ _ (⌣ _ _ ∣ a ∣ b) c
      w base b c = refl
      w (loop i) b c l = fst (pFun≡ m k b l) c i
    funId (suc n) m k north b c = refl
    funId (suc n) m k south b c = refl
    funId (suc n) m k (merid a i) b c j = help2 j i
      where
      assoc-mainLem : (n m : ℕ) (a : _) (b : _) → Kn→ΩKn+1 _ (⌣ n m a b) ≡ λ i → ⌣ _ m (Kn→ΩKn+1 _ a i) b
      assoc-mainLem n m a b = funExt⁻ (cong fst (pFun≡ n m a)) b
      
      subAssoc : subst coHomK (cong (3 +_) (cong suc (sym (+-assoc n m k)) ∙ sym (+-suc n (m + k)))) ≡ assoc2-sub (suc n) m k
      subAssoc = cong (subst coHomK) (isSetℕ _ _ _ _)

      subAssoc0 : funExt⁻ subAssoc (0ₖ _) ≡ refl
      subAssoc0 i j = {!!}

      help2 : cong (λ x → ⌣ _ _ ∣ x ∣ (⌣ m k b c)) (merid a) ≡ cong (assoc2-sub (suc n) m k) (cong (λ x → ⌣ _ k (⌣ _ _ ∣ x ∣ b) c) (merid a))
      help2 = (λ r → Kn→ΩKn+1 _ (funId n m k a b c r))
            ∙∙ {!!}
            ∙∙ cong (cong (assoc2-sub (suc n) m k))
                    (assoc-mainLem _ _ ((⌣ n m ∣ a ∣ b)) c)
      {- (λ _ → Kn→ΩKn+1 _ (⌣ _ _ ∣ a ∣ (⌣ m k b c)))
           ∙∙ (λ r → Kn→ΩKn+1 _ (funId n m k a b c r))
           ∙∙ (λ r i → transp (λ i → coHomK ((cong (3 +_) (cong suc (sym (+-assoc n m k)) ∙ sym (+-suc n (m + k)))) (i ∨ ~ r))) (~ r)
                     ((Kn→ΩKn+1
                      ((cong (2 +_) (cong suc (sym (+-assoc n m k)) ∙ sym (+-suc n (m + k)))) (~ r))
                      (transp (λ i → coHomK ((cong (2 +_) (cong suc (sym (+-assoc n m k)) ∙ sym (+-suc n (m + k))))
                      (i ∧ ~ r)))
                      r
                      (⌣ _ k (⌣ _ _ ∣ a ∣ b) c))) i))
           ∙∙ rUnit _
           ∙∙ (λ r → (λ i → subAssoc (i ∧ r) (0ₖ _))
                   ∙∙ cong (subAssoc r) (Kn→ΩKn+1 _ (⌣ _ k (⌣ _ _ ∣ a ∣ b) c))
                   ∙∙ λ i → subAssoc (~ i ∧ r) (0ₖ _))
           ∙∙ ((λ r → subAssoc0 r
                   ∙∙ cong (assoc2-sub (suc n) m k) (Kn→ΩKn+1 _ (⌣ _ k (⌣ _ _ ∣ a ∣ b) c))
                   ∙∙ cong sym (subAssoc0) r))
           ∙∙ sym (rUnit (cong (assoc2-sub (suc n) m k) (Kn→ΩKn+1 _ (⌣ _ k (⌣ _ _ ∣ a ∣ b) c))))
           ∙∙ cong (cong (assoc2-sub (suc n) m k)) (assoc-mainLem _ _ ((⌣ n m ∣ a ∣ b)) c)
           ∙∙ λ _ i → assoc2-sub (suc n) m k (⌣ _ k (Kn→ΩKn+1 _ (⌣ _ _ ∣ a ∣ b) i) c) -}

anti-commer : (n m : ℕ) → coHomK (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
anti-commer n m x y =
  miner (suc n) (suc m) even-or-odd even-or-odd
    (subst coHomK (cong (2 +_) (+-comm m n))
      (⌣ m n y x))

anti-commer∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
fst (anti-commer∙ n m x) y = anti-commer n m x y
snd (anti-commer∙ zero zero x) = refl
snd (anti-commer∙ zero (suc m) x) = refl
snd (anti-commer∙ (suc n) zero x) = refl
snd (anti-commer∙ (suc n) (suc m) x) = refl


G : (n m : ℕ) (p : is-even (suc n) ⊎ is-odd (suc n)) (q : is-even (suc m) ⊎ is-odd (suc m))
    → coHomK (2 + (n + m)) → coHomK (2 + (n + m))
G n m p q = miner (suc n) (suc m) p q

miner-miner : {k : ℕ} (n m : ℕ) (p : is-even n ⊎ is-odd n) (q : is-even m ⊎ is-odd m)
            → (x : coHomK (suc k))
            → miner n m p q (miner n m p q x) ≡ x
miner-miner {k = k} n m p q =
  trElim (λ _ → isOfHLevelPath (3 + k) (isOfHLevelTrunc (3 + k)) _ _)
    (help2 k n m p q)
  where
  help2 : (k n m : ℕ) (p : _) (q : _)
        → (a : S₊ (suc k)) → miner n m p q (miner n m p q ∣ a ∣) ≡ ∣ a ∣
  help2 zero n m p q base = refl
  help2 zero n m (inl x) q (loop i) = refl
  help2 zero n m (inr x) (inl x₁) (loop i) = refl
  help2 zero n m (inr x) (inr x₁) (loop i) = refl
  help2 (suc k) n m (inl x₁) q x w =
    trMap-miner-Left n m x₁ q w (trMap-miner-Left n m x₁ q w ∣ x ∣)
  help2 (suc k) n m (inr x₁) (inl x₂) x w =
    trMap-miner-Right n m (inr x₁) x₂ w (trMap-miner-Right n m (inr x₁) x₂ w ∣ x ∣)
  help2 (suc k) n m (inr x₁) (inr x₂) north = refl
  help2 (suc k) n m (inr x₁) (inr x₂) south = cong ∣_∣ (merid (ptSn (suc k)))
  help2 (suc k) n m (inr x₁) (inr x₂) (merid a i) w = h w i
    where
    h : PathP (λ i → 0ₖ _ ≡ ∣ merid (ptSn (suc k)) i ∣)
              (cong (miner n m (inr x₁) (inr x₂) ∘ miner n m (inr x₁) (inr x₂)) (cong ∣_∣ (merid a)))
              (cong ∣_∣ (merid a))
    h = compPathR→PathP
          (cong (cong (miner n m (inr x₁) (inr x₂))) (cong (cong ∣_∣) (symDistr (merid a) (sym (merid (ptSn _))))
                                                    ∙ congFunct ∣_∣ (merid (ptSn _)) (sym (merid a)))
        ∙∙ cong-∙ (miner n m (inr x₁) (inr x₂)) (cong ∣_∣ (merid (ptSn _))) (cong ∣_∣ (sym (merid a)))
        ∙∙ cong (_∙ λ i → ∣ (merid a ∙ sym (merid (ptSn _))) i ∣) (cong (cong ∣_∣) (cong sym (rCancel (merid (ptSn _)))))
        ∙∙ sym (lUnit _)
        ∙∙ cong-∙ ∣_∣ (merid a) (sym (merid (ptSn _)))
         ∙ lUnit _)

miner-comm : {k : ℕ} (n m : ℕ) (p : is-even n ⊎ is-odd n) (q : is-even m ⊎ is-odd m)
            → (x : coHomK (suc k))
            → miner n m p q x ≡ miner m n q p x
miner-comm {k = k} n m (inl x₁) q x =
  funExt⁻ (trMap-miner-Left n m x₁ q) x
  ∙ sym (funExt⁻ (trMap-miner-Right m n q x₁) x)
miner-comm {k = k} n m (inr x₁) (inl x₂) x =
  funExt⁻ (trMap-miner-Right n m (inr x₁) x₂) x
  ∙ sym (funExt⁻ (trMap-miner-Left m n x₂ (inr x₁)) x)
miner-comm {k = k} n m (inr x₁) (inr x₂) =
  trElim (λ _ → isOfHLevelPath (3 + k) (isOfHLevelTrunc (3 + k)) _ _)
    (help2 k)
  where
  help2 : (k : ℕ) → (a : S₊ (suc k)) →
       miner n m (inr x₁) (inr x₂) ∣ a ∣ ≡
      miner m n (inr x₂) (inr x₁) ∣ a ∣
  help2 zero base = refl
  help2 zero (loop i) = refl
  help2 (suc k₁) north = refl
  help2 (suc k₁) south = refl
  help2 (suc k₁) (merid a i) = refl

sub : (n m : ℕ) → coHomK (2 + (m + n)) → coHomK (2 + (n + m))
sub n m = subst coHomK (cong (2 +_) (+-comm m n))

F : (n m : ℕ) → coHomK (2 + (m + n)) → coHomK (2 + (n + m))
F n m = G n m even-or-odd even-or-odd ∘ sub n m

F⁻ : (n m : ℕ) → coHomK (2 + (n + m)) → coHomK (2 + (m + n))
F⁻ n m = subst coHomK (cong (2 +_) (sym (+-comm m n))) ∘ miner (suc n) (suc m) even-or-odd even-or-odd

permF : {k l : ℕ} (n m : ℕ) (P : _) (Q : _) (x : coHomK k) (p : k ≡ l)
      → miner n m P Q (subst coHomK p x) ≡ subst coHomK p (miner n m P Q x)
permF n m P Q x p k =
  transp (λ i → coHomK (p (i ∨ ~ k))) (~ k)
    (miner n m P Q
      (transp (λ i → coHomK (p (i ∧ ~ k))) k x))

Kn→ΩKn+1F : (n m : ℕ) (p : 0ₖ _ ≡ 0ₖ _) (P : is-even (suc n) ⊎ is-odd (suc n)) (Q : is-even (suc m) ⊎ is-odd (suc m))
  → sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (cong (F n m) p) ∙∙ Kn→ΩKn+10ₖ _
  ≡ cong (cong (miner (suc n) (suc m) P Q ∘ subst coHomK (cong (3 +_) (+-comm m n)))) (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) p ∙∙ Kn→ΩKn+10ₖ _)
Kn→ΩKn+1F n m p (inl x) Q =
     (λ k → sym (Kn→ΩKn+10ₖ _)
          ∙∙ (λ i → Kn→ΩKn+1 _ (miner (suc n) (suc m) (prop-help _ even-or-odd (inl x) k) even-or-odd (sub n m (p i))))
          ∙∙ Kn→ΩKn+10ₖ _)
   ∙∙ (λ k → sym (Kn→ΩKn+10ₖ _)
           ∙∙ cong (Kn→ΩKn+1 _) (cong (trMap-miner-Left (suc n) (suc m) x even-or-odd k) (cong (sub n m) p) )
           ∙∙ Kn→ΩKn+10ₖ _)
   ∙∙ (λ k i j → transp (λ j → coHomK (cong (3 +_) (+-comm m n) (~ k ∨ j))) (~ k)
           ((((sym (Kn→ΩKn+10ₖ (((cong (2 +_) (+-comm m n)) (~ k))))
          ∙∙ (λ i → Kn→ΩKn+1 ((cong (2 +_) (+-comm m n)) (~ k))
                (transp (λ j → coHomK ((cong (2 +_) (+-comm m n)) (j ∧ ~ k))) k (p i)))
          ∙∙ Kn→ΩKn+10ₖ ((cong (2 +_) (+-comm m n)) (~ k))))) i j))
   ∙∙ {!!}
   ∙∙ λ k → cong (cong {!!})
            (cong (cong (subst coHomK (cong (3 +_) (+-comm m n))))
              (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) p ∙∙ Kn→ΩKn+10ₖ _))
Kn→ΩKn+1F n m p (inr x) (inl x₁) = {!!}
Kn→ΩKn+1F n m p (inr x) (inr x₁) = {!!}

-- F-F : (n m : ℕ) (x : _) → F n m (F m n x) ≡ x
-- F-F n m x =
--     permF (suc n) (suc m) even-or-odd even-or-odd (F m n x) (cong (2 +_) (+-comm m n))
--  ∙∙ cong (sub n m)
--          (miner-comm (suc n) (suc m) even-or-odd even-or-odd
--            (F m n x))
--  ∙∙ cong (sub n m)
--          (miner-miner (suc m) (suc n) even-or-odd even-or-odd
--            (sub m n x))
--  ∙∙ sym (substComposite coHomK (cong (2 +_) (+-comm n m)) (cong (2 +_) (+-comm m n)) x)
--  ∙∙ (cong (λ z → subst coHomK z x) (isSetℕ _ _ (cong (2 +_) (+-comm n m) ∙ cong (2 +_) (+-comm m n)) refl)
--    ∙ transportRefl x)

-- F-wrapped : (n m : ℕ) (x : _) (p : x ≡ x) (w : 0ₖ _ ≡ x)
--          → {!!} ∙∙ cong (F n m) p ∙∙ {!!} ≡ {!!}
-- F-wrapped = {!!}

-- F⁻-F : (n m : ℕ) (x : _) → F⁻ n m (F n m x) ≡ x
-- F⁻-F n m x = 
--   cong (subst coHomK (cong (2 +_) (sym (+-comm m n))))
--     (miner-miner (suc n) (suc m) even-or-odd even-or-odd
--       (subst coHomK (cong (2 +_) (+-comm m n)) x))
--      ∙ transport⁻Transport (λ i → coHomK (2 + (+-comm m n i))) x

-- anti-comm-main0 : (m : ℕ) → (a : S¹) (b : S₊ (suc m))
--         → ⌣ zero m ∣ a ∣ ∣ b ∣ ≡  F zero m (⌣ m zero ∣ b ∣ ∣ a ∣)
-- anti-comm-main0 zero base base = refl
-- anti-comm-main0 zero base (loop i) k =
--   F zero zero (Kn→ΩKn+10ₖ _ (~ k) i)
-- anti-comm-main0 zero (loop i) base k =
--   Kn→ΩKn+10ₖ _ k i
-- anti-comm-main0 zero (loop i) (loop j) k =
--   hcomp (λ r → λ {(i = i0) → F zero zero ∣ rCancel (merid base) (~ k ∨ ~ r) j ∣
--                  ; (i = i1) → F zero zero ∣ rCancel (merid base) (~ k ∨ ~ r) j ∣
--                  ; (j = i0) → ∣ rCancel (merid base) k i ∣
--                  ; (j = i1) → ∣ rCancel (merid base) k i ∣
--                  ; (k = i0) → ⌣ zero zero ∣ loop i ∣ ∣ loop j ∣
--                  ; (k = i1) → F zero zero
--                                 (doubleCompPath-filler
--                                   (cong (cong ∣_∣) (sym (rCancel (merid base))))
--                                   (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                                   (cong (cong ∣_∣) (rCancel (merid base))) (~ r) i j) })
--         (hcomp (λ r → λ {(i = i0) → F zero zero ∣ north ∣
--                  ; (i = i1) → F zero zero ∣ north ∣
--                  ; (j = i0) → ∣ rCancel (merid base) (k ∨ ~ r) i ∣
--                  ; (j = i1) → ∣ rCancel (merid base) (k ∨ ~ r) i ∣
--                  ; (k = i0) → doubleCompPath-filler
--                                  (cong (cong ∣_∣) (sym (rCancel (merid base))))
--                                  (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                                  (cong (cong ∣_∣) ( (rCancel (merid base)))) (~ r) j i
--                  ; (k = i1) →
--                    F zero zero (inst _ (cong (cong ∣_∣) (sym (rCancel (merid base)))
--                                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                                     ∙∙ (cong (cong ∣_∣) (rCancel (merid base)))) r j i) })
--                (helper k i j))
--   where
--   helper : flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid base))))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) ( (rCancel (merid base)))))
--         ≡ cong (cong (F zero zero)) (cong sym (flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid base))))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) ( (rCancel (merid base)))))))
--   helper =
--        sym (inst _ _)
--      ∙ (λ k → rUnit (sym (cong (cong (λ x → transportRefl x (~ k)))
--                        (cong (cong ∣_∣) (sym (rCancel (merid base)))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) (rCancel (merid base)))))) k)
--     ∙∙ (λ k → transportRefl refl (~ k)
--             ∙∙ inst4 (cong (cong (transport refl))
--                  (cong (cong ∣_∣) (sym (rCancel (merid base)))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) (rCancel (merid base))))) k
--             ∙∙ transportRefl refl (~ k))
--     ∙∙ (λ k → (λ i → congMinner' 1 1 tt tt
--                             (λ i₁ → transport (λ _ → HubAndSpoke (Susp S¹) 3) (0ₖ _))
--                             (~ k ∧ i))
--             ∙∙ cong (λ x → congMinner' 1 1 tt tt x (~ k)) (cong (cong (transport refl))
--                  (cong (cong ∣_∣) (sym (rCancel (merid base)))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) ( (rCancel (merid base))))))
--             ∙∙ λ i → congMinner' 1 1 tt tt
--                             (λ i₁ → transport (λ _ → HubAndSpoke (Susp S¹) 3) (0ₖ _))
--                             (~ k ∧ ~ i))
--     ∙∙ sym (rUnit _)
--     ∙∙ cong (cong (cong (F zero zero))) (cong (cong sym)
--                        (sym (inst3 _ (cong (cong ∣_∣) (sym (rCancel (merid base)))
--                     ∙∙ (λ i j → ⌣ zero zero ∣ loop j ∣ ∣ loop i ∣)
--                     ∙∙ (cong (cong ∣_∣) (rCancel (merid base)))))))
-- anti-comm-main0 (suc m) base north = refl
-- anti-comm-main0 (suc m) base south = refl
-- anti-comm-main0 (suc m) base (merid a i) k =
--   F zero (suc m) (rUnit-⌣ (suc m) zero ∣ merid a i ∣ (~ k))
-- anti-comm-main0 (suc m) (loop i) north k =
--   cong (cong ∣_∣) (rCancel (merid north)) k i
-- anti-comm-main0 (suc m) (loop i) south k = help2 k i
--   where
--   help2  : cong (λ x → ⌣ zero (suc m) ∣ x ∣ ∣ south ∣) loop ≡ refl
--   help2 = (λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
--         ∙ cong (cong ∣_∣) (rCancel (merid north))
-- anti-comm-main0 (suc m) (loop i) (merid a j) k =
--   comp (λ _ → coHomK (3 + m))
--     (λ r → λ {(i = i0) → F zero (suc m) (rUnit-⌣ (suc m) zero ∣ merid a j ∣ (~ k ∨ ~ r))
--               ; (i = i1) → F zero (suc m) (rUnit-⌣ (suc m) zero ∣ merid a j ∣ (~ k ∨ ~ r))
--               ; (j = i0) → ∣ rCancel (merid north) k i ∣
--               ; (j = i1) → ((λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
--                            ∙ cong (cong ∣_∣) (rCancel (merid north))) k i
--               ; (k = i0) → ⌣ zero (suc m) ∣ loop i ∣ ∣ merid a j ∣
--               ; (k = i1) →
--                 F zero (suc m)
--                    (doubleCompPath-filler {x = refl {x = 0ₖ _}} {w = refl {x = 0ₖ _}}
--                      (λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ (~ i))
--                      (λ i j → ⌣ (suc m) zero ∣ merid a j ∣ ∣ loop i ∣)
--                      (λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ i) (~ r) i j)})
--         (comp (λ _ → coHomK (3 + m))
--     (λ r → λ {(i = i0) → 0ₖ _
--               ; (i = i1) → 0ₖ _
--               ; (j = i0) → ∣ rCancel (merid north) (k ∨ ~ r) i ∣
--               ; (j = i1) → ((λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
--                            ∙ cong (cong ∣_∣) (rCancel (merid north))) (k ∨ ~ r) i
--               ; (k = i0) →
--                    doubleCompPath-filler {x = refl {x = 0ₖ _}} {w = refl {x = 0ₖ _}}
--                      (cong (cong ∣_∣) (sym (rCancel (merid north))))
--                        (λ j i → ⌣ zero (suc m) ∣ loop i ∣ ∣ merid a j ∣)
--                        (((λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
--                            ∙ cong (cong ∣_∣) (rCancel (merid north)))) (~ r) j i
--               ; (k = i1) →
--                 cong (cong (F zero (suc m))) 
--                      ((λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ (~ i))
--                      ∙∙ (λ i j → ⌣ (suc m) zero ∣ merid a j ∣ ∣ loop i ∣)
--                      ∙∙ (λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ i)) i j})
--              (help2 k i j))
--   where
--   help2 : Path (typ ((Ω^ 2) (coHomK-ptd (3 + m))))
--           (flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid north))))
--                       ∙∙ (λ j i → ⌣ zero (suc m) ∣ loop i ∣ ∣ merid a j ∣)
--                       ∙∙ ((λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i)) ∙ sym (merid north)))
--                            ∙ cong (cong ∣_∣) (rCancel (merid north)))))
--           (cong (cong (F zero (suc m)))
--             ((λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ (~ i))
--                      ∙∙ (λ i j → ⌣ (suc m) zero ∣ merid a j ∣ ∣ loop i ∣)
--                      ∙∙ (λ i j → rUnit-⌣ (suc m) zero ∣ merid a j ∣ i)))
--   help2 =
--       cong flipSquare
--         ((λ k → (cong (cong ∣_∣) (sym (rCancel (merid north))))
--                       ∙∙ (λ i j → Kn→ΩKn+1 _ ∣ compPath-filler (merid a) (sym (merid (ptSn _))) k i ∣ j)
--                       ∙∙ ((λ i → cong ∣_∣ (merid (merid (ptSn (suc m)) (~ i ∧ ~ k)) ∙ sym (merid north)))
--                            ∙ cong (cong ∣_∣) (rCancel (merid north))))
--       ∙∙ (λ k → (cong (cong ∣_∣) (sym (rCancel (merid north))))
--               ∙∙ cong (Kn→ΩKn+1 _) (rUnit (λ i → (⌣ zero m ∣ loop i ∣ ∣ a ∣)) k) -- (λ i j → Kn→ΩKn+1 _ (⌣ zero m ∣ loop i ∣ ∣ a ∣) j) k
--               ∙∙ lUnit (cong (cong ∣_∣) (rCancel (merid north))) (~ k))
--       ∙∙ λ k → (cong (cong ∣_∣) (sym (rCancel (merid north))))
--              ∙∙ cong (Kn→ΩKn+1 _)
--                   ((λ i → anti-comm-main0 m base a (i ∧ k))
--                 ∙∙ (λ i → anti-comm-main0 m (loop i) a k)
--                 ∙∙ λ i → anti-comm-main0 m base a (~ i ∧ k))
--              ∙∙ (cong (cong ∣_∣) (rCancel (merid north))))
--    ∙∙ (λ k → flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid north))))
--              ∙∙ cong (Kn→ΩKn+1 _)
--                   ((anti-comm-main0 m base a)
--                 ∙∙ cong (F zero m) (λ i → ⌣ m zero ∣ a ∣ ∣ loop i ∣)
--                 ∙∙ sym (anti-comm-main0 m base a))
--              ∙∙ (cong (cong ∣_∣) (rCancel (merid north)))))
--    ∙∙ {!⌣ m zero ∣ a ∣ ∣ loop i ∣!}
--    ∙∙ {!!}
--    ∙∙ cong (cong (cong (F zero (suc m))))
--            λ _ → ((λ i₁ j₁ → rUnit-⌣ (suc m) zero ∣ merid a j₁ ∣ (~ i₁)) ∙∙
--                    ((λ i j → Kn→ΩKn+1 _ (⌣ m zero ∣ a ∣ ∣ loop i ∣) j)) ∙∙
--                  (λ i₁ j₁ → rUnit-⌣ (suc m) zero ∣ merid a j₁ ∣ i₁))

--   rUnit-anti-comm : (m : ℕ) (a : _)
--                   → (cong (F zero m) (rUnit-⌣ m zero ∣ a ∣)) ≡ sym (anti-comm-main0 m base a)
--   rUnit-anti-comm zero base = refl
--   rUnit-anti-comm zero (loop i) = refl
--   rUnit-anti-comm (suc m) north = refl
--   rUnit-anti-comm (suc m) south = refl
--   rUnit-anti-comm (suc m) (merid a i) k j = cong (F zero (suc m))
--          (rUnit-⌣ (suc m) zero ∣ merid a i ∣) j

--   help3 : (m : ℕ) (x : is-even (suc (suc m)) ⊎ is-odd (suc (suc m))) → (a : _) →
--     flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid north))))
--              ∙∙ cong (Kn→ΩKn+1 _)
--                   ((anti-comm-main0 m base a)
--                 ∙∙ cong (F zero m) (λ i → ⌣ m zero ∣ a ∣ ∣ loop i ∣)
--                 ∙∙ sym (anti-comm-main0 m base a))
--              ∙∙ (cong (cong ∣_∣) (rCancel (merid north))))
--              ≡
--     {!!}
--   help3 m p a =
--     (λ k → flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid north))))
--              ∙∙ cong (Kn→ΩKn+1 _)
--                   ((cong sym (rUnit-anti-comm m a)) (~ k)
--                 ∙∙ cong (F zero m) (λ i → ⌣ m zero ∣ a ∣ ∣ loop i ∣)
--                 ∙∙ rUnit-anti-comm m a (~ k))
--              ∙∙ (cong (cong ∣_∣) (rCancel (merid north)))))
--              ∙∙ (λ k → flipSquare ((cong (cong ∣_∣) (sym (rCancel (merid north))))
--              ∙∙ cong (Kn→ΩKn+1 _)
--                   (cong (F zero m)
--                         (λ i → rUnit-⌣ m zero ∣ a ∣ (~ i ∨ k))
--                 ∙∙ cong (F zero m)
--                         (doubleCompPath-filler
--                           (sym (rUnit-⌣ m zero ∣ a ∣))
--                           (λ i → ⌣ m zero ∣ a ∣ ∣ loop i ∣)
--                           (rUnit-⌣ m zero ∣ a ∣) k)
--                 ∙∙ cong (F zero m)
--                         λ i → rUnit-⌣ m zero ∣ a ∣ (i ∨ k))
--              ∙∙ (cong (cong ∣_∣) (rCancel (merid north)))))
--              ∙∙ (λ k →
--                    flipSquare (
--                     (cong (cong ∣_∣) (sym (rCancel (merid north))))
--                  ∙∙ cong (Kn→ΩKn+1 _)
--                       (rUnit (cong (F zero m) (sym (rUnit-⌣ m zero ∣ a ∣)
--                           ∙∙ (λ i → ⌣ m zero ∣ a ∣ ∣ loop i ∣)
--                           ∙∙ (rUnit-⌣ m zero ∣ a ∣))) (~ k))
--                  ∙∙ (cong (cong ∣_∣) (rCancel (merid north)))))
--              ∙∙ {!!}
--              ∙∙ {!!}
-- anti-comm-main : (n : ℕ) (m : ℕ) → (a : S₊ (suc n)) (b : S₊ (suc m))
--         → ⌣ n m ∣ a ∣ ∣ b ∣ ≡  F n m (⌣ m n ∣ b ∣ ∣ a ∣)
-- anti-comm-main zero = anti-comm-main0
-- anti-comm-main (suc n) zero a b =
--      sym (F-F (suc n) zero _)
--    ∙ sym (cong (F (suc n) zero) (anti-comm-main0 (suc n) b a))
-- anti-comm-main (suc n) (suc m) a b = {!!}
