{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Cup where


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

∪-alt : (n m : ℕ) → is-even (suc n) ⊎ is-odd (suc n) → is-even (suc m) ⊎ is-odd (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt-id : (n : ℕ) (a : _) → ∪-alt n zero even-or-odd (inr tt) a base ≡ 0ₖ _
∪-alt zero m p q base y = 0ₖ _
∪-alt zero zero p q (loop i) base = 0ₖ _
∪-alt zero zero p q (loop i) (loop j) =
  hcomp (λ k → λ {(j = i0) → 0ₖ 2
                 ; (j = i1) → ∣ merid base (~ k) ∣
                 ; (i = i0) → ∣ merid base (~ k ∧ j) ∣
                 ; (i = i1) → ∣ merid base (~ k ∧ j) ∣})
        ∣ merid (loop i) j ∣
∪-alt zero (suc m) p q (loop i) north = 0ₖ _
∪-alt zero (suc m) p q (loop i) south = 0ₖ _
∪-alt zero (suc m) p q (loop i) (merid a j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (cong (λ x → ∪-alt zero m (inr tt) (even-or-odd {n = suc m}) x a) loop)
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt (suc n) zero p q x base = 0ₖ _
∪-alt (suc n) zero p q north (loop i) = 0ₖ _
∪-alt (suc n) zero p q south (loop i) = 0ₖ _
∪-alt (suc n) zero p q (merid a i) (loop j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) ((sym (∪-alt-id n a) ∙∙ cong (∪-alt n zero (even-or-odd {n = suc n}) (inr tt) a) loop ∙∙ ∪-alt-id n a))
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt (suc n) (suc m) (inl even-sucn) (inl even-sucm) north y = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inl even-sucm) south y = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inl even-sucm) (merid a i) north = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inl even-sucm) (merid a i) south = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inl even-sucm) (merid a i) (merid b j) =
     (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m)))
             (∪-alt n m (inr (even-suc→odd even-sucn)) (inr (even-suc→odd even-sucm)) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) i j
-- even + odd
∪-alt (suc n) (suc m) (inl even-sucn) (inr odd-sucm) north y = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inr odd-sucm) south y = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inr odd-sucm) (merid a i) north = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inr odd-sucm) (merid a i) south = 0ₖ _
∪-alt (suc n) (suc m) (inl even-sucn) (inr odd-sucm) (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m)))
             (∪-alt n m (inr (even-suc→odd even-sucn)) (inl (odd-suc→even odd-sucm)) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) j i
-- odd + even
∪-alt (suc n) (suc m) (inr odd-sucn) (inl even-sucm) north y = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inl even-sucm) south y = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inl even-sucm) (merid a i) north = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inl even-sucm) (merid a i) south = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inl even-sucm) (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m)))
             (subber n m (∪-alt m n (inr (even-suc→odd {n = suc m} even-sucm)) (inl (odd-suc→even {n = suc n} odd-sucn)) b a))))
  ∙∙ Kn→ΩKn+10ₖ _) i j
-- odd + odd
∪-alt (suc n) (suc m) (inr odd-sucn) (inr odd-sucm) north y = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inr odd-sucm) south y = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inr odd-sucm) (merid a i) north = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inr odd-sucm) (merid a i) south = 0ₖ _
∪-alt (suc n) (suc m) (inr odd-sucn) (inr odd-sucm) (merid a i) (merid b j) =
     (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m)))
             (∪-alt n m (inl (odd-suc→even odd-sucn)) (inl (odd-suc→even odd-sucm)) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt-id zero base = refl
∪-alt-id zero (loop i) = refl
∪-alt-id (suc n) a = refl

{-
∪-alt2 : (n m : ℕ) → is-even (suc n) ⊎ is-odd (suc n) → is-even (suc m) ⊎ is-odd (suc m) → (S₊ (suc n)) → (S₊ (suc m)) → coHomK (suc n + suc m)
∪-alt2 zero m p q x y = {!!}
∪-alt2 (suc n) zero p q x y = {!!}
∪-alt2 (suc n) (suc m) (inl p) (inl q) north y = 0ₖ _
∪-alt2 (suc n) (suc m) (inl p) (inl q) south y = 0ₖ _
∪-alt2 (suc n) (suc m) (inl p) (inl q) (merid a i) y =
  Kn→ΩKn+1 _ (∪-alt2 n (suc m) (inr (even-suc→odd p)) (inl q) a y) i
∪-alt2 (suc n) (suc m) (inl x₁) (inr x₂) north y = 0ₖ _
∪-alt2 (suc n) (suc m) (inl x₁) (inr x₂) south y = 0ₖ _
∪-alt2 (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) y =
  Kn→ΩKn+1 _ (∪-alt2 n (suc m) (inr (even-suc→odd x₁)) (inr x₂) a y) i
∪-alt2 (suc n) (suc m) (inr x₁) (inl x₂) x north = 0ₖ _
∪-alt2 (suc n) (suc m) (inr x₁) (inl x₂) x south = 0ₖ _
∪-alt2 (suc n) (suc m) (inr x₁) (inl x₂) x (merid a i) =
  Kn→ΩKn+1 _ (subst coHomK (cong suc (sym (+-suc n (suc m))))
              (∪-alt2 (suc n) m (inr x₁) (inr (even-suc→odd x₂)) x a)) i
∪-alt2 (suc n) (suc m) (inr x₁) (inr x₂) north y = 0ₖ _
∪-alt2 (suc n) (suc m) (inr x₁) (inr x₂) south y = 0ₖ _
∪-alt2 (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) y =
  Kn→ΩKn+1 _ (∪-alt2 n (suc m) (inl (odd-suc→even x₁)) (inr x₂) a y) i


∪≡ : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n)) → (q : is-even (suc m) ⊎ is-odd (suc m)) → (x : S₊ (suc n)) → (y : S₊ (suc m))
  → ∪-alt2 n m p q x y ≡ ∪-alt n m p q x y
∪≡ zero m p q x y = {!!}
∪≡ (suc n) zero p q x y = {!!}
∪≡ (suc n) (suc m) (inl x₁) (inl x₂) north y = refl
∪≡ (suc n) (suc m) (inl x₁) (inl x₂) south y = refl
∪≡ (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) y j = help1 y j i
  where
  lUnithelers : (n m : ℕ) (x : _) (x₁ : _) (x₂ : _) → cong (λ x → ∪-alt2 (suc n) (suc m) (inl x₁) (inl x₂) x south)
      (merid x) ≡ refl
  lUnithelers zero m base x₁ x₂ = cong (Kn→ΩKn+1 _) (∪≡ zero (suc m) (inr (even-suc→odd x₁)) (inl x₂) base south) ∙ Kn→ΩKn+10ₖ _
  lUnithelers zero m (loop i) x₁ x₂ = cong (Kn→ΩKn+1 _) (∪≡ zero (suc m) (inr (even-suc→odd x₁)) (inl x₂) (loop i) south) ∙ Kn→ΩKn+10ₖ _
  lUnithelers (suc n) m north x₁ x₂ = cong (Kn→ΩKn+1 _) (∪≡ (suc n) (suc m) (inr (even-suc→odd x₁)) (inl x₂) north south) ∙ Kn→ΩKn+10ₖ _
  lUnithelers (suc n) m south x₁ x₂ = cong (Kn→ΩKn+1 _) (∪≡ (suc n) (suc m) (inr (even-suc→odd x₁)) (inl x₂) south south) ∙ Kn→ΩKn+10ₖ _
  lUnithelers (suc n) m (merid a i) x₁ x₂ = cong (Kn→ΩKn+1 _) (∪≡ (suc n) (suc m) (inr (even-suc→odd x₁)) (inl x₂) (merid a i) south) ∙ Kn→ΩKn+10ₖ _

  lUnitheler : (n m : ℕ) (x : _) (x₁ : _) (x₂ : _) → cong (λ x → ∪-alt2 (suc n) (suc m) (inl x₁) (inl x₂) x north)
      (merid x) ≡ refl
  lUnitheler zero m x x₁ x₂ = {!!}
  lUnitheler (suc n) m x x₁ x₂ = {!!}

  main : (b : _) → cong (λ y → cong (λ x → ∪-alt2 (suc n) (suc m) (inl x₁) (inl x₂) x y)
      (merid a)) (merid b)
      ≡
      ({!!} ∙∙ cong (λ y → cong (λ x → ∪-alt (suc n) (suc m) (inl x₁) (inl x₂) x y)
      (merid a)) (merid b) ∙∙ sym (lUnithelers n m a x₁ x₂))
  main b =  (λ i → (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))) (rUnit (cong (∪-alt2 n (suc m) (inr (even-suc→odd x₁)) (inl x₂) a) (merid b)) i))
        ∙∙ cong (cong (Kn→ΩKn+1 (suc (n + suc (suc m)))))
                (λ i → (λ j → ∪≡ n (suc m) (inr (even-suc→odd x₁)) (inl x₂) a north (i ∧ j))
                    ∙∙ (λ j → ∪≡ n (suc m) (inr (even-suc→odd x₁)) (inl x₂) a (merid b j) i)
                    ∙∙ λ j → ∪≡ n (suc m) (inr (even-suc→odd x₁)) (inl x₂) a south (i ∧ ~ j))
        ∙∙ {!!}
        ∙∙ {!!}
        ∙∙ {!!}

  help1 : (y : _) → cong (λ x → ∪-alt2 (suc n) (suc m) (inl x₁) (inl x₂) x y) (merid a) ≡ cong (λ x → ∪-alt (suc n) (suc m) (inl x₁) (inl x₂) x y) (merid a)
  help1 y = {!!}
∪≡ (suc n) (suc m) (inl x₁) (inr x₂) x y = {!!}
∪≡ (suc n) (suc m) (inr x₁) q x y = {!!}
-}

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


miner : {k : ℕ} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m ⊎ is-odd m)
      → coHomK k → coHomK k
miner {k = zero} n m p q x = x --doesn't really make sense, but doesn't matter in practice
miner {k = suc k} n m p q = trMap (miner-h n m p q)


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

congMinner : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) → (P : 0ₖ (2 + k) ≡ 0ₖ _)  → cong (miner n m (inr p) (inr q)) P ≡ sym P
congMinner = {!!}

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

miner≡minus : {k : ℕ} (n m : ℕ) → (p : is-odd n) → (q : is-odd m) (x : coHomK (suc k)) → miner n m (inr p) (inr q) x ≡ -ₖ x
miner≡minus {k = k} n m p q = {!!}

{-
∪-alt-assoc : (n m l : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n)) (q : is-even (suc m) ⊎ is-odd (suc m)) (r : is-even (suc l) ⊎ is-odd (suc l))
              → (hLevHyp : (a b : ℕ) → isOfHLevel (2 + (suc (a + suc b))) (S₊ (suc (a + suc b))))
              → (qr : is-even (suc (m + suc l)) ⊎ is-odd (suc (m + suc l)))
              → (pr : is-even (suc (n + suc m)) ⊎ is-odd (suc (n + suc m)))
              → (x : (S₊ (suc n))) → (y : (S₊ (suc m))) (z : (S₊ (suc l)))
              → ∪-alt n (m + suc l) p qr x (trRec (hLevHyp m l) (λ x → x) (∪-alt m l q r y z))
              ≡ subst coHomK (sym (+-assoc (suc n) (suc m) (suc l))) (∪-alt (n + suc m) l pr r (trRec (hLevHyp n m) (λ x → x) (∪-alt n m p q x y)) z)
∪-alt-assoc zero zero zero p q r hLevHyp qr pr base base base = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr base base (loop i) = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr base (loop i) base = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr base (loop i) (loop i₁) = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) base base = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) base (loop i₁) = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) (loop i₁) base = refl
∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) (loop j) (loop k) = {!!}
∪-alt-assoc zero zero (suc l) p q r hLevHyp qr pr x y z = {!!}
∪-alt-assoc zero (suc m) l p q r hLevHyp qr pr x y z = {!!}
∪-alt-assoc (suc n) zero l p q r hLevHyp qr pr x y z = {!!}
∪-alt-assoc (suc n) (suc m) zero p q r hLevHyp qr pr x y z = {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) north y z = refl
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) south y z = refl
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) north z = refl
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) south z = refl
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) north = {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) south = {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) (merid a₂ i₂) = {!!}
  where

  cong-below : ∀ {ℓ} {A : Type ℓ} {x y z w pt : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → cong-∙∙ (λ x → pt) p q r ≡ rUnit refl
  cong-below p q r = refl

  help₁ : (a : _) (b : _) (c : _) → cong (λ a → cong (λ b → cong (λ c → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄)
      a
      (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆)
       (∪-alt (suc m) (suc l) (inl x₂) (inl x₃) b c))) (merid c)) (merid b)) (merid a)
      ≡
      {!!}{-
      ({!!} ∙∙ cong (λ a → cong (λ b → cong (λ a → subst coHomK
      (sym (λ i₁ → suc (suc (+-assoc n (suc (suc m)) (suc (suc l)) i₁))))
      (∪-alt (suc (n + suc (suc m))) (suc l) (inl x₅) (inl x₃)
       (rec₊ (hLevHyp (suc n) (suc m)) (λ x₆ → x₆)
        (∪-alt (suc n) (suc m) (inl x₁) (inl x₂) a b))
       c)) (merid a)) (merid b)) (merid c) ∙∙ {!!}) -}
  help₁ a b c =
       (λ r i j k → cong (cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))) ((sym (Kn→ΩKn+10ₖ _)
                 ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
                            (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c)))
                 ∙∙ Kn→ΩKn+10ₖ _)) j k)
    ∙∙ rUnit _
    ∙∙ (λ r → (λ i → rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))) (i ∧ r)) ∙∙ (λ i j k
                     → cong-∙∙ ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))) (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
                            (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c)))) (Kn→ΩKn+10ₖ _) r j k)
                     ∙∙ λ i → rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))) (~ i ∧ r))
    ∙∙ (λ r → (rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))))
            ∙∙ (λ i j k → (cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))))
                                 ((sym (Kn→ΩKn+10ₖ _)))
                        ∙∙ (cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))))
                                 (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
                                                     (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c))))
                        ∙∙ cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))))
                                 ((Kn→ΩKn+10ₖ _))) j k)
           ∙∙ sym (rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l)))))))))
    ∙∙ {!(cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
                           (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))))
                                 (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
                                                     (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c))))!}
    ∙∙ {!!}
    ∙∙ {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inr x₅) x y z = {!!} --⊥
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inr x₄) pr x y z = {!!} --⊥
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inr x₃) hLevHyp qr pr x y z = {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inr x₂) r hLevHyp qr pr x y z = {!!}
∪-alt-assoc (suc n) (suc m) (suc l) (inr x₁) q r hLevHyp qr pr x y z = {!!}
-}

∪-alt-anticomm : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n))
              → (q : is-even (suc m) ⊎ is-odd (suc m))
              → (x : (S₊ (suc n))) → (y : (S₊ (suc m)))
              → ∪-alt n m p q x y ≡ subber n m (miner (suc n) (suc m) p q (∪-alt m n q p y x))
∪-alt-anticomm zero zero (inr x) (inr x₁) base base = refl
∪-alt-anticomm zero zero (inr x) (inr x₁) base (loop i) = refl
∪-alt-anticomm zero zero (inr x) (inr x₁) (loop i) base = refl
∪-alt-anticomm zero zero (inr x) (inr x₁) (loop i) (loop j) k = helper' k i j
  where
  helper' : Path (typ ((Ω^ 2) (coHomK-ptd 2)))
                 (λ i j → ∪-alt zero zero (inr x) (inr x₁) (loop i) (loop j))
                 λ i j → subber zero zero (trMap (miner-h 1 1 (inr x) (inr x₁)) (∪-alt zero zero (inr x) (inr x₁) (loop j) (loop i)))
  helper' = inst2 _ _
           ∙∙ rUnit _
           ∙∙ cong (λ p → p ∙∙ (λ i j → ∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop (~ j))) ∙∙ sym p) (sym (transportRefl (λ _ _ → 0ₖ 2)))
         ∙∙ (λ k → (λ i → congMinner' 1 1 tt tt (λ j₁ → 0ₖ 2) (~ k ∧ i))
                 ∙∙ (λ i → congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop j)) (~ k))
                 ∙∙ λ i → congMinner' 1 1 tt tt (λ j₁ → 0ₖ 2) (~ k ∧ ~ i))
         ∙∙ sym (rUnit _)
         ∙∙ (λ k i j → transportRefl (trMap (miner-h 1 1 (inr x) (inr x₁)) (∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop j))) (~ k))
         ∙∙ inst _  _
∪-alt-anticomm zero (suc m) p q base north = refl
∪-alt-anticomm zero (suc m) p q base south = refl
∪-alt-anticomm zero (suc m) p q base (merid a i) = refl
∪-alt-anticomm zero (suc m) p q (loop i) north = refl
∪-alt-anticomm zero (suc m) p q (loop i) south = refl
∪-alt-anticomm zero (suc m) (inr x₁) (inl x) (loop i) (merid a j) =
  {!!}
  where -- cong suc (+-comm m (suc n) ∙ sym (+-suc n m))
  transp-lem : {!!}
  transp-lem = {!!}

  other-help : (m : ℕ) (a : _) (x : _)
             → sym (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
                    (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
              ≡ (((∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a)
           ∙∙
           (λ i₂ →
              subber zero m
              (trMap (miner-h 1 (suc m) (inr tt) (inr (even-suc→odd x)))
               (∪-alt m zero (inr (even-suc→odd x)) (inr tt) a (loop i₂))))
           ∙∙
           (sym (∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a))))
  other-help zero base tt =
    cong sym (transportRefl (refl ∙∙ (cong (∪-alt zero zero even-or-odd (inr tt) base) loop) ∙∙ refl))
           ∙∙ cong sym (sym (rUnit (cong (∪-alt zero zero even-or-odd (inr tt) base) loop)))
           ∙∙ sym (congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr tt) (inr tt) base (loop j)))
           ∙∙ (λ k i₂ → transportRefl (trMap (miner-h 1 1 (inr tt) (inr tt))
                                   (∪-alt zero zero (inr tt) (inr tt) base (loop i₂))) (~ k))
           ∙∙ rUnit _
  other-help zero (loop i) tt =
    cong sym (transportRefl (refl ∙∙ (cong (∪-alt zero zero even-or-odd (inr tt) (loop i)) loop) ∙∙ refl))
           ∙∙ cong sym (sym (rUnit (cong (∪-alt zero zero even-or-odd (inr tt) (loop i)) loop)))
           ∙∙ sym (congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr tt) (inr tt) (loop i) (loop j)))
           ∙∙ (λ k i₂ → transportRefl (trMap (miner-h 1 1 (inr tt) (inr tt))
                                   (∪-alt zero zero (inr tt) (inr tt) (loop i) (loop i₂))) (~ k))
           ∙∙ rUnit _
  other-help (suc m) north x =
    cong sym (λ k → (transport
       (λ i₂ →
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
       ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) north) loop)) (~ k))))
    ∙∙ (λ k → sym (transp
       (λ i₂ →
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
            λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) north (loop j))))
    ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) north) loop)))
     ∙ rUnit _
  other-help (suc m) south x =
    cong sym (λ k → (transport
       (λ i₂ →
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
       ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) south) loop)) (~ k))))
    ∙∙ (λ k → sym (transp
       (λ i₂ →
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
            λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) south (loop j))))
    ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) south) loop)))
     ∙ rUnit _
  other-help (suc m) (merid a i) x = -- cong suc (+-comm m (suc n) ∙ sym (+-suc n m))
       cong sym (λ k → (transport
       (λ i₂ →
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
          0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
       ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i)) loop)) (~ k))))
    ∙∙ (λ k → sym (transp
       (λ i₂ →
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
          0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
            λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i) (loop j))))
    ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) (merid a i)) loop)))
     ∙ rUnit _


  prop-help : (m : ℕ) → isProp (is-even m ⊎ is-odd m)
  prop-help m p q = {!!}

  helper' : (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))) ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (suc m))
          (∪-alt zero m (inr tt) even-or-odd (loop i₁) a))
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m))))))
      ≡
      flipSquare (
      cong (cong (subber zero (suc m)))
      (cong (cong (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inl x))))
       ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + 1))))))) ∙∙
       (cong (Kn→ΩKn+1 (suc (m + 1))) (sym (∪-alt-id m a) ∙∙
              (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙
              ∪-alt-id m a))
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + 1)))))))))
  helper' =
       cong (λ x → (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))) ∙∙ x
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
            (cong (cong (Kn→ΩKn+1 (suc (suc m))))
                  ((λ k → rUnit (cong (λ z → ∪-alt zero m (inr tt) (prop-help (suc m) even-or-odd (inr (even-suc→odd {n = suc (suc (suc m))} x)) k) z a) loop) k)
                ∙∙ (λ k → (λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a (k ∧ i))
                       ∙∙ (λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd {n = suc (suc (suc m))} x)) (loop i) a k)
                       ∙∙ λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a (k ∧ ~ i))
                ∙∙ sym (other-help m a x)))
    ∙∙ sym (sym-∙∙ ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))))
               (cong (Kn→ΩKn+1 (suc (suc m)))
                      (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
                                 (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a)))
               (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
    ∙∙ (λ k → sym (cong (cong (trMap-miner-Right 1 (suc (suc m)) (inr x₁) x (~ k)))
                   ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m)))))))
                   ∙∙ cong (Kn→ΩKn+1 (suc (suc m)))
                      (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
                                 (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))))
    ∙∙ inst _ _
    ∙∙ λ k i j →
         transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∨ ~ k))) (~ k)
             (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inl x))
               ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k))))))
               ∙∙ cong (Kn→ΩKn+1 ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k)))
                       (transp (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k ∧ i)) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k ∧ i))) k
                               (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
               ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k)))))) j i))
    {- λ k i j
      → subber zero (suc m)
         (rUnit ((cong (cong (trMap (miner-h 1 (suc (suc m)) p (inl x))))
       ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + 1))))))) ∙∙
       (cong (Kn→ΩKn+1 (suc (m + 1))) (sym (∪-alt-id m a) ∙∙
              (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙
              ∪-alt-id m a))
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + 1))))))))) (~ k) i j) -}
∪-alt-anticomm zero (suc m) (inr x₁) (inr x) (loop i) (merid a j) = {!!}
∪-alt-anticomm (suc n) zero p (inr x₁) x y = {!!}
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) (merid b j) k = helper' k i j
  where

  t-help : (n m : ℕ) (x : _) → transport (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) i))
                          (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) x) ≡ subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (subber n m x)
  t-help n m x = sym (substComposite coHomK (sym (+-suc m (suc n))) (cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) x)
             ∙∙ cong (λ y → subst coHomK y x) (isSetℕ _ _ _ _)
             ∙∙ substComposite coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m))) x

  subst-ₖ : {n m : ℕ} (x : coHomK n) → (p : n ≡ m) → subst coHomK p (-[ n ]ₖ x) ≡ (-ₖ (subst coHomK p x))
  subst-ₖ {n = n} x = J (λ m p → subst coHomK p (-[ n ]ₖ x) ≡ (-ₖ (subst coHomK p x)))
                    λ i → transportRefl (-ₖ (transportRefl x (~ i))) i

  subst2-ₖ : {n m l : ℕ} (x : coHomK n) → (p : n ≡ m) (q : m ≡ l) → subst coHomK q (subst coHomK p (-[ n ]ₖ x)) ≡ (-ₖ subst coHomK q (subst coHomK p x))
  subst2-ₖ x p q = sym (substComposite coHomK p q (-ₖ x)) ∙∙ subst-ₖ x (p ∙ q) ∙∙ cong -ₖ_ (substComposite coHomK p q x)

  helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (∪-alt n m (inr (even-suc→odd x₁)) (inr (even-suc→odd x₂)) a b))
           i₁))
       ∙∙
       (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
      ≡
      flipSquare
        (cong (cong (subber (suc n) (suc m)))
              (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inl x₁) (inl x₂))))
                ((((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
         ∙∙
         (λ i₁ →
            Kn→ΩKn+1 (suc (m + suc (suc n)))
            (Kn→ΩKn+1 (m + suc (suc n))
             (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
              (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))
             i₁))
         ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))))
  helper' = (λ i → (cong (cong ∣_∣)
       (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (∪-alt-anticomm n m (inr (even-suc→odd x₁)) (inr (even-suc→odd x₂)) a b i))
           i₁))
       ∙∙
       cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
         ∙∙ (λ i → (cong (cong ∣_∣)
       (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (subber n m (miner≡minus (suc n) (suc m) (even-suc→odd x₁) (even-suc→odd x₂) (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a) i)))
           i₁))
       ∙∙
       cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))) -- subst coHomK (cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
         ∙∙ ((λ i → (cong (cong ∣_∣)
       (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst2-ₖ (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a) (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m))) i)
           i₁))
       ∙∙
       cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))))
         ∙∙ (((λ i → (cong (cong ∣_∣)
       (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1-ₖ (n + suc (suc m)) (subst coHomK (λ i₃ → +-suc n (suc m) (~ i₃))
       (subst coHomK
        (λ i₃ →
           suc
           (((+-suc m n ∙ (λ i₄ → suc (+-comm m n i₄))) ∙
             (λ i₄ → +-suc n m (~ i₄)))
            i₃))
        (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))) i
           i₁))
       ∙∙
       cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))))
         ∙∙ sym (sym-∙∙ (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
                ((cong (Kn→ΩKn+1 (suc (n + suc (suc m)))) (
                  Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₃ → +-suc n (suc m) (~ i₃))
                    (subst coHomK
                     (λ i₃ →
                        suc
                        (((+-suc m n ∙ (λ i₄ → suc (+-comm m n i₄))) ∙
                          (λ i₄ → +-suc n m (~ i₄)))
                         i₃))
                     (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))))
                (((cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))))
         ∙∙ inst _ _
         ∙∙ cong flipSquare
                 (cong (λ x → sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
                              ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m)))) (
                                        Kn→ΩKn+1 (n + suc (suc m)) x)
                              ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
                       (sym (t-help _ _ (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))
         ∙∙ cong flipSquare (λ k i₁ i₂ →
            transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
               (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
            ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
                     (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
                        (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
                          (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
              (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))
            ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i₁ i₂))
         ∙∙ cong flipSquare
           (cong (cong (cong (subber (suc n) (suc m))))
             λ k i j → trMap-miner-Left (suc (suc n)) (suc (suc m)) x₁ (inl x₂) (~ k)
               ((((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
         ∙∙
         (λ i₁ →
            Kn→ΩKn+1 (suc (m + suc (suc n)))
            (Kn→ΩKn+1 (m + suc (suc n))
             (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
              (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))
             i₁))
         ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))) i j))
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) north = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) south = refl
∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) (merid b j) k = helper' k j i
  where
  helper' : (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))
           i₁))
       ∙∙
       (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ≡ cong (cong (subber (suc n) (suc m)))
          (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inl x₁) (inr x₂))))
            (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
            ∙∙
            cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
               (Kn→ΩKn+1 (m + suc (suc n))
                (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                 (subber m n
                  (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))))
            ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))))
  helper' =
       cong (λ x → sym (cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
                 ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
               (Kn→ΩKn+1 (n + suc (suc m)) x)
                 ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
           (cong (λ x → subst coHomK x (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)) (isSetℕ _ _ _ _)
         ∙∙ substComposite coHomK (cong suc (+-comm n (suc m) ∙ sym (+-suc m n))) (sym (+-suc m (suc n)) ∙ cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
                                             (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)
         ∙∙ substComposite coHomK (sym (+-suc m (suc n))) (cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
               (subber m n (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)))
    ∙∙ (λ k i j →
            transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
               (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
            ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
                     (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
                        (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
                          (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                            (subber m n (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)))))
            ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i j))
    ∙∙ λ k i j
      → subber (suc n) (suc m)
          (trMap-miner-Left (suc (suc n)) (suc (suc m)) x₁ (inr x₂) (~ k)
            ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
            ∙∙
            cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
               (Kn→ΩKn+1 (m + suc (suc n))
                (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                 (subber m n
                  (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))))
            ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))) i j))
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) (merid b j) k = helper' k i j
  where
  helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
       ∙∙
       (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (subber n m
             (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))))
       ∙∙
       (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
      ≡
      cong (cong (subber (suc n) (suc m)))
      (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inr x₁) (inl x₂))))
        (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
       ∙∙ cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
            (Kn→ΩKn+1 (m + suc (suc n))
             (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
              (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))
       ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))
  helper' =
       cong (λ x → sym (cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
                 ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
               (Kn→ΩKn+1 (n + suc (suc m)) x)
                 ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
              (sym (substComposite coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m)))
                   (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
            ∙∙ cong (λ x → subst coHomK x (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
                    (isSetℕ _ _ _ _)
            ∙∙ substComposite coHomK (sym (+-suc m (suc n)))
               (cong predℕ ((+-comm (suc m) (2 + n) ∙ (sym (+-suc (suc n) (suc m))))))
                 (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
    ∙∙ (λ k i j →
            transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
               (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
            ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
                     (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
                        (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
                          (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                            (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))))
            ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i j))
    ∙∙ λ k i j
      → subber (suc n) (suc m)
          (trMap-miner-Right (suc (suc n)) (suc (suc m)) (inr x₁) x₂ (~ k)
            ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
            ∙∙
            cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
               (Kn→ΩKn+1 (m + suc (suc n))
                (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                 (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))
            ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))) i j))
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south (merid a i) = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) north = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) south = refl
∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) (merid b j) k =
  helper' n m a b x₁ x₂ k i j
  where
  helper' : (n m : ℕ) (a : _) (b : _) (x₁ : _) (x₂ : _) → (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
       ∙∙
       (λ i₁ →
          Kn→ΩKn+1 (suc (n + suc (suc m)))
          (Kn→ΩKn+1 (n + suc (suc m))
           (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
            (∪-alt n m (inl (odd-suc→even x₁)) (inl (odd-suc→even x₂)) a b))
           i₁))
       ∙∙
       cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
      ≡
      flipSquare (cong (cong (subber (suc n) (suc m)))
      (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inr x₁) (inr x₂))))
       ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
         ∙∙
         (cong (
            Kn→ΩKn+1 (suc (m + suc (suc n))))
            (Kn→ΩKn+1 (m + suc (suc n))
             (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
              (∪-alt m n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
         ∙∙
         cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))
  helper' n (suc m) a b x₁ x₂ =
       cong (λ x → ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc (suc m))))))))
         ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc (suc m))) x)
         ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc (suc m))))))))))
              (cong (subst coHomK (λ i₂ → +-suc n (suc (suc m)) (~ i₂)))
                (∪-alt-anticomm n (suc m) (inl (odd-suc→even x₁)) (inl (odd-suc→even x₂)) a b)
            ∙∙ sym (substComposite coHomK (cong suc (+-comm (suc m) (suc n) ∙ sym (+-suc n (suc m)))) (sym (+-suc n (suc (suc m))))
                   (trMap
                     (miner-h (suc n) (suc (suc m)) (inl (odd-suc→even x₁))
                      (inl (odd-suc→even x₂)))
                     (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b
                      a)))
            ∙∙ cong (subst coHomK (cong suc (+-comm (suc m) (suc n) ∙ sym (+-suc n (suc m))) ∙ sym (+-suc n (suc (suc m)))))
                    (funExt⁻ (trMap-miner-Right (suc n) (suc (suc m)) ((inl (odd-suc→even x₁))) (odd-suc→even x₂))
                             (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a)) 
            ∙∙ cong (λ x → subst coHomK x (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a)) (isSetℕ _ _ _ _)
            ∙∙ substComposite
                coHomK
                (sym (+-suc (suc m) (suc n))) (cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))))
                (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))
    ∙∙ (λ k i j →
            transp (λ i → coHomK ((cong suc (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (i ∨ ~ k))) (~ k)
               (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k)))))))
            ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))) (~ k)))
                     (Kn→ΩKn+1 ((cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k))
                        (transp (λ i → coHomK ((cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k ∧ i))) k
                          (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
                            (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
            ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))) (~ k))))))) i j))
    ∙∙ inst _ _
    ∙∙ (λ k → (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m))))) (rUnit (inst4 ((((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
         ∙∙
         (cong (
            Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
            (Kn→ΩKn+1 ((suc m) + suc (suc n))
             (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
              (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
         ∙∙
         cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))))) k) k))
    ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
            (λ k → (transportRefl (λ _ _ → ∣ north ∣) (~ k)
                 ∙∙ (λ i → sym ((((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
         ∙∙
         (cong (
            Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
            (Kn→ΩKn+1 ((suc m) + suc (suc n))
             (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
              (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
         ∙∙
         cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))) i)))
         ∙∙ transportRefl (λ _ _ → ∣ north ∣) (~ k)))
    ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
            (λ k → (λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ refl (~ k ∧ i))
                 ∙∙ (λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ (((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
         ∙∙
         (cong (
            Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
            (Kn→ΩKn+1 ((suc m) + suc (suc n))
             (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
              (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
         ∙∙
         cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))) i) (~ k))
                 ∙∙ λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ refl (~ k ∧ ~ i))
    ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
            (sym (rUnit (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc (suc m))) (inr x₁) (inr x₂))))
       ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
         ∙∙
         (cong (
            Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
            (Kn→ΩKn+1 ((suc m) + suc (suc n))
             (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
              (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
         ∙∙
         cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))))))

{-
anti-com : (n m : ℕ) (x : S₊ (suc n)) (y : S₊ (suc m)) → ∪-help n m x y ≡ subber n m (minner n m (∪-help m n y x))
anti-com zero zero base base = refl
anti-com zero zero base (loop i) = refl
anti-com zero zero (loop i) base = refl
anti-com zero zero (loop i) (loop j) k = test k i j
  where
  p₁ = (λ i j → ∪-help 0 0 (loop i) (loop j))
  p₂ = (λ i j → -ₖ (∪-help 0 0 (loop j) (loop i)))
  lazy : inv' f p₁ ≡ inv' f p₂
  lazy = {!!} -- refl

  test : Path (Path (Path (coHomK 2) (0ₖ _) (0ₖ _)) refl refl) p₁ λ i j → ((subst coHomK (cong suc (+-comm zero 1 ∙ sym (+-suc zero zero))) (-ₖ (∪-help 0 0 (loop j) (loop i)))))
  test = (sym (Iso.rightInv f p₁) ∙ cong (fun f) lazy) ∙∙ Iso.rightInv f p₂ ∙∙ λ z i j → (transportRefl (-ₖ (∪-help 0 0 (loop j) (loop i))) (~ z))

anti-com zero (suc m) base north = refl
anti-com zero (suc m) base south = refl
anti-com zero (suc m) base (merid a i) = refl
anti-com zero (suc m) (loop i) north = refl
anti-com zero (suc m) (loop i) south = refl
anti-com zero (suc m) (loop i) (merid a j) = {!!}
anti-com (suc n) zero north base = refl
anti-com (suc n) zero north (loop i) = refl
anti-com (suc n) zero south base = refl
anti-com (suc n) zero south (loop i) = refl
anti-com (suc n) zero (merid a i) base = refl
anti-com (suc n) zero (merid a i) (loop j) = {!!}
anti-com (suc n) (suc m) north north = refl
anti-com (suc n) (suc m) north south = refl
anti-com (suc n) (suc m) north (merid a i) = refl
anti-com (suc n) (suc m) south north = refl
anti-com (suc n) (suc m) south south = refl
anti-com (suc n) (suc m) south (merid a i) = refl
anti-com (suc n) (suc m) (merid a i) north = refl
anti-com (suc n) (suc m) (merid a i) south = refl
anti-com (suc n) (suc m) (merid a i) (merid b j) k = fstt (~ k) j i
  where
  minnerId : {k : ℕ} (n m : ℕ) (x : coHomK (suc k))
          → (minner (suc n) (suc m) ∘ minner n m) x ≡ x
  minnerId n m = trElim {!!} {!!}
    where
    re : {k : ℕ} (n m : ℕ) → (a : Susp (S₊ (suc k))) →
      (minner (suc n) (suc m) ∘ minner n m) ∣ a ∣ ≡ ∣ a ∣
    re n m = {!!}

  sndd : (n m : ℕ) → (a : _) → subst coHomK (cong predℕ (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
                                                                   (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
                                                                     (subber m n a)) ≡ subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) a
  sndd n m a = {!!}
            ∙∙ {!!}
            ∙∙ {!!}

  3rd : (n m : ℕ) → (a : _) → subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (minner m n a) ≡ minner m n (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) a)
  3rd n m a i = transp (λ i₂ → coHomK (+-suc n (suc m) (~ i₂ ∧ ~ i))) i (minner m n (transp (λ i₂ → coHomK (+-suc n (suc m) (~ i₂ ∨ ~ i))) (~ i) a))

  4th : (n m : ℕ) → (a : _) → (sym (cong (cong (minner (suc n) (suc m))) (Kn→ΩKn+10ₖ _))
                              ∙∙ cong (cong (minner (suc n) (suc m))) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a)))
                              ∙∙ cong (cong (minner (suc n) (suc m))) (Kn→ΩKn+10ₖ _)) ≡
                                sym (cong (cong (minner (suc n) (suc m) ∘ minner m n)) (Kn→ΩKn+10ₖ _))
                              ∙∙ cong (cong (minner (suc n) (suc m) ∘ minner m n)) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) a))
                              ∙∙ cong (cong (minner (suc n) (suc m) ∘ minner m n)) (Kn→ΩKn+10ₖ _)
  4th n m a = {!!}
    where
    t : cong (cong (minner (suc n) (suc m))) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a))) ≡ {!minner m n a!}
    t = (λ _ i j → minner (suc n) (suc m) (Kn→ΩKn+1 (suc (n + suc (suc m))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a) i) j))
     ∙∙ {!!}
     ∙∙ {!!}

  -- trElim {!!} {!λ {north → refl ; south → refl ; (merid a i) → refl}!}

  fstt : cong (cong (subber (suc n) (suc m)))
         (cong (cong (minner (suc n) (suc m)))
          (((λ i₁ j₁ →
               ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
            ∙∙
            (λ i₁ →
               Kn→ΩKn+1 (suc (m + suc (suc n)))
               (Kn→ΩKn+1 (m + suc (suc n))
                (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))
                i₁))
            ∙∙
            (λ i₁ j₁ →
               ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣)))) ≡
               flipSquare ((λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)
                                                          ∙∙ (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
                                                                 (Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))))
                                                         ∙∙  λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)
  fstt = cong (cong (cong (subber (suc n) (suc m))))
              (cong-∙∙ (cong (minner (suc n) (suc m)))
                (λ i₁ j₁ →
               ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
               (cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
                 (Kn→ΩKn+1 (m + suc (suc n))
                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))))
               (λ i₁ j₁ →
               ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣))
      ∙∙ cong-∙∙ (cong (subber (suc n) (suc m)))
                 (cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣))
                 (cong (cong (minner (suc n) (suc m))) (cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
                 (Kn→ΩKn+1 (m + suc (suc n))
                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a)))))
                 (cong (cong (minner (suc n) (suc m))) λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣)
      ∙∙ (λ k → (λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
                                  ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k))) (~ i₁) j₁ ∣)) i j))
              ∙∙ (λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
                                  (minner (suc n) (suc m) (Kn→ΩKn+1 ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k)
                                    (Kn→ΩKn+1 (cong predℕ (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k)
                                      (transp (λ i → coHomK (predℕ ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (k ∧ i)))) (~ k)
                                              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (anti-com m n b a k))) i) j)))
              ∙∙ λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
                                  ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k))) i₁ j₁ ∣)) i j))
      ∙∙ (λ k → (λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)) i j))
              ∙∙ (λ i j → minner (suc n) (suc m) ((Kn→ΩKn+1 (suc (n + suc (suc m))))
                                    (Kn→ΩKn+1 (n + suc (suc m)) (sndd n m (minner m n (∪-help n m a b)) k) i) j))
              ∙∙ λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)) i j))
      ∙∙ (λ k → (λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)) i j))
              ∙∙ (λ i j → minner (suc n) (suc m) ((Kn→ΩKn+1 (suc (n + suc (suc m))))
                                    (Kn→ΩKn+1 (n + suc (suc m)) (3rd n m (∪-help n m a b) k) i) j))
              ∙∙ λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
                                          ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)) i j))
      ∙∙ 4th n m (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))
      ∙∙ sym (cong-∙∙ (cong (minner (suc n) (suc m) ∘ minner m n)) ((λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣))
                                                               (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
                                                                 (Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))))
                                                               λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)
      ∙∙ {!!}
      ∙∙ inst _ _ -}

  {- (λ i → cong (cong (minner (suc n) (suc m)))
              (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (subst coHomK (sym (+-suc m (suc n))) (indhyp n m a b i)))))
                ∙∙ (λ i → cong (cong (minner (suc n) (suc m)))
              (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (minnerf n m (∪-help n m a b) i))))
                ∙∙ (λ i → {!!})
                ∙∙ {!!}
                ∙∙ {!!} -}

--   -* = -ₖ2 {m = suc (suc n) + suc (suc m)} (m + suc (suc (m + n · suc (suc m))))
--   test : (n m : ℕ) → (a : _) (b : _)
--        → cong (cong (subber (suc n) (suc m)
--       ∘ (minner (suc n) (suc m))))
--        (((λ i₁ j₁ →
--             ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
--          ∙∙
--          (λ i₁ →
--             Kn→ΩKn+1 (suc (m + suc (suc n)))
--             (Kn→ΩKn+1 (m + suc (suc n))
--              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))
--              i₁))
--          ∙∙
--          (λ i₁ j₁ →
--             ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣))) ≡
--           {!!}
--   test n m a b = (λ i → cong (cong (subber (suc n) (suc m))) (cong-∙∙ (cong (minner (suc n) (suc m))) (cong (cong ∣_∣) (sym (rCancel (merid (ptSn _))))) (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a)))) (cong (cong ∣_∣) (rCancel (merid (ptSn _)))) i)) ∙∙ {!!} ∙∙ {!!} ∙∙ {!!} ∙∙ {!!}


-- -- {-
-- -- ∪-help (suc n) (suc m) north north = 0ₖ _
-- -- ∪-help (suc n) (suc m) north south = 0ₖ _
-- -- ∪-help (suc n) (suc m) north (merid a i) = 0ₖ _
-- -- ∪-help (suc n) (suc m) south north = 0ₖ _
-- -- ∪-help (suc n) (suc m) south south = 0ₖ _
-- -- ∪-help (suc n) (suc m) south (merid a i) = 0ₖ _
-- -- ∪-help (suc n) (suc m) (merid a i) north = 0ₖ _
-- -- ∪-help (suc n) (suc m) (merid a i) south = 0ₖ _
-- -- ∪-help (suc n) (suc m) (merid a i) (merid b j) = ?
-- --   hcomp (λ k → λ {(j = i0) → {!!}
-- --                  ; (j = i1) → {!!}
-- --                  ; (i = i0) → {!!}
-- --                  ; (i = i1) → {!!}})
-- --         {!Kn→ΩKn+1 _ (Kn→ΩKn+1 _ (∪-help n m a b) i) j!} -}

-- -- ⌣ₖ'' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- ⌣ₖ'' zero m x = {!!}
-- -- ⌣ₖ'' (suc n) m x = {!m!}

-- -- ⌣ₖ' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- ⌣ₖ' zero zero x = (λ y → y ℤ∙ x) , refl
-- -- ⌣ₖ' zero (suc m) x = ^ₖ x , ^ₖ-base x
-- -- ⌣ₖ' (suc n) zero x =
-- --   subst (λ m → coHomK-ptd zero →∙ coHomK-ptd (suc m)) (+-comm zero n)
-- --         ((λ y → ^ₖ y x) , refl)
-- -- ⌣ₖ' (suc n) (suc m) =
-- --   trRec (subst (isOfHLevel (3 + n))
-- --             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (wow (suc n) m))
-- --     (k n m)
-- -- _⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n + m)
-- -- _⌣ₖ_ {n = n} {m = m} x = fst (⌣ₖ' n m x)

-- -- open import Cubical.Data.Sum
-- -- open import Cubical.Data.Empty renaming (rec to ⊥-rec)
-- -- open import Cubical.Data.Nat.Order

-- -- -ₖ2 : {m : ℕ} (n : ℕ) → coHomK m → coHomK m
-- -- -ₖ2 zero x = x
-- -- -ₖ2 (suc zero) x = -ₖ x
-- -- -ₖ2 (suc (suc n)) x = -ₖ2 n x

-- -- ⌣2 : (n m : ℕ) → (n ≤ m) ⊎ (m < n) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- ⌣2 zero m (inl x) y = ^ₖ y , ^ₖ-base y
-- -- ⌣2 (suc n) zero (inl x) = ⊥-rec (help _ _ (snd x))
-- --   where
-- --   help : (n m : ℕ) → m + suc n ≡ zero → ⊥
-- --   help n zero p = ⊥-rec (snotz p)
-- --   help n (suc m) p = ⊥-rec (snotz p)
-- -- ⌣2 (suc n) (suc m) (inl x) = trRec (subst (isOfHLevel (3 + n))
-- --             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (wow (suc n) m))
-- --     (k n m)
-- -- ⌣2 zero m (inr x) y = (λ z → fst (⌣2 zero m (inl (m , +-comm m zero)) y) z) , {!!}
-- -- ⌣2 (suc n) m (inr x) y = {!!}

-- -- -ₖ'_ : {n : ℕ} → coHomK n → coHomK n
-- -- -ₖ'_ {n = zero} x = 0 - x
-- -- -ₖ'_ {n = suc n} = trMap (help n)
-- --   where
-- --   help : (n : ℕ) → S₊ (suc n) → S₊ (suc n) 
-- --   help zero base = base
-- --   help zero (loop i) = loop (~ i)
-- --   help (suc n) north = south
-- --   help (suc n) south = north
-- --   help (suc n) (merid a i) = merid a (~ i)

-- -- S1case : S₊ 1 → S₊ 1 → coHomK 2
-- -- S1case base y = ∣ north ∣
-- -- S1case (loop i) base = ∣ (merid base ∙ sym (merid base)) i ∣
-- -- S1case (loop i) (loop j) = ∣ (merid (loop j) ∙ sym (merid base)) i ∣

-- -- lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
-- --          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
-- --                    (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- -- lem = {!!}

-- -- lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- -- lem₂ = {!!}

-- -- lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- -- lem₃ = {!!}

-- -- lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- -- lem₄ = {!!}


-- -- test :  (cong (λ x → merid x ∙ sym (merid base)) (loop)) ∙ (cong (λ x → merid base ∙ sym (merid x)) loop) ≡ refl
-- -- test = sym (cong₂Funct (λ x y → merid x ∙ sym (merid y)) loop loop) ∙ help
-- --   where
-- --   help : cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) loop loop ≡ refl
-- --   help = (λ i → cong (λ x → merid x ∙ (sym (merid x))) loop) ∙ rUnit _
-- --               ∙ (λ i → (λ j → rCancel (merid base) (i ∧ j)) ∙∙ (λ j → rCancel (merid (loop j)) i) ∙∙ λ j → rCancel (merid base) (i ∧ ~ j)) ∙ (λ i → (λ j → rCancel (merid base) (j ∧ ~ i)) ∙∙ refl ∙∙ (λ j → rCancel (merid base) (~ j ∧ ~ i))) ∙ sym (rUnit refl)
-- --   t2 : (x y : S¹) (p : x ≡ y) → cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) p p ≡ {!!}
-- --   t2 = {!!}

-- -- wiho : Path (Path (Path (coHomK 2) ∣ north ∣ ∣ north ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣)) (λ j i →  ∣ (merid (loop (~ j)) ∙ sym (merid base)) i ∣) (λ j i →  ∣ (merid base ∙ sym (merid (loop j))) i ∣)
-- -- wiho = {!!}



-- -- S1caseeq : (x y : S₊ 1) → S1case x y ≡ (-ₖ S1case y x)
-- -- S1caseeq base base = refl
-- -- S1caseeq base (loop i) j = -ₖ (∣ (rCancel (merid base) (~ j) i) ∣)
-- -- S1caseeq (loop i) base j = ∣ rCancel (merid base) j i ∣
-- -- S1caseeq (loop i) (loop j) r =
-- --   hcomp (λ k → λ { (i = i0) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
-- --                   ; (i = i1) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
-- --                   ; (j = i0) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
-- --                   ; (j = i1) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
-- --                   ; (r = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ k) i
-- --                   ; (r = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ k) j})
-- --         (
-- --     hcomp (λ k → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
-- --                     ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
-- --                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
-- --                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
-- --                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- --                     ; (r = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (sym ((cong ∣_∣ (merid base)))) (~ k) j})
-- --           (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
-- --                     ; (i = i1) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
-- --                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
-- --                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
-- --                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- --                     ; (r = i1) → (wiho k i ∙ sym (cong ∣_∣ (merid base ∙ sym (merid base)))) j})
-- --                  (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
-- --                                   ; (i = i1) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
-- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i -- {!rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j!}
-- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i -- rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ k))) r i -- rCancel (cong ∣_∣ (merid base)) r i
-- --                                   ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i -- (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- --                                   ; (r = i1) → ((λ j →  ∣ compPath-filler (merid (loop (~ i))) (sym (merid base)) k j  ∣) ∙ λ j →  ∣ compPath-filler (merid base) (sym (merid base)) k (~ j)  ∣) j})
-- --                         (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
-- --                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
-- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
-- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
-- --                                   ; (r = i0) → p₂ (~ k) j i 
-- --                                   ; (r = i1) → p₁ (~ k) j i})
-- --                                   (p₁≡p₂ (~ r) j i)))))
-- --     where
-- --     p₁ : (z i j : I) → coHomK 2
-- --     p₁ z i j = hfill (λ k → λ { (i = i0) → 0ₖ 2
-- --                                   ; (i = i1) → 0ₖ 2
-- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) k i
-- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) k i })
-- --                    (inS ((cong ∣_∣ (merid (loop (~ j))) ∙ sym (cong ∣_∣ (merid base))) i)) z

-- --     p₂ : (z i j : I) → coHomK 2
-- --     p₂ z i j =
-- --       hfill (λ k → λ { (j = i0) → 0ₖ 2
-- --                                   ; (j = i1) → 0ₖ 2
-- --                                   ; (i = i0) → rCancel (cong ∣_∣ (merid base)) k j -- ∣ rCancel ((merid base)) k j ∣
-- --                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) k j }) -- ∣ rCancel ((merid base)) k j ∣})
-- --                    (inS ((cong ∣_∣ (merid (loop i)) ∙ sym (cong ∣_∣ (merid base))) j)) z -- (∣ (merid (loop i) ∙ sym (merid base)) j ∣)


-- --     open import Cubical.Foundations.Equiv.HalfAdjoint

-- --     f : Iso Int (typ ((Ω^ 2) (coHomK-ptd 2)))
-- --     f = compIso (Iso-Kn-ΩKn+1 0) (invIso (congIso (invIso (Iso-Kn-ΩKn+1 1))))

-- --     -- reduce everything to a computation: f (λ i j → p₁ i1 i j) ≡ f (λ i j → p₂ i1 i j) holds definitionally
-- --     p₁≡p₂ : Path (typ ((Ω^ 2) (coHomK-ptd 2))) (λ i j → p₁ i1 i j) (λ i j → p₂ i1 i j)
-- --     p₁≡p₂ = sym (rightInv f (λ i j → p₁ i1 i j)) ∙ rightInv f (λ i j → p₂ i1 i j)


-- -- {-
-- -- i = i0 ⊢ S1caseeq base (loop j) r
-- -- i = i1 ⊢ S1caseeq base (loop j) r
-- -- j = i0 ⊢ S1caseeq (loop i) base r
-- -- j = i1 ⊢ S1caseeq (loop i) base r
-- -- r = i0 ⊢ S1case (loop i) (loop j)
-- -- r = i1 ⊢ -ₖ S1case (loop j) (loop i)
-- -- -}

-- -- mainCommLem : (n : ℕ) → (x y : S₊ (suc n)) → fst (k n n x) ∣ y ∣ ≡ -ₖ2 ((suc n) · (suc n)) (fst (k n n y) ∣ x ∣)
-- -- mainCommLem zero base base = refl
-- -- mainCommLem zero (loop i) base j = Kn→ΩKn+10ₖ 1 j i
-- -- mainCommLem zero base (loop i) j = -ₖ (Kn→ΩKn+10ₖ 1 (~ j) i)
-- -- mainCommLem zero (loop r) (loop i) j = {!!}
-- -- mainCommLem (suc n) x y = {!!}

-- -- -- (λ z → -ₖ2 (n · m) (subst coHomK (+-comm m n) (fst (⌣2 m n (inl ((suc (fst x)) , (sym (+-suc (fst x) m) ∙ snd x))) z) y))) , {!!}


-- -- -- _⌣_ : ∀ {ℓ} {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n + m) A
-- -- -- _⌣_ {n = n} {m = m} = sRec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

-- -- -- -ₖ̂_ : (n : ℕ) {m : ℕ} → coHomK m → coHomK m
-- -- -- -ₖ̂ zero = λ x → x
-- -- -- (-ₖ̂ suc n) {m = m} x = -[ m ]ₖ (-ₖ̂ n) x

-- -- -- sisi : (n m : ℕ) → (x : coHomK n) (y : coHomK m) → (x ⌣ₖ y) ≡ -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (y ⌣ₖ x))
-- -- -- sisi zero m = {!!}
-- -- -- sisi (suc n) zero = {!!}
-- -- -- sisi (suc n) (suc m) = {!!}


-- -- -- wowzie : (n m : ℕ) → (x : S₊ (suc n)) → (y : S₊ (suc m)) → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) ∣ y ∣ ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) ∣ y ∣) ∣ x ∣))
-- -- -- wowzie zero zero x y = {!!}
-- -- -- wowzie zero (suc zero) = {!!}
-- -- -- wowzie zero (suc (suc m)) x y = {!!}
-- -- -- wowzie (suc n) m x y = {!!}

-- -- -- ptpt : (n m : ℕ) → (x : coHomK n) → (-ₖ̂ (n · m)) (subst coHomK (+-comm m n) (fst (⌣ₖ' m n (snd (coHomK-ptd m))) x)) ≡ 0ₖ _
-- -- -- ptpt zero zero x = transportRefl (x ℤ∙ 0) ∙ ∙-comm x 0
-- -- -- ptpt zero (suc m) x = {!!}
-- -- -- ptpt (suc n) zero = {!refl!}
-- -- -- ptpt (suc zero) (suc zero) _ = refl
-- -- -- ptpt (suc zero) (suc (suc m)) _ = {!!}
-- -- -- ptpt (suc (suc n)) (suc m) _ = {!!}

-- -- -- test : (n m : ℕ) → (x : coHomK (suc n)) → ⌣ₖ' (suc n) (suc m) x ≡ ((λ y → -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) x))) , ptpt (suc n) (suc m) x)
-- -- -- test n m = trElim {!!} λ a → ΣPathP ((funExt (λ x → funExt⁻  (cong fst (help x)) a)) , {!!})
-- -- --   where
-- -- --   help : (y : coHomK (suc m)) → Path (S₊∙ (suc n) →∙ coHomK-ptd _) ((λ x → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) y) , {!!}) ((λ x → -ₖ̂_ ((suc n) · (suc m)) ((subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) ∣ x ∣)))) , {!!})
-- -- --   help = {!!}

-- -- -- cong-ₖ : (n : ℕ) → (p : typ ((Ω^ 2) (coHomK-ptd 1))) → cong (cong (-ₖ_)) p ≡ {!!}
-- -- -- cong-ₖ = {!!}

-- -- -- ptCP∞ : (n m : ℕ) (x : coHomK n) → ⌣ₖ' n m x ≡ ((λ y → -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (fst (⌣ₖ' m n y) x))) , ptpt n m x)
-- -- -- ptCP∞ zero m x = {!!}
-- -- -- ptCP∞ (suc n) zero x = {!!}
-- -- -- ptCP∞ (suc n) (suc m) = trElim {!!} {!!}
-- -- --   where
-- -- --   help : (n m : ℕ) → (s : S₊ (suc n)) (l : _) → fst (k n m s) l ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) l) ∣ s ∣))
-- -- --   help zero zero s =
-- -- --     trElim (λ _ → isOfHLevelTrunc 4 _ _)
-- -- --            λ a → {!!} ∙∙ (λ i → -ₖ transportRefl (fst (k 0 0 a) ∣ s ∣) (~ i)) ∙∙ λ i → -ₖ (subst coHomK (rUnit (λ i → 2) i) (fst (k 0 0 a) ∣ s ∣))
-- -- --     where
-- -- --     r : cong (fst (k zero zero base)) (λ i → ∣ loop i ∣) ≡ cong (λ x → -ₖ (fst (k 0 0 x) ∣ base ∣)) loop
-- -- --     r i = cong (λ x → -ₖ x) (Kn→ΩKn+10ₖ 1 (~ i))

-- -- --     l : cong (λ x → fst (k 0 0 x) ∣ base ∣) loop ≡ cong (λ x → -ₖ (fst (k zero zero base) x)) (λ i → ∣ loop i ∣)
-- -- --     l i = Kn→ΩKn+10ₖ 1 i

-- -- --     r-l : Square {!λ i j → (fst (k 0 0 (loop (i ∧ j)))) (∣ loop j ∣)!} {!cong (λ x → -ₖ fst (k zero zero base) x) (λ i → ∣ loop i ∣)!} l r
-- -- --     -- PathP (λ i → {!cong (λ x → fst (k 0 0 x) ∣ base ∣) loop!} ≡ {!!}) l r
-- -- --     r-l = {!!}

-- -- --     lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
-- -- --          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
-- -- --                   (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- -- --     lem = {!!}

-- -- --     lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- -- --     lem₂ = {!!}

-- -- --     lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- -- --     lem₃ = {!!}

-- -- --     lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- -- --     lem₄ = {!!}

-- -- --     characFun≡S¹ : ∀ {ℓ} {A : Type ℓ} (f g : S¹ → S¹ → A)
-- -- --                   → (p : f base base ≡ g base base)
-- -- --                   → (ppₗ : PathP (λ i → p i ≡ p i) (cong (f base) loop) (cong (g base) loop))
-- -- --                   → (ppᵣ : PathP (λ i → p i ≡ p i) (cong (λ x → f x base) loop ) (cong (λ x → g x base) loop))
-- -- --                   → PathP (λ i → ppₗ i ≡ ppᵣ i) {!λ i j → f (loop i) (loop j)!} {!!}
-- -- --                   → (s t : S¹) → f s t ≡ g s t
-- -- --     characFun≡S¹ f g p ppl ppr pp base base = p
-- -- --     characFun≡S¹ f g p ppl ppr pp base (loop i) j = ppl j i
-- -- --     characFun≡S¹ f g p ppl ppr pp (loop i) base j = ppr j i
-- -- --     characFun≡S¹ f g p ppl ppr pp (loop i) (loop k) j = {!!}

-- -- --     help2 : (s a : S¹) → fst (k zero zero s) ∣ a ∣ ≡ -ₖ (fst (k 0 0 a) ∣ s ∣)
-- -- --     help2 base base = refl
-- -- --     help2 base (loop i) j = r j i
-- -- --     help2 (loop i) base j = l j i
-- -- --     help2 (loop i) (loop j) s =
-- -- --       hcomp (λ r → λ { (i = i0) → -ₖ lem (merid base) 3 r (~ s) j
-- -- --                        ; (i = i1) → -ₖ lem (merid base) 3 r (~ s) j
-- -- --                        ; (j = i0) → lem (merid base) 3 r s i
-- -- --                        ; (j = i1) → lem (merid base) 3 r s i
-- -- --                        ; (s = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ r) i
-- -- --                        ; (s = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ r) j })
-- -- --             (hcomp (λ r → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- -- --                        ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- -- --                        ; (j = i0) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- -- --                        ; (j = i1) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- -- --                        ; (s = i0) → (cong ∣_∣ (merid (loop j)) ∙ cong ∣_∣ (sym (merid base))) i
-- -- --                        ; (s = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (cong ∣_∣ (sym (merid base))) (~ r) j })
-- -- --                    (hcomp (λ r → λ { (i = i0) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- -- --                        ; (i = i1) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- -- --                        ; (j = i0) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- -- --                        ; (j = i1) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- -- --                        ; (s = i0) → {!(cong ∣_∣ (λ i → merid (loop j) (i ∨ ~ r)) ∙ cong ∣_∣ (sym (λ i → merid base (i ∨ ~ r)))) i!}
-- -- --                        ; (s = i1) → (((cong ∣_∣ (lem₃ (merid base) (sym (merid (loop i))) r))) ∙ sym (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r))) j })
-- -- --                          {!!}))
-- -- --       where
-- -- --       help3 : {!!}
-- -- --       help3 = {!!}
-- -- --   help zero (suc m) s l = {!!}
-- -- --   help (suc n) m s l = {!i = i0 ⊢ help2 base (loop j) s
-- -- -- i = i1 ⊢ help2 base (loop j) s
-- -- -- j = i0 ⊢ help2 (loop i) base s
-- -- -- j = i1 ⊢ help2 (loop i) base s
-- -- -- s = i0 ⊢ fst (k zero zero (loop i))
-- -- --          ∣ loop j ∣
-- -- -- s = i1 ⊢ -ₖ
-- -- --          fst (k 0 0 (loop j)) ∣ loop i ∣!}

-- -- -- -- ⌣ₖ∙ : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- -- ⌣ₖ∙ zero zero = λ x → (λ y → y ℤ∙ x) , refl
-- -- -- -- ⌣ₖ∙ zero (suc zero) x = (trMap λ {base → base ; (loop i) → intLoop x i}) , refl
-- -- -- -- ⌣ₖ∙ zero (suc (suc m)) = {!!}
-- -- -- -- ⌣ₖ∙ (suc n) zero = {!!}
-- -- -- -- ⌣ₖ∙ (suc zero) (suc m) = {!!}
-- -- -- -- ⌣ₖ∙ (suc (suc n)) (suc zero) = {!!}
-- -- -- -- ⌣ₖ∙ (suc (suc n)) (suc (suc m)) = trRec {!wow (suc n) (suc m)!} {!!}
-- -- -- --   where
-- -- -- --   helpME! : Susp (S₊ (suc n)) →
-- -- -- --       coHomK (suc m) → coHomK (suc (suc (n + (suc m))))
-- -- -- --   helpME! north x = 0ₖ _
-- -- -- --   helpME! south x = 0ₖ _
-- -- -- --   helpME! (merid a i) x = Kn→ΩKn+1 (suc (n + suc m)) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i
-- -- -- --   {- (λ x → Kn→ΩKn+1 _ (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i) , λ j → (cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) m ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i 
-- -- -- --     where
-- -- -- --     help : (n m : ℕ) (a : _) → Kn→ΩKn+1 (suc (n + (suc m)))
-- -- -- --       (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst (snd (coHomK-ptd (suc m)))) ≡ refl
-- -- -- --     help n m a = cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m))) -}
