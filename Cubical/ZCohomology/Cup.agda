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
                                 (isOfHLevel↑∙ (suc n) m))
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
                                 (isOfHLevel↑∙' (suc m) n))) λ y → (λ x → ∪-help n m x y) , ptHelp n m y

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

{-
zero-fun : S₊ 1 → S₊ 1 → coHomK 2
zero-fun base y = 0ₖ _
zero-fun (loop i) base = 0ₖ _
zero-fun (loop i) (loop j) =
  hcomp (λ k → λ {(j = i0) → 0ₖ 2
                 ; (j = i1) → ∣ merid base (~ k) ∣
                 ; (i = i0) → ∣ merid base (~ k ∧ j) ∣
                 ; (i = i1) → ∣ merid base (~ k ∧ j) ∣})
        ∣ merid (loop i) j ∣
zero-l : (m : ℕ) → (S₊ 1 → (S₊ (suc (suc m))) → coHomK (1 + suc (suc m)))
zero-r : (n : ℕ) → (S₊ (suc (suc n))) → S₊ 1 → coHomK (suc (suc n) + 1)
zero-l-id : (m : ℕ) (a : _) → zero-l m base a ≡ 0ₖ _
zero-l n base y = 0ₖ _
zero-l zero (loop i) north = 0ₖ _
zero-l zero (loop i) south = 0ₖ _
zero-l zero (loop i) (merid a j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _) (cong (λ z → zero-fun z a) loop)
  ∙∙ Kn→ΩKn+10ₖ _) i j
zero-l (suc n) (loop i) north = 0ₖ _
zero-l (suc n) (loop i) south = 0ₖ _
zero-l (suc n) (loop i) (merid a j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 (suc (suc (suc n))))
          (cong (λ z → zero-l n z a) loop)
  ∙∙ Kn→ΩKn+10ₖ _) i j
zero-r n x y = subber (suc n) 0 (miner (suc (suc n)) 1 even-or-odd (inr tt) (zero-l n y x))
zero-l-id zero a = refl
zero-l-id (suc m) a = refl

∪-alt-even-even : (n m : ℕ) → is-even (suc n) → is-even (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt-odd-odd : (n m : ℕ) → is-odd (suc n) → is-odd (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt-even-odd : (n m : ℕ) → is-even (suc n) → is-odd (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt-odd-even : (n m : ℕ) → is-odd (suc n) → is-even (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt-even-even (suc n) (suc m) evn evm north y = 0ₖ _
∪-alt-even-even (suc n) (suc m) evn evm south y = 0ₖ _
∪-alt-even-even (suc n) (suc m) evn evm (merid a i) north = 0ₖ _
∪-alt-even-even (suc n) (suc m) evn evm (merid a i) south = 0ₖ _
∪-alt-even-even (suc n) (suc m) evn evm (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _)
          (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m))) (∪-alt-odd-odd n m (even-suc→odd evn) (even-suc→odd evm) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt-odd-odd zero zero odn odm x y = zero-fun x y
∪-alt-odd-odd zero (suc m) odn odm x y = zero-l m x y
∪-alt-odd-odd (suc n) zero odn odm x y = zero-r n x y
∪-alt-odd-odd (suc n) (suc m) odn odm north y = 0ₖ _
∪-alt-odd-odd (suc n) (suc m) odn odm south y = 0ₖ _
∪-alt-odd-odd (suc n) (suc m) odn odm (merid a i) north = 0ₖ _
∪-alt-odd-odd (suc n) (suc m) odn odm (merid a i) south = 0ₖ _
∪-alt-odd-odd (suc n) (suc m) odn odm (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _)
          (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m))) (∪-alt-even-even n m (odd-suc→even odn) (odd-suc→even odm) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt-even-odd (suc n) zero evn odm x y = zero-r n x y
∪-alt-even-odd (suc n) (suc m) evn odm north y = 0ₖ _
∪-alt-even-odd (suc n) (suc m) evn odm south y = 0ₖ _
∪-alt-even-odd (suc n) (suc m) evn odm (merid a i) north = 0ₖ _
∪-alt-even-odd (suc n) (suc m) evn odm (merid a i) south = 0ₖ _
∪-alt-even-odd (suc n) (suc m) evn odm (merid a i) (merid b j) =
  (sym (Kn→ΩKn+10ₖ _)
  ∙∙ cong (Kn→ΩKn+1 _)
          (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m))) (∪-alt-odd-even n m (even-suc→odd evn) (odd-suc→even odm) a b)))
  ∙∙ Kn→ΩKn+10ₖ _) i j
∪-alt-odd-even zero (suc m) odn evm x y = zero-l m x y
∪-alt-odd-even (suc n) (suc m) odn evm x y = subber (suc n) (suc m) (∪-alt-even-odd (suc m) (suc n) evm odn y x)

∪-alt' : (n m : ℕ) → is-even (suc n) ⊎ is-odd (suc n) → is-even (suc m) ⊎ is-odd (suc m) → (S₊ (suc n) → (S₊ (suc m)) → coHomK (suc n + suc m))
∪-alt' n m (inl x) (inl x₁) = ∪-alt-even-even n m x x₁
∪-alt' n m (inl x) (inr x₁) = ∪-alt-even-odd n m x x₁
∪-alt' n m (inr x) (inl x₁) = ∪-alt-odd-even n m x x₁
∪-alt' n m (inr x) (inr x₁) = ∪-alt-odd-odd n m x x₁

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
∪-alt-id (suc n) a = refl -}

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

∪ₗ'-1-cool : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
∪ₗ'-1-cool m base y = north
∪ₗ'-1-cool zero (loop i) base = north
∪ₗ'-1-cool zero (loop i) (loop i₁) =
  (sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base)) i i₁
∪ₗ'-1-cool (suc m) (loop i) north = north
∪ₗ'-1-cool (suc m) (loop i) south = north
∪ₗ'-1-cool (suc m) (loop i) (merid a j) = 
  (sym (rCancel (merid north)) ∙∙ (λ i → merid ((∪ₗ'-1-cool m (loop i) a)) ∙ sym (merid north)) ∙∙ rCancel (merid north)) i j

∪ₗ'-cool : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (suc (n + m)))
∪ₗ'-cool-0 : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n m x (ptSn _) ≡ north
∪ₗ'-cool-south : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n (suc m) x south ≡ north
∪ₗ'-cool zero m x y = ∪ₗ'-1-cool m x y
∪ₗ'-cool (suc n) zero north y = north
∪ₗ'-cool (suc n) zero south y = north
∪ₗ'-cool (suc n) zero (merid a i) base = north
∪ₗ'-cool (suc n) zero (merid a i) (loop i₁) =
  ∪ₗ'-1-cool (suc (n + zero))
       (loop i) ((sym (∪ₗ'-cool-0 n zero a)
    ∙∙ (λ i₁ → ∪ₗ'-cool n _ a (loop i₁))
    ∙∙ ∪ₗ'-cool-0 n zero a) i₁)
∪ₗ'-cool (suc n) (suc m) north y = north
∪ₗ'-cool (suc n) (suc m) south y = north
∪ₗ'-cool (suc n) (suc m) (merid a i) north = north
∪ₗ'-cool (suc n) (suc m) (merid a i) south = north
∪ₗ'-cool (suc n) (suc m) (merid a i) (merid b j) =
  ∪ₗ'-1-cool (suc (n + suc m)) (loop i)
    ((sym (∪ₗ'-cool-0 n (suc m) a) ∙∙ (λ i → ∪ₗ'-cool n _ a (merid b i)) ∙∙ ∪ₗ'-cool-south n m a) j)
∪ₗ'-cool-0 zero zero base = refl
∪ₗ'-cool-0 zero zero (loop i) = refl
∪ₗ'-cool-0 (suc n) zero north = refl
∪ₗ'-cool-0 (suc n) zero south = refl
∪ₗ'-cool-0 (suc n) zero (merid a i) = refl
∪ₗ'-cool-0 zero (suc m) base = refl
∪ₗ'-cool-0 zero (suc m) (loop i) = refl
∪ₗ'-cool-0 (suc n) (suc m) north = refl
∪ₗ'-cool-0 (suc n) (suc m) south = refl
∪ₗ'-cool-0 (suc n) (suc m) (merid a i) = refl
∪ₗ'-cool-south zero m base = refl
∪ₗ'-cool-south zero m (loop i) = refl
∪ₗ'-cool-south (suc n) m north = refl
∪ₗ'-cool-south (suc n) m south = refl
∪ₗ'-cool-south (suc n) m (merid a i) = refl

cup∙ : (n m : ℕ) → coHomK (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
cup∙ n m = trRec (isOfHLevel↑∙ (suc n) m)
                 (sndP n m)
     where

     t₁ : (m : ℕ) → S¹ → coHomK (suc m) → coHomK (suc (suc m))
     F : (m : ℕ) → coHomK (suc m) → 0ₖ (2 + m) ≡ 0ₖ (2 + m)
     t₁ m base y = 0ₖ _
     t₁ m (loop i) y = F m y i
     t : (n : ℕ) (m : ℕ) → S₊ (suc n) → coHomK (suc m) → coHomK (suc (suc (n + m)))
     t zero = t₁ 
     t (suc n) m north y = 0ₖ _
     t (suc n) m south y = 0ₖ _
     t (suc n) m (merid a i) y =
       t₁ _ (loop i) (t n m a y)

     F zero = trRec (isOfHLevelTrunc 4 _ _)
                 λ {base → refl
                 ; (loop j) i → cong (cong ∣_∣) (sym (rCancel (merid base))
                             ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
                             ∙∙ rCancel (merid base))  i j}
     F (suc m) = trRec (isOfHLevelTrunc (5 + m) _ _)
                 λ {north → refl
                 ; south → refl
                 ; (merid a j) i → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → t₁ m (loop i) ∣ a ∣) ∙∙ Kn→ΩKn+10ₖ _) i j}

     sndP : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (suc (n + m)))
     fst (sndP n m x) = t n m x
     snd (sndP zero m base) = refl
     snd (sndP zero zero (loop i)) = refl
     snd (sndP zero (suc m) (loop i)) = refl
     snd (sndP (suc n) m north) = refl
     snd (sndP (suc n) m south) = refl
     snd (sndP (suc n) m (merid a i)) k = t₁ _ (loop i) (snd (sndP n m a) k)

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
{-
  cong (miner (suc n) (suc m) even-or-odd even-or-odd ∘
    (subst coHomK (cong (2 +_) (+-comm m n))))
      {!snd (cup∙ m n )!} -}

anti-comm-main : (n : ℕ) (m : ℕ) → (a : S₊ (suc n)) (b : S₊ (suc m))
        → ⌣ n m ∣ a ∣ ∣ b ∣ ≡  miner (suc n) (suc m) even-or-odd even-or-odd
                                   (subst coHomK (cong (2 +_) (+-comm m n))
                                     (⌣ m n ∣ b ∣ ∣ a ∣))
anti-comm-main zero zero base base = refl
anti-comm-main zero zero base (loop i) = refl
anti-comm-main zero zero (loop i) base = refl
anti-comm-main zero zero (loop i) (loop j) k =
  help2 k i j
  where
  help2 : (λ i j → ⌣ zero zero ∣ loop i ∣ ∣ loop j ∣)
          ≡ flipSquare (cong (cong (trMap (miner-h 1 1 (inr tt) (inr tt)) ∘ subst coHomK (cong (_+_ 2) (λ _ → 0)))) λ i j → ⌣ zero zero ∣ loop i ∣ ∣ loop j ∣)
  help2 =
       inst2 _ (λ i j → ⌣ zero zero ∣ loop i ∣ ∣ loop j ∣)
    ∙∙ rUnit _
    ∙∙ (λ k → transportRefl refl (~ k)
          ∙∙ (λ i j → ⌣ zero zero ∣ loop (~ i) ∣ ∣ loop (~ j) ∣)
          ∙∙ transportRefl refl (~ k))
   ∙∙ (λ k → (λ i → congMinner' 1 1 tt tt refl (~ k ∧ i))
           ∙∙ (λ i → congMinner' 1 1 tt tt (λ j → ⌣ zero zero ∣ loop (~ i) ∣ ∣ loop j ∣) (~ k))
           ∙∙ λ i → congMinner' 1 1 tt tt refl (~ k ∧ ~ i))
   ∙∙ sym (rUnit _)
   ∙∙ (λ k i j
     → trMap (miner-h 1 1 (inr tt) (inr tt))
              (transportRefl (⌣ zero zero ∣ loop (~ i) ∣ ∣ loop j ∣) (~ k)))
   ∙∙ inst _ _
anti-comm-main zero (suc m) base north = refl
anti-comm-main zero (suc m) base south = refl
anti-comm-main zero (suc m) base (merid a i) k =
  trMap (miner-h 1 (suc (suc m)) (inr tt) even-or-odd)
         (subst coHomK (cong (_+_ 2) (λ i₁ → suc (+-zero m i₁)))
           (⌣ zero _ ∣ loop i ∣ (rUnit-⌣ m zero ∣ a ∣ (~ k))))
anti-comm-main zero (suc m) (loop i) north = refl
anti-comm-main zero (suc m) (loop i) south = refl
anti-comm-main zero (suc m) (loop i) (merid a j) k = helper m even-or-odd a k i j
  where
  helper : (m : ℕ) (p : _) (a : _)
    → Square (flipSquare (cong (funExt⁻ (cong (λ x → ⌣ zero (suc m) ∣ x ∣) loop)) (cong ∣_∣ (merid a))))
                      (cong (cong (miner 1 (suc (suc m)) (inr tt) p ∘
                                         (subst coHomK (cong (_+_ 2) (+-comm (suc m) zero)))))
                                         λ i j → ⌣ (suc m) zero ∣ merid a j ∣ ∣ loop i ∣)
                   (λ k i → trMap (miner-h 1 (suc (suc m)) (inr tt) p)
         (subst coHomK (cong (_+_ 2) (λ i₁ → suc (+-zero m i₁)))
           (⌣ zero _ ∣ loop i ∣ (rUnit-⌣ m zero ∣ a ∣ (~ k)))))
                   λ k i → trMap (miner-h 1 (suc (suc m)) (inr tt) p)
         (subst coHomK (cong (_+_ 2) (λ i₁ → suc (+-zero m i₁)))
           (⌣ zero _ ∣ loop i ∣ (rUnit-⌣ m zero ∣ a ∣ (~ k))))
  helper zero (inl x) base = _
  helper zero (inl x) (loop z) =
       sym (inst _ _)
    ∙∙ {- (λ k i j → ⌣ zero 1 ∣ loop j ∣ ∣ merid l (~ i) ∣) -- ⌣ zero 1 {!∣ loop i ∣!} ∣ merid l (~ j) ∣)
    ∙∙ (λ k i j → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → anti-comm-main zero zero (loop i) l k) ∙∙ Kn→ΩKn+10ₖ _) j (~ i))
    ∙∙ (λ k i j → (sym (Kn→ΩKn+10ₖ _)
                ∙∙ cong (Kn→ΩKn+1 _) (congMinner' 1 1 tt tt (cong (λ x → transportRefl x k) (λ i → ⌣ zero zero ∣ l ∣ ∣ loop i ∣)) k)
                ∙∙ Kn→ΩKn+10ₖ _) j (~ i))
    ∙∙ (λ k i j → sym-∙∙ (sym (Kn→ΩKn+10ₖ _))
                          (cong (Kn→ΩKn+1 _) (λ i → ⌣ zero zero ∣ l ∣ ∣ loop i ∣))
                          (Kn→ΩKn+10ₖ _) (~ k) j (~ i))
    ∙∙ (λ k i j → (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (λ i → ⌣ zero zero ∣ l ∣ ∣ loop i ∣) ∙∙ Kn→ΩKn+10ₖ _) (~ j) (~ i)) -}
      ({!(λ k i j → ⌣ zero 1 ∣ loop j ∣ ∣ merid l (~ i) ∣)!} ∙∙
        (λ k → {!!})
        ∙∙ sym (rUnit _))
    ∙∙ (λ k i j → ⌣ zero 1 ∣ loop j ∣ (⌣ zero zero ∣ loop (~ i) ∣ ∣ l ∣))
    ∙∙ (λ k i j → ⌣ zero 1 ∣ loop j ∣ (congMinner' 1 1 tt tt (cong (λ x → transportRefl x (~ k)) (λ i → ⌣ zero zero ∣ loop i ∣ ∣ l ∣)) (~ k) i))
    ∙∙ (λ k i j → ⌣ zero 1 ∣ loop j ∣ (anti-comm-main zero zero l (loop i) (~ k)))
    ∙∙ (λ k → cong (cong (λ x → transportRefl x (~ k)))
              λ i₁ j₁ → ⌣ 1 zero ∣ merid l j₁ ∣ ∣ loop i₁ ∣)
    ∙∙ λ k → cong (cong (trMap-miner-Right 1 2 (inr tt) x (~ k)))
         (cong (cong (subst coHomK (cong (_+_ 2) (λ i₁ → 1))))
               (λ i₁ j₁ → ⌣ 1 zero ∣ merid l j₁ ∣ ∣ loop i₁ ∣))
    where
    l = loop z
    help3 : cong (λ x → ⌣ zero zero ∣ x ∣ ∣ l ∣) (sym loop) ≡ cong ∣_∣ (merid base) ∙ (λ i → ∣ merid l (~ i) ∣)
    help3 i j = {!cong (cong ∣_∣) (sym (rCancel (merid base))
                             ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
                             ∙∙ rCancel (merid base))  i j!}
  helper (suc m) (inl x) a = {!!}
  helper m (inr x) a = {!!}
  {-
    compPathR→PathP∙∙
        ((λ k → (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 _) (rUnit (λ i → ⌣ zero m ∣ loop i ∣ ∣ a ∣) k)
              ∙∙ Kn→ΩKn+10ₖ _))
      ∙∙ (λ k → (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 _)
                      ((λ i → anti-comm-main zero m base a (i ∧ k))
                   ∙∙ (λ i → anti-comm-main zero m (loop i) a k)
                   ∙∙ (λ i → anti-comm-main zero m base a (~ i ∧ k)))
              ∙∙ Kn→ΩKn+10ₖ _))
      ∙∙ (λ k → (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 _)
                      (anti-comm-main zero m base a
                   ∙∙ (λ i → G (⌣ m zero ∣ a ∣ ∣ loop i ∣))
                   ∙∙ sym (anti-comm-main zero m base a))
              ∙∙ Kn→ΩKn+10ₖ _))
      ∙∙ testP m a x
      ∙∙ {!!}
      ∙∙ {!!}
      ∙∙ {!!}
      ∙∙ cong-∙∙ (cong (subst coHomK (cong (_+_ 2) (λ i₃ → suc (+-zero m i₃)))))
                 (λ i j → ⌣ zero (suc (m + zero)) ∣ loop j ∣
                   (rUnit-⌣ m zero ∣ a ∣ (~ i)))
                    (λ i j → ⌣ zero _ ∣ loop j ∣ (⌣ m zero ∣ a ∣ ∣ loop i ∣))
                  ((λ i j → ⌣ zero (suc (m + zero)) ∣ loop j ∣
                   (rUnit-⌣ m zero ∣ a ∣ i)))
      ∙∙ λ k → (λ i₁ i₂ →
           trMap-miner-Right 1 (suc (suc m)) (inr tt) x (~ k)
           (subst coHomK (cong (_+_ 2) (λ i₃ → suc (+-zero m i₃)))
            (⌣ zero (suc (m + zero)) ∣ loop i₂ ∣
             (rUnit-⌣ m zero ∣ a ∣ (~ i₁)))))
        ∙∙
        cong
        (cong
         (trMap-miner-Right 1 (suc (suc m)) (inr tt) x (~ k) ∘
          subst coHomK (cong (_+_ 2) (λ i₁ → suc (+-zero m i₁)))))
        (λ i₁ j₁ → ⌣ (suc m) zero ∣ merid a j₁ ∣ ∣ loop i₁ ∣)
        ∙∙
        sym
        (λ i₁ i₂ →
           trMap-miner-Right 1 (suc (suc m)) (inr tt) x (~ k)
           (subst coHomK (cong (_+_ 2) (λ i₃ → suc (+-zero m i₃)))
            (⌣ zero (suc (m + zero)) ∣ loop i₂ ∣
             (rUnit-⌣ m zero ∣ a ∣ (~ i₁))))))
    where
    G = trMap (miner-h 1 (suc m) (inr tt) even-or-odd) ∘
      (subst coHomK (cong (_+_ 2) (+-zero m)))
    minF = trMap (miner-h 1 (suc (suc m)) (inr tt) (inl x))
    subF = subst coHomK (cong (_+_ 2) (λ i₁ → suc (+-zero m i₁)))
    help2 : {!!}
    help2 = {!!}

    testP : (m : ℕ) (a : _) → (is-even (suc (suc m))) → (sym (Kn→ΩKn+10ₖ _)
              ∙∙ cong (Kn→ΩKn+1 _)
                      (anti-comm-main zero m base a
                   ∙∙ (λ i → (trMap (miner-h 1 (suc m) (inr tt) even-or-odd) ∘
                                   (subst coHomK (cong (_+_ 2) (+-zero m)))) (⌣ m zero ∣ a ∣ ∣ loop i ∣))
                   ∙∙ sym (anti-comm-main zero m base a))
              ∙∙ Kn→ΩKn+10ₖ _)
             ≡ cong (cong (subst coHomK (cong (2 +_) (+-comm (suc m) zero))))
                    (sym (Kn→ΩKn+10ₖ _)
                  ∙∙ cong (Kn→ΩKn+1 _)
                        (sym (rUnit-⌣ m zero ∣ a ∣)
                     ∙∙ (λ i → (⌣ m zero ∣ a ∣ ∣ loop i ∣))
                     ∙∙ (rUnit-⌣ m zero ∣ a ∣))
                  ∙∙ Kn→ΩKn+10ₖ _)
    testP zero a p = {!p!}
    testP (suc m) a p = {!!}

  helper m (inr x) a = {!!} -}
anti-comm-main (suc n) zero a b = {!!}
  where
  help2 : {!!}
  help2 = {!!}
anti-comm-main (suc n) (suc m) a b = {!!}

anti-comm : (n m : ℕ) → cup∙ n m ≡ anti-commer∙ n m
anti-comm n m = funExt (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevel↑∙ (suc n) m) _ _)
                       {!!})
  where
  firstInd : (n : ℕ) → (a : S₊ (suc n)) → cup∙ n m ∣ a ∣ ≡ anti-commer∙ n m ∣ a ∣
  firstInd = {!!}

  ptFst : (n m : ℕ) (y : _) → fst (cup∙ n m ∣ snd (S₊∙ (suc n)) ∣) y ≡ 0ₖ _
  ptFst zero m y = refl
  ptFst (suc n) m y = refl

  -- ptSnd : (n m : ℕ) (y : _) → fst (anti-commer∙ n m ∣ snd (S₊∙ (suc n)) ∣) y ≡ 0ₖ _
  -- ptSnd n m y = {!!}

  sndInd : (n : ℕ) (m : ℕ)
        → (y : coHomK (suc m)) → Path (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (n + m))))
           ((λ a → fst (cup∙ n m ∣ a ∣) y)
          , ptFst n m y)
           ((λ a → fst (anti-commer∙ n m ∣ a ∣) y)
          , cong (miner (suc n) (suc m) even-or-odd even-or-odd ∘
                 (subst coHomK (cong (2 +_) (+-comm m n))))
                 (rUnit-⌣ m n y))
  sndInd n m =
    trElim (λ _ → isOfHLevelPath (3 + m)
              (subst (isOfHLevel (3 + m))
                (λ i → (S₊∙ (suc n) →∙ coHomK-ptd (suc (suc (+-comm m n i)))))
                  (isOfHLevel↑∙' (suc m) n)) _ _)
           λ b → funExt∙ ((λ a → main n m a b)
               , {!!})
    where
    main : (n : ℕ) (m : ℕ) → (a : S₊ (suc n)) (b : S₊ (suc m))
        → ⌣ n m ∣ a ∣ ∣ b ∣ ≡ (anti-commer n m ∣ a ∣ ∣ b ∣)
    main n m = {!!}

    p : (n m : ℕ) → (b : _) → main n m (ptSn (suc n)) b ≡
      ptFst n m ∣ b ∣ ∙
      cong
      (trMap (miner-h (suc n) (suc m) even-or-odd even-or-odd) ∘
       subst coHomK (cong (_+_ 2) (+-comm m n)))
      (rUnit-⌣ m n ∣ b ∣)
      ⁻¹
    p = {!!}

  help2 : (n : ℕ) (y : S¹) →
      anti-commer n zero ∣ snd (S₊∙ (suc n)) ∣ ∣ y ∣ ≡
      0ₖ (suc (suc (n + zero)))
  help2 n base = refl
  help2 zero (loop i) = refl
  help2 (suc n) (loop i) = refl

-- σ : ∀ {ℓ} {A : Type ℓ} (a : A) → (x : A) → (Path (Susp A) north north)
-- σ a x = merid x ∙ sym (merid a)

-- ∪ₗ-1 : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
-- ∪ₗ-1 m base y = north
-- ∪ₗ-1 m (loop i) y = σ (ptSn (suc m)) y i

-- ∪ᵣ-1 : (n : ℕ) → S₊ (suc n) → S¹ → S₊ (suc (n + 1))
-- ∪ᵣ-1 zero x base = north
-- ∪ᵣ-1 zero x (loop i) = σ (ptSn _) x (~ i)
-- ∪ᵣ-1 (suc n) x base = north
-- ∪ᵣ-1 (suc n) x (loop i) = subst S₊ (cong (2 +_) (+-comm 1 n)) (σ (ptSn _) x (~ i))

-- ∪ₗ : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (n + suc m))
-- ∪ₗ zero = ∪ₗ-1
-- ∪ₗ (suc n) m north y = north
-- ∪ₗ (suc n) m south y = north
-- ∪ₗ (suc n) m (merid a i) y = ∪ₗ-1 (n + suc m) (loop i) (∪ₗ n m a y)

-- ∪ᵣ : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (n + suc m))
-- ∪ᵣ n zero = ∪ᵣ-1 n
-- ∪ᵣ zero (suc m) x north = north
-- ∪ᵣ zero (suc m) x south = north
-- ∪ᵣ zero (suc m) x (merid a i) = (∪ₗ-1 _ (loop (~ i)) (∪ᵣ _ _ x a))
-- ∪ᵣ (suc n) (suc m) x north = north
-- ∪ᵣ (suc n) (suc m) x south = north
-- ∪ᵣ (suc n) (suc m) x (merid a i) =
--   subst S₊ (cong (2 +_) (sym (+-suc n (suc m))))
--            (∪ₗ-1 _ (loop (~ i)) (∪ᵣ _ _ x a))

-- lisr : (n m : ℕ) → (x : S₊ (suc n)) →  (y : S₊ (suc m)) → ∪ₗ n m x y ≡ ∪ᵣ n m x y
-- lisr zero zero base base = refl
-- lisr zero zero base (loop i) k = rCancel (merid base) (~ k) (~ i)
-- lisr zero zero (loop i) base k = rCancel (merid base) k i
-- lisr zero zero (loop i) (loop j) k =
--   comp (λ _ → S₊ 2)
--        (λ z → λ { (i = i0) → rCancel (merid base) (~ k) (~ j)
--                  ; (i = i1) → rCancel (merid base) (~ k) (~ j)
--                  ; (j = i0) → rCancel (merid base) (k ∨ ~ z) i
--                  ; (j = i1) → rCancel (merid base) (k ∨ ~ z) i
--                  ; (k = i0) → doubleCompPath-filler (sym (rCancel (merid base))) (λ j i → σ base (loop j) i) (rCancel (merid base)) (~ z) j i
--                  ; (k = i1) → σ base (loop i) (~ j)})
--        (comp (λ _ → S₊ 2)
--        (λ z → λ { (i = i0) → rCancel (merid base) (~ k) (~ j)
--                  ; (i = i1) → rCancel (merid base) (~ k) (~ j)
--                  ; (j = i0) → north
--                  ; (j = i1) → north
--                  ; (k = i0) → (sym (inst4 (sym (rCancel (merid base)) ∙∙ (λ i j → σ base (loop i) j) ∙∙ rCancel (merid base)))
--                               ∙ inst _ (sym (rCancel (merid base)) ∙∙ (λ j i → σ base (loop j) i) ∙∙ rCancel (merid base))) z i j
--                  ; (k = i1) → σ base (loop i) (~ j)})
--         (comp (λ _ → S₊ 2)
--        (λ z → λ { (i = i0) → rCancel (merid base) (~ k ∧ z) (~ j)
--                  ; (i = i1) → rCancel (merid base) (~ k ∧ z) (~ j)
--                  ; (j = i0) → north 
--                  ; (j = i1) → north
--                  ; (k = i0) → doubleCompPath-filler (sym (rCancel (merid base))) (λ j i → σ base (loop j) i) (rCancel (merid base)) z i (~ j) 
--                  ; (k = i1) → σ base (loop i) (~ j)})
--               (σ base (loop i) (~ j))))
-- lisr zero (suc m) x y = {!!}
-- lisr (suc n) zero x y = {!!}
-- lisr (suc n) (suc m) north north = refl
-- lisr (suc n) (suc m) north south = refl
-- lisr (suc n) (suc m) north (merid a i) k =
--   subst S₊ (λ i₁ → suc (suc (+-suc n (suc m) (~ i₁))))
--         (hcomp (λ z → λ {(i = i0) → north
--                         ; (i = i1) → north
--                         ; (k = i0) → rCancel (merid north) z (~ i)
--                         ; (k = i1) → (σ north (∪ᵣ (suc n) m north a)) (~ i)})
--                (σ north ((lisr (suc n) m north a) k) (~ i)))
-- lisr (suc n) (suc m) south north = refl
-- lisr (suc n) (suc m) south south = refl
-- lisr (suc n) (suc m) south (merid a i) k =
--   subst S₊ (λ i₁ → suc (suc (+-suc n (suc m) (~ i₁))))
--         (hcomp (λ z → λ {(i = i0) → north
--                         ; (i = i1) → north
--                         ; (k = i0) → rCancel (merid north) z (~ i)
--                         ; (k = i1) → (σ north (∪ᵣ (suc n) m south a)) (~ i)})
--                (σ north ((lisr (suc n) m south a) k) (~ i)))
-- lisr (suc n) (suc m) (merid a i) north k = {!!}
-- lisr (suc n) (suc m) (merid a i) south = {!!}
-- lisr (suc n) (suc m) (merid a i) (merid b j) = {!!}

-- -S : {k : ℕ} → (n m : ℕ) → (is-even n ⊎ is-odd n) → (is-even m ⊎ is-odd m) → S₊ (suc k) → S₊ (suc k)
-- -S {k = zero} n m p q base = base
-- -S {k = zero} n m (inl x) q (loop i) = loop i
-- -S {k = zero} n m (inr x) (inl x₁) (loop i) = loop i
-- -S {k = zero} n m (inr x) (inr x₁) (loop i) = loop (~ i)
-- -S {k = suc k₁} n m p q north = north
-- -S {k = suc k₁} n m p q south = north
-- -S {k = suc k₁} n m (inl x) q (merid a i) = σ (ptSn (suc k₁)) a i
-- -S {k = suc k₁} n m (inr x) (inl x₁) (merid a i) = σ (ptSn (suc k₁)) a i
-- -S {k = suc k₁} n m (inr x) (inr x₁) (merid a i) = σ (ptSn (suc k₁)) a (~ i)
-- open import Cubical.Data.Nat.Order
-- leq-dec : (n m : ℕ) → (n ≤ m) ⊎ (m < n)
-- leq-dec = {!!}

-- anti-c'-helper : (n m : ℕ)
--        → ((n m : ℕ) → (n ≤ m) → (x : S₊ (suc n))
--        →  (y : S₊ (suc m))
--        →  (∪ₗ n m x y) ≡
--               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (∪ₗ m n y x))))
--        → (x : S₊ (suc n))
--        →  (y : S₊ (suc m))
--        →  (∪ₗ n m x y) ≡
--               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (∪ₗ m n y x)))
-- anti-c'-helper n m hyp x y with (leq-dec n m)
-- ... | inl p = hyp n m p x y
-- ... | inr p =
--      {!!}
--   ∙∙ {!!}
--   ∙∙ {!!}
--   ∙∙ {!!}
--   ∙∙ cong (-S (suc n) (suc m) even-or-odd even-or-odd ∘ (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m)))))
--           (sym (hyp m n (suc (fst p) , sym (+-suc (fst p) m) ∙ snd p) y x) )
--   where
--   help2 : {!!}
--   help2 = {!!}

-- coolAdd : ℕ → ℕ → ℕ
-- coolAdd zero y = y
-- coolAdd (suc x) zero = suc x
-- coolAdd (suc x) (suc y) = suc (suc (x + y))

-- ∪ₗ'-1 : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
-- ∪ₗ'-1 m base y = north
-- ∪ₗ'-1 m (loop i) y = σ (ptSn (suc m)) y i

-- ∪ₗ' : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (suc (n + m)))
-- ∪ₗ' zero = ∪ₗ'-1 -- ∪ₗ-1
-- ∪ₗ' (suc n) m north y = north
-- ∪ₗ' (suc n) m south y = north
-- ∪ₗ' (suc n) m (merid a i) y =
--  (∪ₗ'-1 (suc ((n + m))) (loop i) (∪ₗ' n m a y))

-- ∪ₗ'-1-cool : (m : ℕ) → S¹ → S₊ (suc m) → S₊ (suc (suc m))
-- ∪ₗ'-1-cool m base y = north
-- ∪ₗ'-1-cool zero (loop i) base = north
-- ∪ₗ'-1-cool zero (loop i) (loop i₁) =
--   (sym (rCancel (merid base)) ∙∙ (λ i → merid (loop i) ∙ sym (merid base)) ∙∙ rCancel (merid base)) i i₁
-- ∪ₗ'-1-cool (suc m) (loop i) north = north
-- ∪ₗ'-1-cool (suc m) (loop i) south = north
-- ∪ₗ'-1-cool (suc m) (loop i) (merid a j) = 
--   (sym (rCancel (merid north)) ∙∙ (λ i → merid ((∪ₗ'-1-cool m (loop i) a)) ∙ sym (merid north)) ∙∙ rCancel (merid north)) i j

-- ∪ₗ'-cool : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → S₊ (suc (suc (n + m)))
-- ∪ₗ'-cool-0 : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n m x (ptSn _) ≡ north
-- ∪ₗ'-cool-south : (n m : ℕ) → (x : S₊ (suc n)) → ∪ₗ'-cool n (suc m) x south ≡ north
-- ∪ₗ'-cool zero m x y = ∪ₗ'-1-cool m x y
-- ∪ₗ'-cool (suc n) zero north y = north
-- ∪ₗ'-cool (suc n) zero south y = north
-- ∪ₗ'-cool (suc n) zero (merid a i) base = north
-- ∪ₗ'-cool (suc n) zero (merid a i) (loop i₁) =
--   ∪ₗ'-1-cool (suc (n + zero))
--        (loop i) ((sym (∪ₗ'-cool-0 n zero a)
--     ∙∙ (λ i₁ → ∪ₗ'-cool n _ a (loop i₁))
--     ∙∙ ∪ₗ'-cool-0 n zero a) i₁)
-- ∪ₗ'-cool (suc n) (suc m) north y = north
-- ∪ₗ'-cool (suc n) (suc m) south y = north
-- ∪ₗ'-cool (suc n) (suc m) (merid a i) north = north
-- ∪ₗ'-cool (suc n) (suc m) (merid a i) south = north
-- ∪ₗ'-cool (suc n) (suc m) (merid a i) (merid b j) =
--   ∪ₗ'-1-cool (suc (n + suc m)) (loop i)
--     ((sym (∪ₗ'-cool-0 n (suc m) a) ∙∙ (λ i → ∪ₗ'-cool n _ a (merid b i)) ∙∙ ∪ₗ'-cool-south n m a) j)
-- ∪ₗ'-cool-0 zero zero base = refl
-- ∪ₗ'-cool-0 zero zero (loop i) = refl
-- ∪ₗ'-cool-0 (suc n) zero north = refl
-- ∪ₗ'-cool-0 (suc n) zero south = refl
-- ∪ₗ'-cool-0 (suc n) zero (merid a i) = refl
-- ∪ₗ'-cool-0 zero (suc m) base = refl
-- ∪ₗ'-cool-0 zero (suc m) (loop i) = refl
-- ∪ₗ'-cool-0 (suc n) (suc m) north = refl
-- ∪ₗ'-cool-0 (suc n) (suc m) south = refl
-- ∪ₗ'-cool-0 (suc n) (suc m) (merid a i) = refl
-- ∪ₗ'-cool-south zero m base = refl
-- ∪ₗ'-cool-south zero m (loop i) = refl
-- ∪ₗ'-cool-south (suc n) m north = refl
-- ∪ₗ'-cool-south (suc n) m south = refl
-- ∪ₗ'-cool-south (suc n) m (merid a i) = refl

-- anti-c'-cong :  (n m : ℕ)
--        → (a : S₊ (suc n))
--        →  (y : S₊ (suc (suc m)))
--        →  cong (λ x → ∪ₗ'-cool (suc n) (suc m) x y) (merid a) ≡ λ i → ∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool n (suc m) a y)
-- anti-c'-cong n m a north k j = ∪ₗ'-1-cool (suc (n + suc m)) (loop j)
--          (∪ₗ'-cool-0 n (suc m) a (~ k))
-- anti-c'-cong n m a south k j = ∪ₗ'-1-cool (suc (n + suc m)) (loop j)
--          (∪ₗ'-cool-south n m a (~ k))
-- anti-c'-cong n m a (merid a₁ i) k j = {!!}

-- -S-idemp : {k : ℕ} (n m : ℕ)
--          → (p : is-even n ⊎ is-odd n)
--          → (q : is-even m ⊎ is-odd m)
--          → (x : S₊ (suc k))
--          → -S n m p q (-S n m p q x)
--           ≡ x
-- -S-idemp {k = zero} n m (inl x₁) q base = refl
-- -S-idemp {k = zero} n m (inl x₁) q (loop i) = refl
-- -S-idemp {k = suc k₁} n m (inl x₁) q north = refl
-- -S-idemp {k = suc k₁} n m (inl x₁) q south = merid (ptSn _)
-- -S-idemp {k = suc k₁} n m (inl x₁) q (merid a i) k = help3 k i
--   where
--   help2 : cong (-S n m (inl x₁) q) (cong (-S n m (inl x₁) q) (merid a)) ≡ σ (ptSn (suc k₁)) a
--   help2 = congFunct (-S n m (inl x₁) q) (merid a) (sym (merid (ptSn _)))
--        ∙∙ cong (σ (ptSn _) a ∙_) (cong sym (rCancel (merid (ptSn _))))
--        ∙∙ sym (rUnit _)

--   help3 : PathP (λ i → north ≡ merid (ptSn _) i) (cong (-S n m (inl x₁) q) (cong (-S n m (inl x₁) q) (merid a))) (merid a)
--   help3 = toPathP (cong (transp (λ i₁ → north ≡ merid (ptSn (suc k₁)) i₁) i0) help2
--         ∙ fromPathP λ i j → compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j)
-- -S-idemp {k = zero} n m (inr x₁) (inl x₂) base = refl
-- -S-idemp {k = zero} n m (inr x₁) (inl x₂) (loop i) = refl
-- -S-idemp {k = suc k₁} n m (inr x₁) (inl x₂) north = refl
-- -S-idemp {k = suc k₁} n m (inr x₁) (inl x₂) south = merid (ptSn _)
-- -S-idemp {k = suc k₁} n m (inr x₁) (inl x₂) (merid a i) = λ k → help3 k i
--     where
--   help2 : cong (-S n m (inr x₁) (inl x₂)) (cong (-S n m (inr x₁) (inl x₂)) (merid a))
--         ≡ σ (ptSn (suc k₁)) a
--   help2 = congFunct (-S n m (inr x₁) (inl x₂)) (merid a) (sym (merid (ptSn _)))
--        ∙∙ cong (σ (ptSn _) a ∙_) (cong sym (rCancel (merid (ptSn _))))
--        ∙∙ sym (rUnit _)

--   help3 : PathP (λ i → north ≡ merid (ptSn _) i) (cong (-S n m (inr x₁) (inl x₂)) (cong (-S n m (inr x₁) (inl x₂)) (merid a))) (merid a)
--   help3 = toPathP (cong (transp (λ i₁ → north ≡ merid (ptSn (suc k₁)) i₁) i0) help2
--         ∙ fromPathP λ i j → compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j)
-- -S-idemp {k = zero} n m (inr x₁) (inr x₂) base = refl
-- -S-idemp {k = zero} n m (inr x₁) (inr x₂) (loop i) = refl
-- -S-idemp {k = suc k₁} n m (inr x₁) (inr x₂) north = refl
-- -S-idemp {k = suc k₁} n m (inr x₁) (inr x₂) south = merid (ptSn _)
-- -S-idemp {k = suc k₁} n m (inr x₁) (inr x₂) (merid a i) =
--   λ k → help3 k i
--     where
--   help2 : cong (-S n m (inr x₁) (inr x₂)) (cong (-S n m (inr x₁) (inr x₂)) (merid a))
--         ≡ σ (ptSn (suc k₁)) a
--   help2 = cong sym (congFunct (-S n m (inr x₁) (inr x₂)) (merid a) (sym (merid (ptSn _))))
--        ∙∙ cong sym (cong (sym (σ (ptSn _) a) ∙_) ((rCancel (merid (ptSn _)))))
--        ∙∙ cong sym (sym (rUnit (sym (σ (ptSn _) a))))

--   help3 : PathP (λ i → north ≡ merid (ptSn _) i) (cong (-S n m (inr x₁) (inr x₂)) (cong (-S n m (inr x₁) (inr x₂)) (merid a))) (merid a)
--   help3 = toPathP (cong (transp (λ i₁ → north ≡ merid (ptSn (suc k₁)) i₁) i0) help2
--         ∙ fromPathP λ i j → compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j)

-- anti-cc : (n m : ℕ)
--        → (x : S₊ (suc n))
--        →  (y : S₊ (suc m))
--        →  -S (suc n) (suc m) even-or-odd even-or-odd
--              (subst S₊ (sym (cong (2 +_) (+-comm m n)))
--                (∪ₗ'-cool n m x y))
--          ≡ ∪ₗ'-cool m n y x
--        → (∪ₗ'-cool n m x y) ≡
--               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong (2 +_) (+-comm m n)) (∪ₗ'-cool m n y x)))
-- anti-cc n m x y p =
--      sym (-S-idemp (suc n) (suc m) even-or-odd even-or-odd (∪ₗ'-cool n m x y))
--   ∙∙ cong (-S (suc n) (suc m) even-or-odd even-or-odd)
--           (λ i → transp (λ j → S₊ (2 + (+-comm m n (~ i ∨ j)))) (~ i)
--             (-S (suc n) (suc m) even-or-odd even-or-odd
--               (transp (λ j → S₊ (2 + (+-comm m n (~ i ∨ ~ j)))) (~ i)
--                 (∪ₗ'-cool n m x y))))
--   ∙∙ cong (-S (suc n) (suc m) even-or-odd even-or-odd
--           ∘ (subst S₊ (cong (2 +_) (+-comm m n)))) p

-- goalType : (n m : ℕ) → Type
-- goalType n m = (x : S₊ (suc n)) (y : S₊ (suc m)) →
--   (∪ₗ'-cool n m x y) ≡
--                (-S (suc n) (suc m) even-or-odd even-or-odd
--                  (subst S₊ (cong (2 +_) (+-comm m n)) (∪ₗ'-cool m n y x)))

-- -Scomm : {k : ℕ} (n m : ℕ) (p1 p2 : _) (q1 q2 : _) (x : S₊ (suc k)) → -S n m p1 q1 x ≡ -S m n q2 p2 x
-- -Scomm = {!!}

-- pfForm : goalType 0 0
--         → ((m : ℕ) → goalType zero (suc m))
--         → ((n m : ℕ)
--           → goalType n (suc m)
--           → goalType (suc n) m
--           → goalType (suc n) (suc m))
--         → (n m : ℕ) → goalType n m
-- pfForm b l ind zero zero = b
-- pfForm b l ind zero (suc m) = l m
-- pfForm b l ind (suc n) zero x y =
--   anti-cc (suc n) zero x y
--       ((cong (-S (suc (suc n)) 1 even-or-odd (inr tt))
--         (cong (λ p → subst S₊ p (∪ₗ'-cool (suc n) zero x y)) (isSetℕ _ _ _ _))
--     ∙ (-Scomm (suc (suc n)) 1 even-or-odd even-or-odd (inr tt) (inr tt) ((subst S₊ (λ i → suc (suc (suc (+-zero n i))))
--        (∪ₗ'-cool (suc n) zero x y)))))
--     ∙ sym (pfForm b l ind zero (suc n) y x))
-- pfForm b l ind (suc n) (suc m) =
--   ind n m
--     (pfForm b l ind n (suc m))
--     (pfForm b l ind (suc n) m)

-- anti-c' : (n m : ℕ)
--        → (x : S₊ (suc n))
--        →  (y : S₊ (suc m))
--        →  (∪ₗ'-cool n m x y) ≡
--               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong (2 +_) (+-comm m n)) (∪ₗ'-cool m n y x)))
-- anti-c' zero m x y = {!!}
-- anti-c' (suc n) zero x y = {!!}
-- anti-c' (suc n) (suc m) north north = refl
-- anti-c' (suc n) (suc m) north south = refl
-- anti-c' (suc n) (suc m) north (merid a i) =
--   {!!}
-- anti-c' (suc n) (suc m) south north = refl
-- anti-c' (suc n) (suc m) south south = refl
-- anti-c' (suc n) (suc m) south (merid a i) = refl
-- anti-c' (suc n) (suc m) (merid a i) north = refl
-- anti-c' (suc n) (suc m) (merid a i) south = refl
-- anti-c' (suc n) (suc zero) (merid a i) (merid b j) = {!!}
-- anti-c' (suc zero) (suc (suc m)) (merid a i) (merid b j) = {!!}
-- anti-c' (suc (suc n)) (suc (suc m)) (merid a i) (merid b j) k = {!!} -- main k i j
--   where
--   symmer : ∀ {ℓ} {A : Type ℓ} {x : A} (n m : ℕ) → (is-even n ⊎ is-odd n) → (is-even m ⊎ is-odd m) → x ≡ x → x ≡ x
--   symmer n m (inl x) q P = P
--   symmer n m (inr x) (inl x₁) P = P
--   symmer n m (inr x) (inr x₁) P = sym P

--   symmer≡ : ∀ {k : ℕ} (n m : ℕ) (p : Path (S₊ (suc (suc k))) north north)
--           → symmer n m even-or-odd even-or-odd  p ≡ cong (-S n m even-or-odd even-or-odd) p
--   symmer≡ = {!!}

--   cong-symmer : ∀ {ℓ} {A B : Type ℓ} {x : A} (n m : ℕ) → (p : is-even n ⊎ is-odd n) → (q : is-even m ⊎ is-odd m) (f : A → B) (P : x ≡ x)
--              → cong f (symmer n m p q P) ≡ symmer n m p q (cong f P)
--   cong-symmer = {!!}

--   symmerId1 : ∀ {ℓ} (n m : ℕ) {A : Type ℓ} {x : A} (P : x ≡ x) → (p : is-even (suc (suc n)) ⊎ is-odd (suc (suc n)))
--            → (q : is-even (suc (suc m)) ⊎ is-odd (suc (suc m)))
--            → (z : is-even (3 + n) ⊎ is-odd (3 + n)) →
--              ((symmer (suc (suc m)) (3 + n) q z) ∘ (symmer (suc (suc n)) (suc (suc m)) p q)) P -- m(1 + n) + nm = m
--              ≡ symmer 1 m (inr tt) q P
--   symmerId1 n m P (inl x) (inl x₁) z = refl
--   symmerId1 n m P (inl x) (inr x₁) (inl x₂) = Cubical.Data.Empty.rec {!even-and-odd!}
--   symmerId1 n m P (inl x) (inr x₁) (inr x₂) = refl
--   symmerId1 n m P (inr x) (inl x₁) z = refl
--   symmerId1 n m P (inr x) (inr x₁) (inl x₂) = refl
--   symmerId1 n m P (inr x) (inr x₁) (inr x₂) = Cubical.Data.Empty.rec {!!}

--   help2 : sym (cong (∪ₗ'-cool (suc n) _ a) (merid b)) ≡
--               anti-c' (suc n) (suc (suc m)) a south
--                 ∙∙ symmer (suc (suc n)) (suc (suc (suc m))) even-or-odd even-or-odd
--                      (sym (cong (subst S₊ (cong (_+_ 2) ((λ i₂ → suc (suc (+-suc m n i₂))) ∙ λ i₂ → suc (+-comm (suc (suc m)) n i₂))))
--                        (λ i → ∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool (suc m) (suc n) b a))))
--                 ∙∙ sym (anti-c' (suc n) (suc (suc m)) a north)
--   help2 = rUnit _
--        ∙∙ (λ k → (λ i → anti-c' (suc n) (suc (suc m)) a south (k ∧ i))
--                ∙∙ (λ i → anti-c' (suc n) _ a (merid b (~ i)) k)
--                ∙∙ λ i → anti-c' (suc n) (suc (suc m)) a north (k ∧ ~ i))
--        ∙∙ (λ k → anti-c' (suc n) (suc (suc m)) a south
--                ∙∙ (λ i → -S (suc (suc n)) (suc (suc (suc m))) even-or-odd even-or-odd
--       (subst S₊
--        (cong (_+_ 2)
--         ((λ i₂ → suc (suc (+-suc m n i₂))) ∙
--          (λ i₂ → suc (+-comm (suc (suc m)) n i₂)))) (anti-c'-cong _ _ b a k (~ i))))
--                ∙∙ sym (anti-c' (suc n) (suc (suc m)) a north))
--        ∙∙ (λ k → anti-c' (suc n) (suc (suc m)) a south
--                ∙∙ (λ i → -S (suc (suc n)) (suc (suc (suc m))) even-or-odd even-or-odd
--       (subst S₊
--        (cong (_+_ 2)
--         ((λ i₂ → suc (suc (+-suc m n i₂))) ∙
--          (λ i₂ → suc (+-comm (suc (suc m)) n i₂))))
--            (∪ₗ'-1-cool _ (loop (~ i)) (∪ₗ'-cool (suc m) (suc n) b a)))) -- 1 + n(1 + m) = n + 1 + nm
--                ∙∙ sym (anti-c' (suc n) (suc (suc m)) a north))
--        ∙∙ (λ k → anti-c' (suc n) (suc (suc m)) a south
--                 ∙∙ symmer≡ (suc (suc n)) (suc (suc (suc m)))
--                      (sym (cong (subst S₊ (cong (_+_ 2) ((λ i₂ → suc (suc (+-suc m n i₂))) ∙ λ i₂ → suc (+-comm (suc (suc m)) n i₂))))
--                        (λ i → ∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool (suc m) (suc n) b a))))
--                      (~ k) 
--                 ∙∙ sym (anti-c' (suc n) (suc (suc m)) a north))

--   moveMin : {k : ℕ} (n m : ℕ) (x : S₊ (suc (suc k))) → (p : is-even n ⊎ is-odd n) → (q : is-even m ⊎ is-odd m)
--           → cong (λ z → ∪ₗ'-1-cool (suc k) z (-S n m p q x)) loop ≡ symmer n m p q (cong (λ z → ∪ₗ'-1-cool (suc k) z x) loop)
--   moveMin n m x p q = {!!}

--   sub-path = (cong suc (cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂)))))
--                                                    ∙ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))

--   help-right : cong (∪ₗ'-cool (suc m) (suc (suc n)) b) (merid a)
--              ≡ anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer 1 m (inr tt) even-or-odd
--                          (cong (subst S₊ sub-path)
--                                (λ i → ∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool (suc m) (suc n) b a)))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south)
--   help-right = rUnit _
--             ∙∙ (λ k → (λ i → anti-c' (suc m) (suc (suc n)) b north (k ∧ i))
--                     ∙∙ (λ i → anti-c' (suc m) (suc (suc n)) b (merid a i) k)
--                     ∙∙ λ i → anti-c' (suc m) (suc (suc n)) b south (k ∧ ~ i))
--             ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ (λ i → -S (suc (suc m)) (suc (suc (suc n))) even-or-odd even-or-odd
--       (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))
--        (anti-c'-cong (suc n) _ a b k i)))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--             ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ (λ i → -S (suc (suc m)) (suc (suc (suc n))) even-or-odd even-or-odd
--       (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))
--                 (∪ₗ'-1-cool (suc ((suc n) + suc m)) (loop i) (anti-c' (suc n) (suc m) a b k))))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--             ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ (λ i → -S (suc (suc m)) (suc (suc (suc n))) even-or-odd even-or-odd  -- nm + m
--                        (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))
--                        (∪ₗ'-1-cool (suc ((suc n) + suc m)) (loop i)
--                        (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd -- nm -- total m -- with rest : (n + 1)(m + 1) + m = n + 1 + nm
--                        (subst S₊
--                          (cong (_+_ 2)
--                            ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))))
--                        (∪ₗ'-cool (suc m) (suc n) b a))))))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--             ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer≡ (suc (suc m)) (3 + n)
--                        (λ i → (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))
--                        (∪ₗ'-1-cool (suc ((suc n) + suc m)) (loop i)
--                        (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd
--                        (subst S₊
--                          (cong (_+_ 2)
--                            ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))))
--                        (∪ₗ'-cool (suc m) (suc n) b a))))))
--                                (~ k)
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--             ∙∙ ((λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer (suc (suc m)) (3 + n) even-or-odd even-or-odd
--                        (cong (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m))))
--                        (moveMin (suc (suc n)) (suc (suc m)) (
--                          subst S₊
--                          (cong (_+_ 2)
--                            ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))))
--                        (∪ₗ'-cool (suc m) (suc n) b a)) even-or-odd even-or-odd k))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer (suc (suc m)) (3 + n) even-or-odd even-or-odd
--                          (cong-symmer (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m))))
--                              (λ i → ∪ₗ'-1-cool _ (loop i) (subst S₊ (cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))))
--                                        (∪ₗ'-cool (suc m) (suc n) b a))) k)
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmerId1 n m
--                          (cong (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m))))
--                            (λ i → ∪ₗ'-1-cool _ (loop i) (subst S₊ (cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))))
--                                        (∪ₗ'-cool (suc m) (suc n) b a))))
--                          even-or-odd even-or-odd even-or-odd k
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer 1 m (inr tt) even-or-odd
--                          (λ i →
--                          (subst S₊ (cong (_+_ 2) (+-comm (suc (suc n)) (suc m))))
--                            (transp (λ i → S₊ (suc (cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))) (i ∨ ~ k)))) (~ k)
--                              (∪ₗ'-1-cool _ (loop i) (transp (λ i → S₊ ((cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂))) (i ∧ ~ k)))) k
--                                                             (∪ₗ'-cool (suc m) (suc n) b a)))))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer 1 m (inr tt) even-or-odd
--                          (λ i → substComposite S₊ (cong suc (cong (_+_ 2) ((λ i₂ → suc (+-suc m n i₂)) ∙ (λ i₂ → suc (+-comm (suc m) n i₂)))))
--                                                    (cong (_+_ 2) (+-comm (suc (suc n)) (suc m)))
--                                                    (∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool (suc m) (suc n) b a)) (~ k))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ (λ k → anti-c' (suc m) (suc (suc n)) b north
--                     ∙∙ symmer 1 m (inr tt) even-or-odd
--                          (cong (subst S₊ sub-path)
--                                (λ i → ∪ₗ'-1-cool _ (loop i) (∪ₗ'-cool (suc m) (suc n) b a)))
--                     ∙∙ sym (anti-c' (suc m) (suc (suc n)) b south))
--              ∙∙ refl)
--   {- rUnit _
--             ∙∙ (λ k → (λ i → anti-c' (suc m) (suc n) b north (k ∧ i))
--                     ∙∙ (λ i → anti-c' (suc m) (suc n) b (merid a i) k)
--                     ∙∙ λ i → anti-c' (suc m) (suc n) b south (k ∧ ~ i))
--             ∙∙ (λ k → {!!}
--                     ∙∙ (λ i → -S (suc (suc m)) (suc (suc n)) even-or-odd even-or-odd
--       (subst S₊ (cong (_+_ 2) (+-comm (suc n) (suc m)))
--        (∪ₗ'-1-cool _ (loop i) {!!})))
--                     ∙∙ {!(merid a i) b!})
--             ∙∙ {!anti-c' (suc m) (suc n) b (merid a i)!}
--             ∙∙ {!!} -}

--   main : flipSquare (cong (funExt⁻ (cong (∪ₗ'-cool (suc (suc n)) (suc (suc m))) (merid a))) (merid b))
--        ≡ cong (cong (-S (suc (suc (suc n))) (suc (suc (suc m))) even-or-odd even-or-odd ∘ 
--                     (subst S₊ (cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n)))))))
--                     ((cong (funExt⁻ (cong (∪ₗ'-cool (suc (suc m)) (suc (suc n))) (merid b))) (merid a)))
--   main = sym (inst _ _)
--        ∙∙ (λ k i j → ∪ₗ'-1-cool _ (loop j)
--                          ((sym (∪ₗ'-cool-0 (suc n) (suc (suc m)) a)
--                       ∙∙ sym (help2 k)
--                       ∙∙ ∪ₗ'-cool-south (suc n) (suc m) a) (~ i)))
--        ∙∙ {!!}
--        ∙∙ {!!}
--        ∙∙ (λ k i j → {!!})
--        ∙∙ (λ k → cong (funExt (symmer≡ (3 + n) (3 + m)) k)
--                        (λ i j → ∪ₗ'-1-cool _ (loop j)
--                                   (subst S₊ (cong predℕ (cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n)))))
--                                      ((sym (∪ₗ'-cool-0 (suc m) (suc (suc n)) b)
--                     ∙∙ help-right i1
--                     ∙∙ ∪ₗ'-cool-south (suc m) (suc n) b) i))))
--        ∙∙ (λ k i j → -S (suc (suc (suc n))) (suc (suc (suc m))) even-or-odd even-or-odd
--                         (∪ₗ'-1-cool _ (loop j)
--                           (subst S₊ (cong predℕ (cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n)))))
--                                      ((sym (∪ₗ'-cool-0 (suc m) (suc (suc n)) b)
--                     ∙∙ help-right i1
--                     ∙∙ ∪ₗ'-cool-south (suc m) (suc n) b) i))))
--        ∙∙ (λ k i j → -S (suc (suc (suc n))) (suc (suc (suc m))) even-or-odd even-or-odd
--                         (transp (λ i → S₊ ((cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n)))) (~ k ∨ i))) (~ k)
--                                 (∪ₗ'-1-cool _ (loop j)
--                                   (transp (λ i → S₊ (predℕ (cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n))) (~ k ∧ i)))) k
--                                           ((sym (∪ₗ'-cool-0 (suc m) (suc (suc n)) b)
--                     ∙∙ help-right i1
--                     ∙∙ ∪ₗ'-cool-south (suc m) (suc n) b) i)))))
--        ∙∙ cong (cong (cong (-S (suc (suc (suc n))) (suc (suc (suc m))) even-or-odd even-or-odd ∘ 
--                     (subst S₊ (cong (_+_ 2) (+-comm (suc (suc m)) (suc (suc n))))))))
--                     λ k i j → ∪ₗ'-1-cool _ (loop j) ((sym (∪ₗ'-cool-0 (suc m) (suc (suc n)) b)
--                     ∙∙ help-right (~ k)
--                     ∙∙ ∪ₗ'-cool-south (suc m) (suc n) b) i)

--   helper : flipSquare (cong (funExt⁻ (cong (∪ₗ'-cool (suc (suc n)) (suc (suc m))) (merid a))) (merid b))
--          ≡ {!λ i j → ?!}
--   helper = (λ k i j → ∪ₗ'-cool (suc (suc n)) (suc (suc m)) (merid a i) (merid b j))
--         ∙∙ sym (inst _ _)
--         ∙∙ (λ k i j → ∪ₗ'-1-cool _ (loop j)
--                          ((sym (∪ₗ'-cool-0 (suc n) (suc (suc m)) a)
--                       ∙∙ (cong (∪ₗ'-cool (suc n) _ a) (merid b))
--                       ∙∙ ∪ₗ'-cool-south (suc n) (suc m) a) (~ i)))
--         ∙∙ {!cong ?!}
--         ∙∙ {!!}

--   helper2 : (cong (funExt⁻ (cong (∪ₗ'-cool (suc (suc m)) (suc (suc n))) (merid b))) (merid a))
--           ≡ {!!}
--   helper2 = (λ k i j → ∪ₗ'-1-cool _ (loop j) ((sym (∪ₗ'-cool-0 (suc m) (suc (suc n)) b)
--                     ∙∙ help-right k
--                     ∙∙ ∪ₗ'-cool-south (suc m) (suc n) b) i))
--          ∙∙ {!!}
--          ∙∙ {!!}


-- -- anti-c' : (n m : ℕ)
-- --        → (x : S₊ (suc n))
-- --        →  (y : S₊ (suc m))
-- --        →  (∪ₗ n m x y) ≡
-- --               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (∪ₗ m n y x)))
-- -- anti-c' zero m x y = {!!}
-- -- anti-c' (suc n) zero x y = {!!}
-- -- anti-c' (suc n) (suc m) north north = refl
-- -- anti-c' (suc n) (suc m) north south = refl
-- -- anti-c' (suc n) (suc m) north (merid a i) k = test k i
-- --   where
-- --   c : (m : ℕ) (a : _) → -S (suc m) (suc (suc n)) even-or-odd even-or-odd
-- --       (subst S₊
-- --        (cong suc (+-comm (suc n) (suc m) ∙ sym (+-suc m (suc n))))
-- --        (∪ₗ (suc n) m north a)) ≡ ptSn _
-- --   c zero = λ _ → refl
-- --   c (suc m) = λ _ → refl

-- --   test : cong (∪ₗ (suc n) (suc m) north) (merid a)
-- --        ≡ cong (λ x → -S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd
-- --          (subst S₊
-- --           (cong suc
-- --            (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
-- --              (∪ₗ (suc m) (suc n) x north)))
-- --              (merid a)
-- --   test =
-- --     cong (cong (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd ∘ 
-- --          (subst S₊
-- --           (cong suc
-- --            (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m)))))))
-- --          (sym (rCancel (merid (ptSn _)))
-- --        ∙∙ cong (σ (ptSn _)) (sym (c m a))
-- --        ∙∙ sym (cong ((σ (ptSn _))) (anti-c' m (suc n) a north)))
-- -- anti-c' (suc n) (suc m) south north = refl
-- -- anti-c' (suc n) (suc m) south south = refl
-- -- anti-c' (suc n) (suc m) south (merid a i) =
-- --   {!!}
-- -- anti-c' (suc n) (suc m) (merid a i) north k = {!!}
-- -- anti-c' (suc n) (suc m) (merid a i) south = {!!}
-- -- anti-c' (suc zero) (suc m) (merid a i) (merid b j) = {!!}
-- -- anti-c' (suc (suc n)) (suc m) (merid a i) (merid b j) = {!!}
-- --   where
-- --   p : Square (σ north (∪ₗ _ _ a north)) (σ north (∪ₗ _ _ a south)) refl refl
-- --   p j i = ∪ₗ (suc (suc n)) (suc m) (merid a i) (merid b j)

-- --   σ-s : σ north (∪ₗ (suc n) (suc m) a south) ≡ refl
-- --   σ-s = {!!}

-- --   σ-n : σ north (∪ₗ (suc n) (suc m) a north) ≡ refl
-- --   σ-n = {!!}

-- --   q : Square (sym (σ (ptSn _) (∪ₗ _ _ b north))) (sym (σ (ptSn _) (∪ₗ _ _ b south))) refl refl
-- --   q j i = ∪ₗ (suc m) (suc (suc n)) (merid b (~ i)) (merid a j)
  
-- --   helper2 : q ≡ {!!}
-- --   helper2 =
-- --        rUnit q
-- --     ∙∙ (λ k → (λ j → sym (σ (ptSn _) (anti-c' m (suc (suc n)) b north (j ∧ k))))
-- --             ∙∙ (λ j → sym (σ (ptSn _) (anti-c' m (suc (suc n)) b (merid a j) k)))
-- --             ∙∙ λ j → sym (σ (ptSn _) (anti-c' m (suc (suc n)) b south (~ j ∧ k))))
-- --     ∙∙ (λ k → cong (sym ∘ σ (ptSn _)) (anti-c' m (suc (suc n)) b north)
-- --             ∙∙ rUnit (λ j → sym (σ (ptSn _) (-S (suc m) (suc (suc (suc n))) even-or-odd even-or-odd
-- --                                                         (subst S₊
-- --                                                          (cong suc
-- --                                                           (((λ i₁ → suc (suc (+-suc n m i₁))) ∙
-- --                                                             (λ i₁ → suc (+-comm (suc (suc n)) m i₁)))
-- --                                                            ∙ sym (+-suc m (suc (suc n)))))
-- --                                                          (σ north (∪ₗ (suc n) m a b) j))))) k -- total flips (1 + m) (3 + n) + 1 = 3m + 1n +nm = m + n + nm
-- --                 ∙∙ sym (cong (sym ∘ σ (ptSn _)) (anti-c' m (suc (suc n)) b south)))
-- --     ∙∙ (λ k → (cong (sym ∘ σ (ptSn _)) (anti-c' m (suc (suc n)) b north))
-- --             ∙∙ {!!}
-- --             ∙∙ {!!}
-- --             ∙∙ {!!}
-- --             ∙∙ sym (cong (sym ∘ σ (ptSn _)) (anti-c' m (suc (suc n)) b south)))
-- --     ∙∙ {!!}

-- --   helper : sym (σ-n) ∙∙ p ∙∙ σ-s ≡
-- --                   (sym σ-n
-- --                ∙∙ cong (σ north) (anti-c' (suc n) (suc m) a north)
-- --                ∙∙ (λ j → σ north (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd
-- --                                       (subst S₊ (cong suc
-- --                                         (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
-- --                                        (σ (ptSn _) (-S (suc m) (suc (suc n)) even-or-odd even-or-odd
-- --                                                    (subst S₊
-- --                                                     (cong suc
-- --                                                      (((λ i₁ → suc (+-suc n m i₁)) ∙ (λ i₁ → suc (+-comm (suc n) m i₁)))
-- --                                                       ∙ sym (+-suc m (suc n))))
-- --                                                     (∪ₗ (suc n) m a b))) j))))
-- --                ∙∙ sym (cong (σ north) (anti-c' (suc n) (suc m) a south))
-- --                ∙∙ σ-s) -- total minus : (2 + n)*(2 + m) + (1 + m)(2 + n) + m*(1 + n) = nm + (1 + m)n + m*(1 + n) = nm + n + m
-- --   helper = (λ k → sym (σ-n) ∙∙ rUnit p k ∙∙ σ-s)
-- --         ∙∙ (λ k → sym (σ-n)
-- --                ∙∙ (λ i → σ north (anti-c' (suc n) (suc m) a north (i ∧ k)))
-- --                ∙∙ (λ j → σ north (anti-c' (suc n) (suc m) a (merid b j) k))
-- --                ∙∙ (λ i → σ north (anti-c' (suc n) (suc m) a south (~ i ∧ k)))
-- --                ∙∙ σ-s)
-- --         ∙∙ (λ k → sym σ-n
-- --                ∙∙ cong (σ north) (anti-c' (suc n) (suc m) a north)
-- --                ∙∙ (λ j → σ north (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd
-- --                                       (subst S₊ (cong suc
-- --                                         (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
-- --                                        (σ (ptSn _) (anti-c' _ _ b a k) j))))
-- --                ∙∙ sym (cong (σ north) (anti-c' (suc n) (suc m) a south))
-- --                ∙∙ σ-s)
-- --         ∙ (λ k → sym σ-n
-- --                ∙∙ cong (σ north) (anti-c' (suc n) (suc m) a north)
-- --                ∙∙ (λ j → σ north (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd
-- --                                       (subst S₊ (cong suc
-- --                                         (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
-- --                                        (σ (ptSn _) (-S (suc m) (suc (suc n)) even-or-odd even-or-odd
-- --                                                    (subst S₊
-- --                                                     (cong suc
-- --                                                      (((λ i₁ → suc (+-suc n m i₁)) ∙ (λ i₁ → suc (+-comm (suc n) m i₁)))
-- --                                                       ∙ sym (+-suc m (suc n))))
-- --                                                     (∪ₗ (suc n) m a b))) j))))
-- --                ∙∙ sym (cong (σ north) (anti-c' (suc n) (suc m) a south))
-- --                ∙∙ σ-s)

-- -- anti-c : (n m : ℕ)
-- --        → (x : S₊ (suc n))
-- --        →  (y : S₊ (suc m))
-- --        →  (∪ₗ n m x y) ≡
-- --               (-S (suc n) (suc m) even-or-odd even-or-odd (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (∪ᵣ m n y x))) 
-- -- anti-c zero m x y = {!x!}
-- -- anti-c (suc n) zero x y = {!!}
-- -- anti-c (suc n) (suc m) north y = refl
-- -- anti-c (suc n) (suc m) south y = refl
-- -- anti-c (suc n) (suc m) (merid a i) b k = {!!}
-- --   where
-- --   helper : (σ (ptSn (suc (n + suc (suc m)))) (∪ₗ n (suc m) a b))
-- --          ≡ cong (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd)
-- --                 (cong (subst S₊ (cong suc (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m)))))
-- --                 λ i → ∪ᵣ (suc m) (suc n) b (merid a i))
-- --   helper =
-- --        cong (σ (ptSn (suc (n + suc (suc m))))) (anti-c n (suc m) a b) -- cong (λ x → cong ∣_∣ (σ (ptSn (suc (n + suc (suc m)))) x)) {!anti-c !}
-- --     ∙∙ {!!}
-- --     ∙∙ {!!}
-- --     ∙∙ {!!}
-- --     ∙∙ λ _
-- --       → cong (-S (suc (suc n)) (suc (suc m)) even-or-odd even-or-odd)
-- --                 (cong (subst S₊ (cong suc (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m)))))
-- --                 λ i → subst S₊ (cong (2 +_) (sym (+-suc m (suc n))))
-- --                                   (σ (ptSn _) (∪ᵣ _ _ b a) (~ i)))



-- -- ∪ₗ-comm : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n)) → (q : is-even (suc m) ⊎ is-odd (suc m))
-- --       → (x : _) (y : _) → ∪ₗ n m x y ≡ -S (suc n) (suc m) p q (subst S₊ (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (∪ₗ m n y x))
-- -- ∪ₗ-comm zero zero p q base base = refl
-- -- ∪ₗ-comm zero zero p q base (loop i) k =
-- --   -S 1 1 p q
-- --          (subst S₊ (cong suc (+-comm zero 1 ∙ sym (+-suc zero zero)))
-- --           (rCancel ((merid base)) (~ k) i))
-- -- ∪ₗ-comm zero zero p q (loop i) base k = rCancel ((merid base)) k i
-- -- ∪ₗ-comm zero zero p q (loop i) (loop j) = {!!} -- true but lazy
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) base north = refl
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) base south = refl
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) base (merid a i) = {!!} --blabla
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) (loop i) north k = rCancel (merid north) k i
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) (loop i) south k = (cong (σ north) (sym (merid (ptSn _))) ∙ rCancel (merid north)) k i
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inl x₂) (loop i) (merid a j) = {!!}
-- -- ∪ₗ-comm zero (suc m) (inr x₁) (inr x₂) x y = {!!}
-- -- ∪ₗ-comm (suc n) zero p q x y = {!!}
-- -- ∪ₗ-comm (suc n) (suc m) (inl x₁) q x y = {!!}
-- -- ∪ₗ-comm (suc n) (suc m) (inr x₁) q x y = {!!}


-- -- test : {!!}
-- -- test = {!!}


-- -- -- ∪-l : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → ∥ S₊ (suc (n + suc m)) ∥ suc (suc (suc (n + suc m)))
-- -- -- ∪-l zero m base y = 0ₖ _
-- -- -- ∪-l zero m (loop i) y = Kn→ΩKn+1 _ ∣ y ∣ i
-- -- -- ∪-l (suc n) m north y = 0ₖ _
-- -- -- ∪-l (suc n) m south y = 0ₖ _
-- -- -- ∪-l (suc n) m (merid a i) y = Kn→ΩKn+1 _ (∪-l n m a y) i

-- -- -- ∪-r : (n m : ℕ) → S₊ (suc n) →  S₊ (suc m) → ∥ S₊ (suc (n + suc m)) ∥ suc (suc (suc (n + suc m)))
-- -- -- ∪-r n zero x base = 0ₖ _
-- -- -- ∪-r zero zero base (loop i) = 0ₖ _
-- -- -- ∪-r zero zero (loop i₁) (loop i) = ∪-alt zero zero (inr tt) (inr tt) (loop i₁) (loop i)
-- -- -- ∪-r (suc n) zero x (loop i) = Kn→ΩKn+1 _ ∣ subst S₊ (cong suc (+-comm 1 n)) x ∣ (~ i)
-- -- -- ∪-r n (suc m) x north = 0ₖ _
-- -- -- ∪-r n (suc m) x south = 0ₖ _
-- -- -- ∪-r n (suc m) x (merid a i) = Kn→ΩKn+1 _ (subst coHomK (sym (+-suc n (suc m))) (∪-r n m x a)) (~ i)

-- -- -- u-l≡u-r-comm : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n)) → (q : is-even (suc m) ⊎ is-odd (suc m)) →
-- -- --   (x : _) (y : _) → ∪-l n m x y ≡ subber n m (miner (suc n) (suc m) p q (∪-r m n y x))
-- -- -- u-l≡u-r-comm zero p q m x y = {!!}
-- -- -- u-l≡u-r-comm (suc n) zero p q x y = {!!}
-- -- -- u-l≡u-r-comm (suc n) (suc m) p q north y = refl
-- -- -- u-l≡u-r-comm (suc n) (suc m) p q south y = refl
-- -- -- u-l≡u-r-comm (suc n) (suc m) (inl x) (inl x₁) (merid a i) y = {!!}
-- -- --   where -- ubst coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m)))
-- -- --   help2 : (Kn→ΩKn+1 (suc (n + suc (suc m))) (∪-l n (suc m) a y)) ≡
-- -- --           sym (cong (subber (suc n) (suc m)) (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inl x) (inl x₁)))
-- -- --               (Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- --               (subst coHomK (λ i₁ → suc (+-suc m (suc n) (~ i₁)))
-- -- --                 (∪-r (suc m) n y a)))))
-- -- --   help2 = {!!}
-- -- --         ∙∙ {!!}
-- -- --         ∙∙ cong sym (cong (cong (subber (suc n) (suc m))) λ i j → trMap-miner-Right (suc (suc n)) (suc (suc m)) (inl x) x₁ (~ i) (Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- --                                                                                  (subst coHomK (λ i₁ → suc (+-suc m (suc n) (~ i₁)))
-- -- --                                                                                    (∪-r (suc m) n y a)) j))
-- -- -- u-l≡u-r-comm (suc n) (suc m) (inl x) (inr x₁) (merid a i) y = {!!}
-- -- -- u-l≡u-r-comm (suc n) (suc m) (inr x) (inl x₁) (merid a i) y = {!!}
-- -- -- u-l≡u-r-comm (suc n) (suc m) (inr x) (inr x₁) (merid a i) y = {!!}

-- -- -- u-l≡u-r : (n m : ℕ) → (x : _) (y : _) → ∪-l n m x y ≡  (∪-r n m x y)
-- -- -- u-l≡u-r zero zero base base = refl
-- -- -- u-l≡u-r zero zero base (loop i) = refl
-- -- -- u-l≡u-r zero zero (loop i) base = {!!}
-- -- -- u-l≡u-r zero zero (loop i) (loop i₁) = {!!}
-- -- -- u-l≡u-r zero (suc m) base north = refl
-- -- -- u-l≡u-r zero (suc m) base south = refl
-- -- -- u-l≡u-r zero (suc m) base (merid a i) k = (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 _ ∘ subst coHomK refl) (u-l≡u-r zero m base a)) k (~ i)
-- -- -- u-l≡u-r zero (suc m) (loop i) north k = Kn→ΩKn+10ₖ _ k i -- Kn→ΩKn+10ₖ _ k (~ i)
-- -- -- u-l≡u-r zero (suc m) (loop i) south k = ((cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) ∙ Kn→ΩKn+10ₖ _) k i
-- -- -- u-l≡u-r zero (suc m) (loop i) (merid a j) z = helper i j z
-- -- --   where
-- -- --   helper : Cube (λ j z → (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 _ ∘ subst coHomK refl) (u-l≡u-r zero m base a)) z (~ j))
-- -- --                 (λ j z → (sym (Kn→ΩKn+10ₖ _) ∙ cong (Kn→ΩKn+1 _ ∘ subst coHomK refl) (u-l≡u-r zero m base a)) z (~ j))
-- -- --                 (λ i z → ∣ rCancel (merid north) z i ∣) (λ i z → ((cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) ∙ Kn→ΩKn+10ₖ _) z i)
-- -- --                 (λ i j → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i) λ i j → Kn→ΩKn+1 (suc (suc m)) (subst coHomK (λ i₁ → suc (suc m)) (∪-r zero m (loop i) a)) (~ j)
-- -- --   helper i j z =
-- -- --     comp (λ k → coHomK (3 + m))
-- -- --          (λ k → λ { (i = i0) → compPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _ ∘ subst coHomK refl) (u-l≡u-r zero m base a)) k z (~ j)
-- -- --                    ; (i = i1) → compPath-filler (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _ ∘ subst coHomK refl) (u-l≡u-r zero m base a)) k z (~ j)
-- -- --                    ; (j = i0) → ∣ rCancel (merid north) z i ∣ -- ∣ rCancel (merid north) (z ∧ k) i ∣
-- -- --                    ; (j = i1) → ((cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) ∙ Kn→ΩKn+10ₖ _) z i
-- -- --                    ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i -- Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                    ; (z = i1) → Kn→ΩKn+1 (suc (suc m)) (subst coHomK (λ i₁ → suc (suc m)) (u-l≡u-r zero m (loop i) a k)) (~ j)})
-- -- --          (comp (λ k → coHomK (3 + m))
-- -- --                (λ k → λ { (i = i0) → Kn→ΩKn+10ₖ _ (~ z ∨ ~ k) (~ j)
-- -- --                          ; (i = i1) → Kn→ΩKn+10ₖ _ (~ z ∨ ~ k) (~ j)
-- -- --                          ; (j = i0) → ∣ rCancel (merid north) z i ∣
-- -- --                          ; (j = i1) → ((cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) ∙ Kn→ΩKn+10ₖ _) z i
-- -- --                          ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                          ; (z = i1) →
-- -- --                            doubleCompPath-filler
-- -- --                              (sym (Kn→ΩKn+10ₖ _))
-- -- --                              (λ i → Kn→ΩKn+1 (suc (suc m)) (subst coHomK (λ i₁ → suc (suc m)) (∪-l zero m (loop i) a)))
-- -- --                                (Kn→ΩKn+10ₖ _) (~ k) i (~ j)})
-- -- --                 (comp (λ k → coHomK (3 + m))
-- -- --                       (λ k → λ { (i = i0) → 0ₖ _
-- -- --                                 ; (i = i1) → 0ₖ _
-- -- --                                 ; (j = i0) → ∣ rCancel (merid north) z i ∣
-- -- --                                 ; (j = i1) → ((cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) ∙ Kn→ΩKn+10ₖ _) z i
-- -- --                                 ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                                 ; (z = i1) →
-- -- --                                   inst3 _ (sym (Kn→ΩKn+10ₖ _)
-- -- --                                         ∙∙ (λ i → Kn→ΩKn+1 (suc (suc m)) (subst coHomK (λ i₁ → suc (suc m)) (∪-l zero m (loop i) a)))
-- -- --                                         ∙∙ Kn→ΩKn+10ₖ _) k i j})
-- -- --                        (comp (λ k → coHomK (3 + m))
-- -- --                       (λ k → λ { (i = i0) → 0ₖ _
-- -- --                                 ; (i = i1) → 0ₖ _
-- -- --                                 ; (j = i0) → ∣ rCancel (merid north) (z ∧ k) i ∣
-- -- --                                 ; (j = i1) → compPath-filler (cong (Kn→ΩKn+1 _) (cong ∣_∣ (sym (merid (ptSn (suc m)))))) (Kn→ΩKn+10ₖ _) k z i
-- -- --                                 ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                                 ; (z = i1) → 
-- -- --                                   doubleCompPath-filler (sym (Kn→ΩKn+10ₖ _))
-- -- --                                            ((λ i → Kn→ΩKn+1 (suc (suc m))
-- -- --                                            (subst coHomK (λ i₁ → suc (suc m)) (∪-l zero m (loop i) a))))
-- -- --                                            (Kn→ΩKn+10ₖ _) k j i})
-- -- --                        (comp (λ k → coHomK (3 + m))
-- -- --                              (λ k → λ { (i = i0) → 0ₖ _
-- -- --                                        ; (i = i1) → 0ₖ _
-- -- --                                        ; (j = i0) → ∣ (merid north ∙ sym (merid north)) i ∣ -- ∣ (merid north ∙ sym (merid north)) i ∣
-- -- --                                        ; (j = i1) → Kn→ΩKn+1 (suc (suc m)) (cong ∣_∣ (sym (merid (ptSn (suc m)))) z) i -- Kn→ΩKn+1 (suc (suc m)) ∣ merid (ptSn (suc m)) (~ z) ∣ i
-- -- --                                        ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                                        ; (z = i1) → Kn→ΩKn+1 (suc (suc m))
-- -- --                                                        (transportRefl ∣ ((merid a) ∙ (sym (merid (ptSn (suc m))))) j ∣ (~ k)) i})
-- -- --                              (comp (λ k → coHomK (3 + m))
-- -- --                              (λ k → λ { (i = i0) → 0ₖ _
-- -- --                                        ; (i = i1) → 0ₖ _
-- -- --                                        ; (j = i0) → ∣ (merid north ∙ sym (merid north)) i ∣
-- -- --                                        ; (j = i1) → Kn→ΩKn+1 (suc (suc m)) ∣ merid (ptSn (suc m)) (~ z ∨ ~ k) ∣ i
-- -- --                                        ; (z = i0) → Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i
-- -- --                                        ; (z = i1) → Kn→ΩKn+1 (suc (suc m))
-- -- --                                                        ∣ compPath-filler (merid a) (sym (merid (ptSn (suc m)))) k j ∣ i})
-- -- --                                     (Kn→ΩKn+1 (suc (suc m)) ∣ merid a j ∣ i))))))
-- -- -- u-l≡u-r (suc n) m x y = {!!}

-- -- -- -- ∪-alt'-anticomm : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n))
-- -- -- --                → (q : is-even (suc m) ⊎ is-odd (suc m))
-- -- -- --                → (x : (S₊ (suc n))) → (y : (S₊ (suc m)))
-- -- -- --                → ∪-alt' n m p q x y ≡ subber n m (miner (suc n) (suc m) p q (∪-alt' m n q p y x))
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north north = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north south = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north (merid a i) = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south north = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south south = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south (merid a i) = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) north = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) south = refl
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) (merid b j) = {!a!}
-- -- -- -- ∪-alt'-anticomm (suc n) zero (inl x₁) (inr x₂) x y = {!!}
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inl x₁) (inr x₂) x y = {!!}
-- -- -- -- ∪-alt'-anticomm zero (suc m) (inr x₁) (inl x₂) x y = {!!}
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inr x₁) (inl x₂) x y = {!refl!}
-- -- -- -- ∪-alt'-anticomm zero zero (inr x₁) (inr x₂) x y = {!!}
-- -- -- -- ∪-alt'-anticomm zero (suc m) (inr x₁) (inr x₂) x y = {!!}
-- -- -- -- ∪-alt'-anticomm (suc n) zero (inr x₁) (inr x₂) x y i = subber (suc n) zero (miner (suc (suc n)) 1 (prop-help _ even-or-odd (inr x₁) i) (inr tt) (zero-l n y x))
-- -- -- -- ∪-alt'-anticomm (suc n) (suc m) (inr x₁) (inr x₂) x y = {!!}



-- -- -- -- -- {-
-- -- -- -- -- ∪-alt-assoc : (n m l : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n)) (q : is-even (suc m) ⊎ is-odd (suc m)) (r : is-even (suc l) ⊎ is-odd (suc l))
-- -- -- -- --               → (hLevHyp : (a b : ℕ) → isOfHLevel (2 + (suc (a + suc b))) (S₊ (suc (a + suc b))))
-- -- -- -- --               → (qr : is-even (suc (m + suc l)) ⊎ is-odd (suc (m + suc l)))
-- -- -- -- --               → (pr : is-even (suc (n + suc m)) ⊎ is-odd (suc (n + suc m)))
-- -- -- -- --               → (x : (S₊ (suc n))) → (y : (S₊ (suc m))) (z : (S₊ (suc l)))
-- -- -- -- --               → ∪-alt n (m + suc l) p qr x (trRec (hLevHyp m l) (λ x → x) (∪-alt m l q r y z))
-- -- -- -- --               ≡ subst coHomK (sym (+-assoc (suc n) (suc m) (suc l))) (∪-alt (n + suc m) l pr r (trRec (hLevHyp n m) (λ x → x) (∪-alt n m p q x y)) z)
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr base base base = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr base base (loop i) = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr base (loop i) base = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr base (loop i) (loop i₁) = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) base base = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) base (loop i₁) = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) (loop i₁) base = refl
-- -- -- -- -- ∪-alt-assoc zero zero zero p q r hLevHyp qr pr (loop i) (loop j) (loop k) = {!!}
-- -- -- -- -- ∪-alt-assoc zero zero (suc l) p q r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc zero (suc m) l p q r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) zero l p q r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) zero p q r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) north y z = refl
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) south y z = refl
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) north z = refl
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) south z = refl
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) north = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) south = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inl x₅) (merid a i) (merid a₁ i₁) (merid a₂ i₂) = {!!}
-- -- -- -- --   where

-- -- -- -- --   cong-below : ∀ {ℓ} {A : Type ℓ} {x y z w pt : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → cong-∙∙ (λ x → pt) p q r ≡ rUnit refl
-- -- -- -- --   cong-below p q r = refl

-- -- -- -- --   help₁ : (a : _) (b : _) (c : _) → cong (λ a → cong (λ b → cong (λ c → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄)
-- -- -- -- --       a
-- -- -- -- --       (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆)
-- -- -- -- --        (∪-alt (suc m) (suc l) (inl x₂) (inl x₃) b c))) (merid c)) (merid b)) (merid a)
-- -- -- -- --       ≡
-- -- -- -- --       {!!}{-
-- -- -- -- --       ({!!} ∙∙ cong (λ a → cong (λ b → cong (λ a → subst coHomK
-- -- -- -- --       (sym (λ i₁ → suc (suc (+-assoc n (suc (suc m)) (suc (suc l)) i₁))))
-- -- -- -- --       (∪-alt (suc (n + suc (suc m))) (suc l) (inl x₅) (inl x₃)
-- -- -- -- --        (rec₊ (hLevHyp (suc n) (suc m)) (λ x₆ → x₆)
-- -- -- -- --         (∪-alt (suc n) (suc m) (inl x₁) (inl x₂) a b))
-- -- -- -- --        c)) (merid a)) (merid b)) (merid c) ∙∙ {!!}) -}
-- -- -- -- --   help₁ a b c =
-- -- -- -- --        (λ r i j k → cong (cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))) ((sym (Kn→ΩKn+10ₖ _)
-- -- -- -- --                  ∙∙ cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
-- -- -- -- --                             (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c)))
-- -- -- -- --                  ∙∙ Kn→ΩKn+10ₖ _)) j k)
-- -- -- -- --     ∙∙ rUnit _
-- -- -- -- --     ∙∙ (λ r → (λ i → rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))) (i ∧ r)) ∙∙ (λ i j k
-- -- -- -- --                      → cong-∙∙ ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))) (sym (Kn→ΩKn+10ₖ _)) (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
-- -- -- -- --                             (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c)))) (Kn→ΩKn+10ₖ _) r j k)
-- -- -- -- --                      ∙∙ λ i → rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))) (~ i ∧ r))
-- -- -- -- --     ∙∙ (λ r → (rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l))))))))
-- -- -- -- --             ∙∙ (λ i j k → (cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))))
-- -- -- -- --                                  ((sym (Kn→ΩKn+10ₖ _)))
-- -- -- -- --                         ∙∙ (cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))))
-- -- -- -- --                                  (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
-- -- -- -- --                                                      (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c))))
-- -- -- -- --                         ∙∙ cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x))))
-- -- -- -- --                                  ((Kn→ΩKn+10ₖ _))) j k)
-- -- -- -- --            ∙∙ sym (rUnit (λ _ _ → 0ₖ (suc (suc (n + suc (suc (m + suc (suc l)))))))))
-- -- -- -- --     ∙∙ {!(cong ((cong (λ x → ∪-alt (suc n) (suc (m + suc (suc l))) (inl x₁) (inl x₄) (merid a i)
-- -- -- -- --                            (rec₊ (hLevHyp (suc m) (suc l)) (λ x₆ → x₆) x)))))
-- -- -- -- --                                  (cong (Kn→ΩKn+1 _) (Kn→ΩKn+1 _ (subst coHomK (sym (+-suc m (suc l)))
-- -- -- -- --                                                      (∪-alt m l (inr (even-suc→odd x₂)) (inr (even-suc→odd x₃)) b c))))!}
-- -- -- -- --     ∙∙ {!!}
-- -- -- -- --     ∙∙ {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inl x₄) (inr x₅) x y z = {!!} --⊥
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inl x₃) hLevHyp (inr x₄) pr x y z = {!!} --⊥
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inl x₂) (inr x₃) hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inl x₁) (inr x₂) r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- ∪-alt-assoc (suc n) (suc m) (suc l) (inr x₁) q r hLevHyp qr pr x y z = {!!}
-- -- -- -- -- -}

-- -- -- -- -- not-even-and-odd : (m : ℕ) → is-even m → is-odd m → ⊥
-- -- -- -- -- not-even-and-odd (suc (suc m)) x y = not-even-and-odd m x y

-- -- -- -- -- ∪-alt-anticomm : (n m : ℕ) → (p : is-even (suc n) ⊎ is-odd (suc n))
-- -- -- -- --               → (q : is-even (suc m) ⊎ is-odd (suc m))
-- -- -- -- --               → (x : (S₊ (suc n))) → (y : (S₊ (suc m)))
-- -- -- -- --               → ∪-alt n m p q x y ≡ subber n m (miner (suc n) (suc m) p q (∪-alt m n q p y x))
-- -- -- -- -- ∪-alt-anticomm zero zero (inr x) (inr x₁) base base = refl
-- -- -- -- -- ∪-alt-anticomm zero zero (inr x) (inr x₁) base (loop i) = refl
-- -- -- -- -- ∪-alt-anticomm zero zero (inr x) (inr x₁) (loop i) base = refl
-- -- -- -- -- ∪-alt-anticomm zero zero (inr x) (inr x₁) (loop i) (loop j) k = helper' k i j
-- -- -- -- --   where
-- -- -- -- --   helper' : Path (typ ((Ω^ 2) (coHomK-ptd 2)))
-- -- -- -- --                  (λ i j → ∪-alt zero zero (inr x) (inr x₁) (loop i) (loop j))
-- -- -- -- --                  λ i j → subber zero zero (trMap (miner-h 1 1 (inr x) (inr x₁)) (∪-alt zero zero (inr x) (inr x₁) (loop j) (loop i)))
-- -- -- -- --   helper' = inst2 _ _
-- -- -- -- --            ∙∙ rUnit _
-- -- -- -- --            ∙∙ cong (λ p → p ∙∙ (λ i j → ∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop (~ j))) ∙∙ sym p) (sym (transportRefl (λ _ _ → 0ₖ 2)))
-- -- -- -- --          ∙∙ (λ k → (λ i → congMinner' 1 1 tt tt (λ j₁ → 0ₖ 2) (~ k ∧ i))
-- -- -- -- --                  ∙∙ (λ i → congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop j)) (~ k))
-- -- -- -- --                  ∙∙ λ i → congMinner' 1 1 tt tt (λ j₁ → 0ₖ 2) (~ k ∧ ~ i))
-- -- -- -- --          ∙∙ sym (rUnit _)
-- -- -- -- --          ∙∙ (λ k i j → transportRefl (trMap (miner-h 1 1 (inr x) (inr x₁)) (∪-alt zero zero (inr x) (inr x₁) (loop (~ i)) (loop j))) (~ k))
-- -- -- -- --          ∙∙ inst _  _
-- -- -- -- -- ∪-alt-anticomm zero (suc m) p q base north = refl
-- -- -- -- -- ∪-alt-anticomm zero (suc m) p q base south = refl
-- -- -- -- -- ∪-alt-anticomm zero (suc m) p q base (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm zero (suc m) p q (loop i) north = refl
-- -- -- -- -- ∪-alt-anticomm zero (suc m) p q (loop i) south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) north base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) north (loop i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) south base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) south (loop i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) (merid a i) base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inr x₂) (inr x₁) north base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inr x₂) (inr x₁) south base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inr x₂) (inr x₁) (merid a i) base = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inr x₂) (inr x₁) north (loop i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inr x₂) (inr x₁) south (loop i) = refl
-- -- -- -- -- ∪-alt-anticomm zero (suc m) (inr x₁) (inl x) (loop i) (merid a j) k = helper' k i j
-- -- -- -- --   where

-- -- -- -- --   other-help : (m : ℕ) (a : _) (x : _)
-- -- -- -- --              → sym (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
-- -- -- -- --                     (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
-- -- -- -- --               ≡ (((∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a)
-- -- -- -- --            ∙∙
-- -- -- -- --            (λ i₂ →
-- -- -- -- --               subber zero m
-- -- -- -- --               (trMap (miner-h 1 (suc m) (inr tt) (inr (even-suc→odd x)))
-- -- -- -- --                (∪-alt m zero (inr (even-suc→odd x)) (inr tt) a (loop i₂))))
-- -- -- -- --            ∙∙
-- -- -- -- --            (sym (∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a))))
-- -- -- -- --   other-help zero base tt =
-- -- -- -- --     cong sym (transportRefl (refl ∙∙ (cong (∪-alt zero zero even-or-odd (inr tt) base) loop) ∙∙ refl))
-- -- -- -- --            ∙∙ cong sym (sym (rUnit (cong (∪-alt zero zero even-or-odd (inr tt) base) loop)))
-- -- -- -- --            ∙∙ sym (congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr tt) (inr tt) base (loop j)))
-- -- -- -- --            ∙∙ (λ k i₂ → transportRefl (trMap (miner-h 1 1 (inr tt) (inr tt))
-- -- -- -- --                                    (∪-alt zero zero (inr tt) (inr tt) base (loop i₂))) (~ k))
-- -- -- -- --            ∙∙ rUnit _
-- -- -- -- --   other-help zero (loop i) tt =
-- -- -- -- --     cong sym (transportRefl (refl ∙∙ (cong (∪-alt zero zero even-or-odd (inr tt) (loop i)) loop) ∙∙ refl))
-- -- -- -- --            ∙∙ cong sym (sym (rUnit (cong (∪-alt zero zero even-or-odd (inr tt) (loop i)) loop)))
-- -- -- -- --            ∙∙ sym (congMinner' 1 1 tt tt (λ j → ∪-alt zero zero (inr tt) (inr tt) (loop i) (loop j)))
-- -- -- -- --            ∙∙ (λ k i₂ → transportRefl (trMap (miner-h 1 1 (inr tt) (inr tt))
-- -- -- -- --                                    (∪-alt zero zero (inr tt) (inr tt) (loop i) (loop i₂))) (~ k))
-- -- -- -- --            ∙∙ rUnit _
-- -- -- -- --   other-help (suc m) north x =
-- -- -- -- --     cong sym (λ k → (transport
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
-- -- -- -- --        ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) north) loop)) (~ k))))
-- -- -- -- --     ∙∙ (λ k → sym (transp
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
-- -- -- -- --             λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) north (loop j))))
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) north) loop)))
-- -- -- -- --      ∙ rUnit _
-- -- -- -- --   other-help (suc m) south x =
-- -- -- -- --     cong sym (λ k → (transport
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
-- -- -- -- --        ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) south) loop)) (~ k))))
-- -- -- -- --     ∙∙ (λ k → sym (transp
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
-- -- -- -- --             λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) south (loop j))))
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) south) loop)))
-- -- -- -- --      ∙ rUnit _
-- -- -- -- --   other-help (suc m) (merid a i) x = -- cong suc (+-comm m (suc n) ∙ sym (+-suc n m))
-- -- -- -- --        cong sym (λ k → (transport
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂) ≡
-- -- -- -- --           0ₖ (isSetℕ _ _ (+-comm (suc (suc m)) 1 ∙ sym (+-suc 0 (suc (suc m)))) (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) k i₂))
-- -- -- -- --        ((rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i)) loop)) (~ k))))
-- -- -- -- --     ∙∙ (λ k → sym (transp
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k)) ≡
-- -- -- -- --           0ₖ ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i₂ ∨ k))) k
-- -- -- -- --             λ j → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∧ k))) (~ k) (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i) (loop j))))
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m))) (sym (congMinner' 1 (suc (suc m)) tt (even-suc→odd x) (cong (∪-alt (suc m) zero (inr (even-suc→odd x)) (inr tt) (merid a i)) loop)))
-- -- -- -- --      ∙ rUnit _

-- -- -- -- --   helper' : (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))) ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (suc m))
-- -- -- -- --           (∪-alt zero m (inr tt) even-or-odd (loop i₁) a))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m))))))
-- -- -- -- --       ≡
-- -- -- -- --       flipSquare (
-- -- -- -- --       cong (cong (subber zero (suc m)))
-- -- -- -- --       (cong (cong (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inl x))))
-- -- -- -- --        ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + 1))))))) ∙∙
-- -- -- -- --        (cong (Kn→ΩKn+1 (suc (m + 1))) (sym (∪-alt-id m a) ∙∙
-- -- -- -- --               (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙
-- -- -- -- --               ∪-alt-id m a))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + 1)))))))))
-- -- -- -- --   helper' =
-- -- -- -- --        cong (λ x → (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))) ∙∙ x
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
-- -- -- -- --             (cong (cong (Kn→ΩKn+1 (suc (suc m))))
-- -- -- -- --                   ((λ k → rUnit (cong (λ z → ∪-alt zero m (inr tt) (prop-help (suc m) even-or-odd (inr (even-suc→odd {n = suc (suc (suc m))} x)) k) z a) loop) k)
-- -- -- -- --                 ∙∙ (λ k → (λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a (k ∧ i))
-- -- -- -- --                        ∙∙ (λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd {n = suc (suc (suc m))} x)) (loop i) a k)
-- -- -- -- --                        ∙∙ λ i → ∪-alt-anticomm zero m (inr tt) (inr (even-suc→odd x)) base a (k ∧ ~ i))
-- -- -- -- --                 ∙∙ sym (other-help m a x)))
-- -- -- -- --     ∙∙ sym (sym-∙∙ ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))))
-- -- -- -- --                (cong (Kn→ΩKn+1 (suc (suc m)))
-- -- -- -- --                       (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
-- -- -- -- --                                  (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a)))
-- -- -- -- --                (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
-- -- -- -- --     ∙∙ (λ k → sym (cong (cong (trMap-miner-Right 1 (suc (suc m)) (inr x₁) x (~ k)))
-- -- -- -- --                    ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m)))))))
-- -- -- -- --                    ∙∙ cong (Kn→ΩKn+1 (suc (suc m)))
-- -- -- -- --                       (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) i))
-- -- -- -- --                                  (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))))
-- -- -- -- --     ∙∙ inst _ _
-- -- -- -- --     ∙∙ λ k i j →
-- -- -- -- --          transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))) (i ∨ ~ k))) (~ k)
-- -- -- -- --              (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inl x))
-- -- -- -- --                ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k))))))
-- -- -- -- --                ∙∙ cong (Kn→ΩKn+1 ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k)))
-- -- -- -- --                        (transp (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k ∧ i)) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k ∧ i))) k
-- -- -- -- --                                (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
-- -- -- -- --                ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))) (~ k)))))) j i))
-- -- -- -- -- ∪-alt-anticomm zero (suc m) (inr x₁) (inr x) (loop i) (merid a j) k =
-- -- -- -- --   helper' k i j
-- -- -- -- --   where
-- -- -- -- --   help2 : (m : ℕ) (x : is-even (suc m)) → (y : _) → (a : _)
-- -- -- -- --         → ∪-alt-anticomm zero m (inr tt) y base a
-- -- -- -- --         ∙∙ (λ i₁ → subber zero m
-- -- -- -- --          (trMap (miner-h 1 (suc m) (inr tt) y)
-- -- -- -- --           (∪-alt m zero y (inr tt) a (loop i₁))))
-- -- -- -- --         ∙∙ sym (∪-alt-anticomm zero m (inr tt) y base a)
-- -- -- -- --         ≡ transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i))
-- -- -- -- --                                      (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a)
-- -- -- -- --   help2 (suc m) x (inl x₁) north =
-- -- -- -- --     sym (rUnit _)
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m)))
-- -- -- -- --             (λ k → cong (trMap-miner-Right 1 (suc (suc m)) (inr tt) x₁ k)
-- -- -- -- --               λ i₁ → ∪-alt (suc m) zero (inl x₁) (inr tt) north (loop i₁))
-- -- -- -- --     ∙∙ rUnit _
-- -- -- -- --     ∙∙ (λ k → (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --           ∙∙ (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) k)
-- -- -- -- --                         (∪-alt (suc m) zero (inl x) (inr tt) north (loop j)))
-- -- -- -- --            ∙∙ λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ ~ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --     ∙∙ ((λ k → (λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) j (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --              ∙∙ cong (subber zero (suc m)) (λ j → ∪-alt (suc m) zero (prop-help m (inl x) even-or-odd k) (inr tt) north (loop j))
-- -- -- -- --              ∙∙ λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (~ j) (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --      ∙ sym (rUnit _))
-- -- -- -- --     ∙∙ (λ k → transp (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)))
-- -- -- -- --                       (~ k)
-- -- -- -- --               λ j → transp (λ i → coHomK ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∧ ~ k))) k
-- -- -- -- --                             (∪-alt (suc m) zero even-or-odd (inr tt) north (loop j)))
-- -- -- -- --     ∙∙ cong (transport (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i)))
-- -- -- -- --             (rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) north) loop))
-- -- -- -- --   help2 (suc m) x (inl x₁) south = 
-- -- -- -- --        sym (rUnit _)
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m)))
-- -- -- -- --             (λ k → cong (trMap-miner-Right 1 (suc (suc m)) (inr tt) x₁ k)
-- -- -- -- --               λ i₁ → ∪-alt (suc m) zero (inl x₁) (inr tt) south (loop i₁))
-- -- -- -- --     ∙∙ rUnit _
-- -- -- -- --     ∙∙ (λ k → (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --           ∙∙ (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) k)
-- -- -- -- --                         (∪-alt (suc m) zero (inl x) (inr tt) south (loop j)))
-- -- -- -- --            ∙∙ λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ ~ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --     ∙∙ ((λ k → (λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) j (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --              ∙∙ cong (subber zero (suc m)) (λ j → ∪-alt (suc m) zero (prop-help m (inl x) even-or-odd k) (inr tt) south (loop j))
-- -- -- -- --              ∙∙ λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (~ j) (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --      ∙ sym (rUnit _))
-- -- -- -- --     ∙∙ (λ k → transp (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)))
-- -- -- -- --                       (~ k)
-- -- -- -- --               λ j → transp (λ i → coHomK ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∧ ~ k))) k
-- -- -- -- --                             (∪-alt (suc m) zero even-or-odd (inr tt) south (loop j)))
-- -- -- -- --     ∙∙ cong (transport (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i)))
-- -- -- -- --             (rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) south) loop))
-- -- -- -- --   help2 (suc m) x (inl x₁) (merid a i) = -- cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m)))
-- -- -- -- --        sym (rUnit _)
-- -- -- -- --     ∙∙ cong (cong (subber zero (suc m)))
-- -- -- -- --             (λ k → cong (trMap-miner-Right 1 (suc (suc m)) (inr tt) x₁ k)
-- -- -- -- --               λ i₁ → ∪-alt (suc m) zero (inl x₁) (inr tt) (merid a i) (loop i₁))
-- -- -- -- --     ∙∙ rUnit _
-- -- -- -- --     ∙∙ (λ k → (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --           ∙∙ (λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) k)
-- -- -- -- --                         (∪-alt (suc m) zero (inl x) (inr tt) (merid a i) (loop j)))
-- -- -- -- --            ∙∙ λ j → subst coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (k ∧ ~ j))
-- -- -- -- --                            (0ₖ _))
-- -- -- -- --     ∙∙ ((λ k → (λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) j (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --              ∙∙ cong (subber zero (suc m)) (λ j → ∪-alt (suc m) zero (prop-help m (inl x) even-or-odd k) (inr tt) (merid a i) (loop j))
-- -- -- -- --              ∙∙ λ j → transp (λ i → coHomK (isSetℕ _ _ (cong suc (+-comm (suc m) 1 ∙ sym (+-suc 0 (suc m))))
-- -- -- -- --                                              (+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (~ j) (i ∨ k)))
-- -- -- -- --                               k (0ₖ _))
-- -- -- -- --      ∙ sym (rUnit _))
-- -- -- -- --     ∙∙ (λ k → transp (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∨ ~ k)))
-- -- -- -- --                       (~ k)
-- -- -- -- --               λ j → transp (λ i → coHomK ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) (i ∧ ~ k))) k
-- -- -- -- --                             (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i) (loop j)))
-- -- -- -- --     ∙∙ cong (transport (λ i → 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i) ≡ 0ₖ ((+-comm (suc (suc m)) 1 ∙ sym (+-suc zero (suc (suc m)))) i)))
-- -- -- -- --             (rUnit (cong (∪-alt (suc m) zero even-or-odd (inr tt) (merid a i)) loop))
-- -- -- -- --   help2 (suc m) x (inr x₁) a = Cubical.Data.Empty.rec (not-even-and-odd _ x x₁)

-- -- -- -- --   helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))) ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (suc m))
-- -- -- -- --           (∪-alt zero m (inr tt) even-or-odd (loop i₁) a))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
-- -- -- -- --       ≡
-- -- -- -- --       flipSquare (cong (cong (subber zero (suc m)))
-- -- -- -- --       (cong (cong (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inr x))))
-- -- -- -- --        ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + 1)))))) ∙∙
-- -- -- -- --          (λ i₁ →
-- -- -- -- --             Kn→ΩKn+1 (suc (m + 1))
-- -- -- -- --             (((λ i₂ → ∪-alt-id m a (~ i₂)) ∙∙
-- -- -- -- --               (λ i₂ → ∪-alt m zero even-or-odd (inr tt) a (loop i₂)) ∙∙
-- -- -- -- --               ∪-alt-id m a)
-- -- -- -- --              i₁))
-- -- -- -- --          ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + 1))))))))))
-- -- -- -- --   helper' =
-- -- -- -- --        cong (λ x → cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))
-- -- -- -- --                   ∙∙ cong (Kn→ΩKn+1 (suc (suc m))) x
-- -- -- -- --                   ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m))))))
-- -- -- -- --              (rUnit (λ i₁ → ∪-alt zero m (inr tt) even-or-odd (loop i₁) a)
-- -- -- -- --            ∙∙ (λ k → (λ i → ∪-alt-anticomm zero m (inr tt) even-or-odd base a (i ∧ k))
-- -- -- -- --                    ∙∙ (λ i → ∪-alt-anticomm zero m (inr tt) even-or-odd (loop i) a k)
-- -- -- -- --                    ∙∙ λ i → ∪-alt-anticomm zero m (inr tt) even-or-odd base a (~ i ∧ k))
-- -- -- -- --            ∙∙ help2 m (odd-suc→even {n = (suc m)} x) even-or-odd a)
-- -- -- -- --     ∙∙ inst2 _ _
-- -- -- -- --     ∙ rUnit _
-- -- -- -- --     ∙∙ (λ k → transportRefl refl (~ k)
-- -- -- -- --             ∙∙ sym (cong sym ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))
-- -- -- -- --                      ∙∙ cong (Kn→ΩKn+1 (suc (suc m))) (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i))
-- -- -- -- --                                      (sym (∪-alt-id m a) ∙∙ (cong (∪-alt m zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id m a))
-- -- -- -- --                      ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m))))))))
-- -- -- -- --             ∙∙ transportRefl refl (~ k))
-- -- -- -- --     ∙∙ (λ k → (λ i → congMinner' 1 (suc (suc m)) tt x refl (~ k ∧ i))
-- -- -- -- --             ∙∙ sym (cong (λ z → congMinner' 1 (suc (suc m)) x₁ x z (~ k))
-- -- -- -- --                        (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc m))))))
-- -- -- -- --                      ∙∙ cong (Kn→ΩKn+1 (suc (suc m))) (transport (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) i))
-- -- -- -- --                                      (sym (∪-alt-id m a) ∙∙ cong (∪-alt m zero even-or-odd (inr tt) a) loop ∙∙ ∪-alt-id m a))
-- -- -- -- --                      ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc m)))))))
-- -- -- -- --                      ∙∙ λ i → congMinner' 1 (suc (suc m)) tt x refl (~ k ∧ ~ i))
-- -- -- -- --     ∙∙ sym (rUnit _)
-- -- -- -- --     ∙∙ cong sym
-- -- -- -- --        (λ k i j
-- -- -- -- --          → transp (λ i → coHomK ((cong suc (+-comm (suc m) 1 ∙ sym (+-suc zero (suc m)))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (trMap (miner-h 1 (suc (suc m)) (inr x₁) (inr x))
-- -- -- -- --                       ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m)))) (~ k))))))
-- -- -- -- --                      ∙∙ cong (Kn→ΩKn+1 ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) (~ k)))
-- -- -- -- --                              (transp (λ i → 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) (~ k ∧ i)) ≡ 0ₖ ((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m))) (~ k ∧ i))) k
-- -- -- -- --                                      (sym (∪-alt-id m a) ∙∙ cong (∪-alt m zero even-or-odd (inr tt) a) loop ∙∙ ∪-alt-id m a))
-- -- -- -- --                      ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (((+-comm (suc m) 1 ∙ sym (+-suc zero (suc m)))) (~ k)))))) i j)))
-- -- -- -- --     ∙∙ inst _ _
-- -- -- -- -- ∪-alt-anticomm (suc n) zero (inl x₂) (inr x₁) (merid a i) (loop j) k = {!!} -- helper' k i j
-- -- -- -- --   where
-- -- -- -- --   {-
-- -- -- -- --   help₁ : is-even zero → (x : _) (i : I)
-- -- -- -- --         → (sym (∪-alt-id zero (loop i)) ∙∙ (cong (∪-alt zero zero even-or-odd (inr tt) (loop i)) loop) ∙∙ ∪-alt-id zero (loop i))
-- -- -- -- --         ≡ sym ((transport (λ i → 0ₖ ((+-comm zero (suc (suc zero)) ∙ sym (+-suc (suc zero) zero)) i) ≡ 0ₖ ((+-comm zero (suc (suc zero)) ∙ sym (+-suc (suc zero) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero zero (inr tt) x z (loop i)) loop)))
-- -- -- -- --   help₁ y x i = sym (rUnit _)
-- -- -- -- --              ∙∙ (λ k j → ∪-alt-anticomm zero zero (inr tt) (inr tt) (loop i) (loop j) k)
-- -- -- -- --              ∙∙ (λ k j → transportRefl (congMinner' 1 1 tt tt (λ j → ∪-alt zero zero x (inr tt) (loop j) (loop i)) k j) k)
-- -- -- -- --               ∙  cong sym (sym (transportRefl (cong (λ z → ∪-alt zero zero (inr tt) even-or-odd z (loop i)) loop)))
-- -- -- -- --   help₂ : (n : ℕ) → is-even (suc (suc n)) → (x : _) (a : _) (i : I) →
-- -- -- -- --     (sym (∪-alt-id (suc (suc n)) (merid a i)) ∙∙
-- -- -- -- --        cong (∪-alt (suc (suc n)) zero even-or-odd (inr tt) (merid a i)) loop ∙∙
-- -- -- -- --        ∪-alt-id (suc (suc n)) (merid a i))
-- -- -- -- --       ≡
-- -- -- -- --       sym
-- -- -- -- --       (transport
-- -- -- -- --        (λ i₂ →
-- -- -- -- --           0ₖ
-- -- -- -- --           ((+-comm zero (suc (suc (suc (suc n)))) ∙ sym (+-suc (suc (suc (suc n))) zero))
-- -- -- -- --            i₂)
-- -- -- -- --           ≡
-- -- -- -- --           0ₖ
-- -- -- -- --           ((+-comm zero (suc (suc (suc (suc n)))) ∙ sym (+-suc (suc (suc (suc n))) zero))
-- -- -- -- --            i₂))
-- -- -- -- --        (cong (λ z → ∪-alt zero (suc (suc n)) (inr tt) x z (merid a i)) loop))
-- -- -- -- --   help₂ n evn (inl x) a i = Cubical.Data.Empty.rec (not-even-and-odd (suc n) x (even-suc→odd evn))
-- -- -- -- --   help₂ n evn (inr x) a i =
-- -- -- -- --        (λ k → cong (∪-alt (suc (suc n)) zero (prop-help _ even-or-odd (inr (even-suc→odd evn)) k) (inr tt) (merid a i)) loop ∙ refl)
-- -- -- -- --     ∙∙ (λ k → (λ j → ∪-alt-anticomm (suc (suc n)) zero (inr (even-suc→odd evn)) (inr tt) (merid a i) base (j ∧ k))
-- -- -- -- --             ∙∙ (λ j → ∪-alt-anticomm (suc (suc n)) zero (inr (even-suc→odd evn)) (inr tt) (merid a i) (loop j) k)
-- -- -- -- --             ∙∙ λ j → ∪-alt-anticomm (suc (suc n)) zero (inr (even-suc→odd evn)) (inr tt) (merid a i) base (~ j ∧ k))
-- -- -- -- --     ∙∙ sym (rUnit _)
-- -- -- -- --     ∙∙ cong (cong (subber (suc (suc n)) zero)) (congMinner (suc (suc (suc n))) 1 (even-suc→odd evn) tt
-- -- -- -- --             (cong (λ z → ∪-alt zero (suc (suc n)) (inr tt) (inr (even-suc→odd evn)) z (merid a i)) loop)) 
-- -- -- -- --     ∙∙ (λ k → transp (λ i → 0ₖ ((cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (i ∨ ~ k))
-- -- -- -- --                            ≡ 0ₖ ((cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                       λ j → transp (λ i → coHomK ((cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (i ∧ ~ k))) k
-- -- -- -- --                                     (∪-alt zero (suc (suc n)) (inr tt) (inr (even-suc→odd evn)) (loop (~ j)) (merid a i)))
-- -- -- -- --     ∙∙ (λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)))
-- -- -- -- --                                                  (+-comm zero (suc (suc (suc (suc n)))) ∙ sym (+-suc (suc (suc (suc n))) zero)) k i)
-- -- -- -- --                                ≡ 0ₖ (isSetℕ _ _ (cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)))
-- -- -- -- --                                                  (+-comm zero (suc (suc (suc (suc n)))) ∙ sym (+-suc (suc (suc (suc n))) zero)) k i))
-- -- -- -- --                          (sym (cong (λ z → ∪-alt zero (suc (suc n)) (inr tt) (inr (even-suc→odd evn)) z (merid a i)) loop)))
-- -- -- -- --     ∙∙ refl
-- -- -- -- --   help! : (n : ℕ) → is-even n → (x : _) → (a : _)
-- -- -- -- --         → (sym (∪-alt-id n a) ∙∙ (cong (∪-alt n zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id n a)
-- -- -- -- --         ≡ sym ((transport (λ i → 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i) ≡ 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero n (inr tt) x z a) loop)))

-- -- -- -- --   help! zero y (inr x) base = help₁ y (inr x) i0
-- -- -- -- --   help! zero y (inr x) (loop i) = help₁ y (inr x) i
-- -- -- -- --   help! (suc (suc n)) y (inl x) z = Cubical.Data.Empty.rec (not-even-and-odd (suc n) x (even-suc→odd y))
-- -- -- -- --   help! (suc (suc n)) y (inr x) north = help₂ n y (inr x) north i0
-- -- -- -- --   help! (suc (suc n)) y (inr x) south = help₂ n y (inr x) north i1
-- -- -- -- --   help! (suc (suc n)) y (inr x) (merid a i) = help₂ n y (inr x) a i

-- -- -- -- --   helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + 1))))))) ∙∙
-- -- -- -- --        (cong (Kn→ΩKn+1 (suc (n + 1)))
-- -- -- -- --           (sym (∪-alt-id n a) ∙∙ (cong (∪-alt n zero even-or-odd (inr tt) a) loop) ∙∙ ∪-alt-id n a))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + 1))))))
-- -- -- -- --       ≡
-- -- -- -- --       flipSquare (cong (cong (subber (suc n) zero))
-- -- -- -- --       (cong (cong (trMap (miner-h (suc (suc n)) 1 (inl x₂) (inr x₁))))
-- -- -- -- --        ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (suc n)))))) ∙∙
-- -- -- -- --          (cong
-- -- -- -- --             (Kn→ΩKn+1 (suc (suc n)))
-- -- -- -- --             (((λ i₂ → ∪-alt zero n (inr tt) even-or-odd (loop i₂) a))))
-- -- -- -- --          ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (suc n)))))))))))
-- -- -- -- --   helper' =
-- -- -- -- --        cong (λ p → ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + 1)))))))
-- -- -- -- --                  ∙∙ (cong (Kn→ΩKn+1 (suc (n + 1))) p)
-- -- -- -- --                  ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + 1))))))))
-- -- -- -- --              (help! n x₂ even-or-odd a)
-- -- -- -- --     ∙∙ sym (sym-∙∙ (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + 1)))))))
-- -- -- -- --                    (cong (Kn→ΩKn+1 (suc (n + 1)))
-- -- -- -- --                  (transport (λ i → 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i) ≡ 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero n (inr tt) even-or-odd z a) loop)))
-- -- -- -- --                    (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + 1)))))))
-- -- -- -- --     ∙∙ cong sym (λ k i j → trMap-miner-Left (suc (suc n)) 1 x₂ (inr tt) (~ k)
-- -- -- -- --                 ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + 1)))))) ∙∙
-- -- -- -- --        (cong (Kn→ΩKn+1 (suc (n + 1)))
-- -- -- -- --                  (transport (λ i → 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i) ≡ 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero n (inr tt) even-or-odd z a) loop)))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + 1))))))) i j))
-- -- -- -- --     ∙∙ cong sym
-- -- -- -- --        (λ k i j
-- -- -- -- --          → transp (λ i → coHomK ((cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (trMap (miner-h (suc (suc n)) 1 (inl x₂) (inr tt))
-- -- -- -- --                       ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (~ k))))))
-- -- -- -- --                      ∙∙ cong (Kn→ΩKn+1 ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) (~ k)))
-- -- -- -- --                              (transp (λ i → 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) (~ k ∧ i)) ≡ 0ₖ ((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)) (~ k ∧ i))) k
-- -- -- -- --                                      (cong (λ z → ∪-alt zero n (inr tt) even-or-odd z a) loop))
-- -- -- -- --                      ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (((+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (~ k)))))) i j)))
-- -- -- -- --     ∙∙ inst _ _ -}
-- -- -- -- -- ∪-alt-anticomm (suc (suc n)) zero (inr x₂) (inr x₁) (merid b i) (loop j) k = helper' k i j
-- -- -- -- --  -- cong suc (+-comm m (suc n) ∙ sym (+-suc n m))
-- -- -- -- --   where
-- -- -- -- --   help₂ : (n : ℕ) → (y : _) (b : _) (i : I) →
-- -- -- -- --           ((λ i₂ → ∪-alt (suc n) zero (inl y) (inr tt) (merid b i) (loop i₂)) ∙ refl)
-- -- -- -- --        ≡ transport (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i)
-- -- -- -- --                                                    ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z (merid b i)) loop)
-- -- -- -- --   help₂ n y b i =
-- -- -- -- --        (λ k → (λ j → ∪-alt-anticomm (suc n) zero (inl y) (inr tt) (merid b i) (loop j) k) ∙ refl)
-- -- -- -- --     ∙∙ sym (rUnit _)
-- -- -- -- --     ∙∙ ((λ k j → subber (suc n) zero (trMap-miner-Left (suc (suc n)) 1 y (inr tt) k (∪-alt zero (suc n) (inr tt) even-or-odd (loop j) (merid b i))))
-- -- -- -- --     ∙∙ (λ k j → transp (λ i → coHomK ((cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (i ∨ k))) k
-- -- -- -- --                         (transp (λ i → 0ₖ ((cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (i ∧ k))
-- -- -- -- --                                       ≡ 0ₖ ((cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero))) (i ∧ k))) (~ k)
-- -- -- -- --                                 (λ j → ∪-alt zero (suc n) (inr tt) even-or-odd (loop j) (merid b i)) j))
-- -- -- -- --     ∙∙ λ k → transport (λ i → 0ₖ (isSetℕ _ _ (cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)))
-- -- -- -- --                                                (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) k i)
-- -- -- -- --                                ≡ 0ₖ (isSetℕ _ _ (cong suc (+-comm zero (suc (suc n)) ∙ sym (+-suc (suc n) zero)))
-- -- -- -- --                                                  (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) k i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z (merid b i)) loop))

-- -- -- -- --   help! : (n : ℕ) → (is-odd (suc n)) → (y : _) (b : _) →
-- -- -- -- --           ((λ i₂ → ∪-alt (suc n) zero y (inr tt) b (loop i₂)) ∙ refl)
-- -- -- -- --        ≡ transport (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i)
-- -- -- -- --                                                    ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z b) loop)
-- -- -- -- --   help! n odd (inl x) north = help₂ n x (ptSn (suc n)) i0
-- -- -- -- --   help! n odd (inl x) south = help₂ n x (ptSn (suc n)) i1
-- -- -- -- --   help! n odd (inl x) (merid a i) = help₂ n x a i
-- -- -- -- --   help! n odd (inr x) b = Cubical.Data.Empty.rec (not-even-and-odd n (odd-suc→even odd) x)

-- -- -- -- --   helper' : sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --           ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 1)))) ((λ i₂ → ∪-alt (suc n) zero even-or-odd (inr tt) b (loop i₂)) ∙ refl)
-- -- -- -- --           ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))) ≡
-- -- -- -- --           flipSquare
-- -- -- -- --             (cong (cong (subber (suc (suc n)) zero))
-- -- -- -- --               (cong (cong (trMap (miner-h (suc (suc (suc n))) 1 (inr x₂) (inr x₁))))
-- -- -- -- --                 (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (suc n)))))))
-- -- -- -- --                   ∙∙ cong (Kn→ΩKn+1 (suc (suc (suc n)))) (λ i₁ → (∪-alt zero (suc n) (inr tt) even-or-odd (loop i₁) b))
-- -- -- -- --                   ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (suc n)))))))))
-- -- -- -- --   helper' = (cong (λ p → sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --           ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 1)))) p
-- -- -- -- --           ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --                    (help! n x₂ even-or-odd b)
-- -- -- -- --           ∙ inst _ _)
-- -- -- -- --          ∙∙ cong flipSquare (inst4 ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --                                  ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 1))))
-- -- -- -- --                                            (transport (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i)
-- -- -- -- --                                                    ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z b) loop))
-- -- -- -- --                                  ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1))))))))))
-- -- -- -- --          ∙∙ cong flipSquare (rUnit _)
-- -- -- -- --          ∙∙ cong flipSquare (λ k → transportRefl refl (~ k)
-- -- -- -- --                                  ∙∙ cong sym (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --                                  ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 1))))
-- -- -- -- --                                            (transport (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i)
-- -- -- -- --                                                    ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z b) loop))
-- -- -- -- --                                  ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1))))))))
-- -- -- -- --                                  ∙∙ transportRefl refl (~ k))
-- -- -- -- --          ∙∙ cong flipSquare
-- -- -- -- --                  ((λ k → (λ i → congMinner' (suc (suc (suc n))) 1 x₂ tt refl (~ k ∧ i))
-- -- -- -- --                       ∙∙ (λ i → congMinner' (suc (suc (suc n))) 1 x₂ tt
-- -- -- -- --                             (λ j → (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))
-- -- -- -- --                                  ∙∙ cong (Kn→ΩKn+1 (suc (suc (n + 1))))
-- -- -- -- --                                            (transport (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i)
-- -- -- -- --                                                    ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) i))
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z b) loop))
-- -- -- -- --                                  ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (suc (n + 1)))))))) i j) (~ k))
-- -- -- -- --                       ∙∙ λ i → congMinner' (suc (suc (suc n))) 1 x₂ tt refl (~ k ∧ ~ i))
-- -- -- -- --          ∙∙ sym (rUnit _)
-- -- -- -- --          ∙∙ λ k i j →
-- -- -- -- --                 transp (λ i → coHomK ((cong suc (+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                    (trMap (miner-h (suc (suc (suc n))) 1 (inr x₂) (inr tt))
-- -- -- -- --                       ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (~ k))))))
-- -- -- -- --                      ∙∙ cong (Kn→ΩKn+1 ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) (~ k)))
-- -- -- -- --                              (transp (λ i → 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) (~ k ∧ i))
-- -- -- -- --                                            ≡ 0ₖ ((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero)) (~ k ∧ i))) k
-- -- -- -- --                                      (cong (λ z → ∪-alt zero (suc n) (inr tt) even-or-odd z b) loop))
-- -- -- -- --                      ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (((+-comm zero (suc (suc (suc n))) ∙ sym (+-suc (suc (suc n)) zero))) (~ k)))))) i j)))
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) north (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) south (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inl x₂) (merid a i) (merid b j) k = helper' k i j
-- -- -- -- --   where

-- -- -- -- --   t-help : (n m : ℕ) (x : _) → transport (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) i))
-- -- -- -- --                           (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) x) ≡ subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (subber n m x)
-- -- -- -- --   t-help n m x = sym (substComposite coHomK (sym (+-suc m (suc n))) (cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) x)
-- -- -- -- --              ∙∙ cong (λ y → subst coHomK y x) (isSetℕ _ _ _ _)
-- -- -- -- --              ∙∙ substComposite coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m))) x

-- -- -- -- --   subst-ₖ : {n m : ℕ} (x : coHomK n) → (p : n ≡ m) → subst coHomK p (-[ n ]ₖ x) ≡ (-ₖ (subst coHomK p x))
-- -- -- -- --   subst-ₖ {n = n} x = J (λ m p → subst coHomK p (-[ n ]ₖ x) ≡ (-ₖ (subst coHomK p x)))
-- -- -- -- --                     λ i → transportRefl (-ₖ (transportRefl x (~ i))) i

-- -- -- -- --   subst2-ₖ : {n m l : ℕ} (x : coHomK n) → (p : n ≡ m) (q : m ≡ l) → subst coHomK q (subst coHomK p (-[ n ]ₖ x)) ≡ (-ₖ subst coHomK q (subst coHomK p x))
-- -- -- -- --   subst2-ₖ x p q = sym (substComposite coHomK p q (-ₖ x)) ∙∙ subst-ₖ x (p ∙ q) ∙∙ cong -ₖ_ (substComposite coHomK p q x)

-- -- -- -- --   helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (∪-alt n m (inr (even-suc→odd x₁)) (inr (even-suc→odd x₂)) a b))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --       ≡
-- -- -- -- --       flipSquare
-- -- -- -- --         (cong (cong (subber (suc n) (suc m)))
-- -- -- -- --               (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inl x₁) (inl x₂))))
-- -- -- -- --                 ((((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (λ i₁ →
-- -- -- -- --             Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- -- -- --             (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --               (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))
-- -- -- -- --              i₁))
-- -- -- -- --          ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))))
-- -- -- -- --   helper' = (λ i → (cong (cong ∣_∣)
-- -- -- -- --        (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (∪-alt-anticomm n m (inr (even-suc→odd x₁)) (inr (even-suc→odd x₂)) a b i))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --          ∙∙ (λ i → (cong (cong ∣_∣)
-- -- -- -- --        (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (subber n m (miner≡minus (suc n) (suc m) (even-suc→odd x₁) (even-suc→odd x₂) (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a) i)))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))) -- subst coHomK (cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
-- -- -- -- --          ∙∙ ((λ i → (cong (cong ∣_∣)
-- -- -- -- --        (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst2-ₖ (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a) (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m))) i)
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))))
-- -- -- -- --          ∙∙ (((λ i → (cong (cong ∣_∣)
-- -- -- -- --        (sym (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1-ₖ (n + suc (suc m)) (subst coHomK (λ i₃ → +-suc n (suc m) (~ i₃))
-- -- -- -- --        (subst coHomK
-- -- -- -- --         (λ i₃ →
-- -- -- -- --            suc
-- -- -- -- --            (((+-suc m n ∙ (λ i₄ → suc (+-comm m n i₄))) ∙
-- -- -- -- --              (λ i₄ → +-suc n m (~ i₄)))
-- -- -- -- --             i₃))
-- -- -- -- --         (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))) i
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))))
-- -- -- -- --          ∙∙ sym (sym-∙∙ (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --                 ((cong (Kn→ΩKn+1 (suc (n + suc (suc m)))) (
-- -- -- -- --                   Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₃ → +-suc n (suc m) (~ i₃))
-- -- -- -- --                     (subst coHomK
-- -- -- -- --                      (λ i₃ →
-- -- -- -- --                         suc
-- -- -- -- --                         (((+-suc m n ∙ (λ i₄ → suc (+-comm m n i₄))) ∙
-- -- -- -- --                           (λ i₄ → +-suc n m (~ i₄)))
-- -- -- -- --                          i₃))
-- -- -- -- --                      (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))))
-- -- -- -- --                 (((cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))))
-- -- -- -- --          ∙∙ inst _ _
-- -- -- -- --          ∙∙ cong flipSquare
-- -- -- -- --                  (cong (λ x → sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --                               ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m)))) (
-- -- -- -- --                                         Kn→ΩKn+1 (n + suc (suc m)) x)
-- -- -- -- --                               ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --                        (sym (t-help _ _ (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))
-- -- -- -- --          ∙∙ cong flipSquare (λ k i₁ i₂ →
-- -- -- -- --             transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
-- -- -- -- --             ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
-- -- -- -- --                      (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
-- -- -- -- --                         (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
-- -- -- -- --                           (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --               (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))))
-- -- -- -- --             ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i₁ i₂))
-- -- -- -- --          ∙∙ cong flipSquare
-- -- -- -- --            (cong (cong (cong (subber (suc n) (suc m))))
-- -- -- -- --              λ k i j → trMap-miner-Left (suc (suc n)) (suc (suc m)) x₁ (inl x₂) (~ k)
-- -- -- -- --                ((((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (λ i₁ →
-- -- -- -- --             Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- -- -- --             (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --               (∪-alt m n (inr (even-suc→odd x₂)) (inr (even-suc→odd x₁)) b a))
-- -- -- -- --              i₁))
-- -- -- -- --          ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))) i j))
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) north (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) south (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inl x₁) (inr x₂) (merid a i) (merid b j) k = helper' k j i
-- -- -- -- --   where
-- -- -- -- --   helper' : (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ≡ cong (cong (subber (suc n) (suc m)))
-- -- -- -- --           (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inl x₁) (inr x₂))))
-- -- -- -- --             (cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
-- -- -- -- --             ∙∙
-- -- -- -- --             cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --                (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                  (subber m n
-- -- -- -- --                   (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))))
-- -- -- -- --             ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))))
-- -- -- -- --   helper' =
-- -- -- -- --        cong (λ x → sym (cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --                  ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                (Kn→ΩKn+1 (n + suc (suc m)) x)
-- -- -- -- --                  ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --            (cong (λ x → subst coHomK x (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)) (isSetℕ _ _ _ _)
-- -- -- -- --          ∙∙ substComposite coHomK (cong suc (+-comm n (suc m) ∙ sym (+-suc m n))) (sym (+-suc m (suc n)) ∙ cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
-- -- -- -- --                                              (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)
-- -- -- -- --          ∙∙ substComposite coHomK (sym (+-suc m (suc n))) (cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))))
-- -- -- -- --                (subber m n (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)))
-- -- -- -- --     ∙∙ (λ k i j →
-- -- -- -- --             transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
-- -- -- -- --             ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
-- -- -- -- --                      (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
-- -- -- -- --                         (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
-- -- -- -- --                           (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                             (subber m n (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b)))))
-- -- -- -- --             ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i j))
-- -- -- -- --     ∙∙ λ k i j
-- -- -- -- --       → subber (suc n) (suc m)
-- -- -- -- --           (trMap-miner-Left (suc (suc n)) (suc (suc m)) x₁ (inr x₂) (~ k)
-- -- -- -- --             ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
-- -- -- -- --             ∙∙
-- -- -- -- --             cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --                (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                  (subber m n
-- -- -- -- --                   (∪-alt n m (inr (even-suc→odd x₁)) (inl (odd-suc→even x₂)) a b))))
-- -- -- -- --             ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))) i j))
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) north (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) south (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inl x₂) (merid a i) (merid b j) k = helper' k i j
-- -- -- -- --   where
-- -- -- -- --   helper' : ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (subber n m
-- -- -- -- --              (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --       ≡
-- -- -- -- --       cong (cong (subber (suc n) (suc m)))
-- -- -- -- --       (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inr x₁) (inl x₂))))
-- -- -- -- --         (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n))))))))
-- -- -- -- --        ∙∙ cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --               (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))
-- -- -- -- --        ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))
-- -- -- -- --   helper' =
-- -- -- -- --        cong (λ x → sym (cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --                  ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                (Kn→ΩKn+1 (n + suc (suc m)) x)
-- -- -- -- --                  ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (n + suc (suc m))))))))
-- -- -- -- --               (sym (substComposite coHomK (cong suc (+-comm m (suc n) ∙ sym (+-suc n m))) (sym (+-suc n (suc m)))
-- -- -- -- --                    (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
-- -- -- -- --             ∙∙ cong (λ x → subst coHomK x (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
-- -- -- -- --                     (isSetℕ _ _ _ _)
-- -- -- -- --             ∙∙ substComposite coHomK (sym (+-suc m (suc n)))
-- -- -- -- --                (cong predℕ ((+-comm (suc m) (2 + n) ∙ (sym (+-suc (suc n) (suc m))))))
-- -- -- -- --                  (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))
-- -- -- -- --     ∙∙ (λ k i j →
-- -- -- -- --             transp (λ i → coHomK ((cong suc (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k)))))))
-- -- -- -- --             ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k)))
-- -- -- -- --                      (Kn→ΩKn+1 ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k))
-- -- -- -- --                         (transp (λ i → coHomK ((cong predℕ (+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m)))) (~ k ∧ i))) k
-- -- -- -- --                           (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                             (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --             ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc m) (2 + n) ∙ sym (+-suc (suc n) (suc m))) (~ k))))))) i j))
-- -- -- -- --     ∙∙ λ k i j
-- -- -- -- --       → subber (suc n) (suc m)
-- -- -- -- --           (trMap-miner-Right (suc (suc n)) (suc (suc m)) (inr x₁) x₂ (~ k)
-- -- -- -- --             ((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
-- -- -- -- --             ∙∙
-- -- -- -- --             cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --                (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                  (∪-alt m n (inr (even-suc→odd x₂)) (inl (odd-suc→even x₁)) b a)))
-- -- -- -- --             ∙∙ cong (cong ∣_∣) ((rCancel (merid (ptSn (suc (m + suc (suc n)))))))) i j))
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) north (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) south (merid a i) = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) north = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) south = refl
-- -- -- -- -- ∪-alt-anticomm (suc n) (suc m) (inr x₁) (inr x₂) (merid a i) (merid b j) k =
-- -- -- -- --   helper' n m a b x₁ x₂ k i j
-- -- -- -- --   where
-- -- -- -- --   helper' : (n m : ℕ) (a : _) (b : _) (x₁ : _) (x₂ : _) → (sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --        ∙∙
-- -- -- -- --        (λ i₁ →
-- -- -- -- --           Kn→ΩKn+1 (suc (n + suc (suc m)))
-- -- -- -- --           (Kn→ΩKn+1 (n + suc (suc m))
-- -- -- -- --            (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂))
-- -- -- -- --             (∪-alt n m (inl (odd-suc→even x₁)) (inl (odd-suc→even x₂)) a b))
-- -- -- -- --            i₁))
-- -- -- -- --        ∙∙
-- -- -- -- --        cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc m)))))))
-- -- -- -- --       ≡
-- -- -- -- --       flipSquare (cong (cong (subber (suc n) (suc m)))
-- -- -- -- --       (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc m)) (inr x₁) (inr x₂))))
-- -- -- -- --        ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n)))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (cong (
-- -- -- -- --             Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --               (∪-alt m n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --          ∙∙
-- -- -- -- --          cong (cong ∣_∣) (rCancel (merid (ptSn (suc (m + suc (suc n))))))))))
-- -- -- -- --   helper' n (suc m) a b x₁ x₂ =
-- -- -- -- --        cong (λ x → ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc (suc m))))))))
-- -- -- -- --          ∙∙ cong (Kn→ΩKn+1 (suc (n + suc (suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc (suc m))) x)
-- -- -- -- --          ∙∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc (n + suc (suc (suc m))))))))))
-- -- -- -- --               (cong (subst coHomK (λ i₂ → +-suc n (suc (suc m)) (~ i₂)))
-- -- -- -- --                 (∪-alt-anticomm n (suc m) (inl (odd-suc→even x₁)) (inl (odd-suc→even x₂)) a b)
-- -- -- -- --             ∙∙ sym (substComposite coHomK (cong suc (+-comm (suc m) (suc n) ∙ sym (+-suc n (suc m)))) (sym (+-suc n (suc (suc m))))
-- -- -- -- --                    (trMap
-- -- -- -- --                      (miner-h (suc n) (suc (suc m)) (inl (odd-suc→even x₁))
-- -- -- -- --                       (inl (odd-suc→even x₂)))
-- -- -- -- --                      (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b
-- -- -- -- --                       a)))
-- -- -- -- --             ∙∙ cong (subst coHomK (cong suc (+-comm (suc m) (suc n) ∙ sym (+-suc n (suc m))) ∙ sym (+-suc n (suc (suc m)))))
-- -- -- -- --                     (funExt⁻ (trMap-miner-Right (suc n) (suc (suc m)) ((inl (odd-suc→even x₁))) (odd-suc→even x₂))
-- -- -- -- --                              (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a)) 
-- -- -- -- --             ∙∙ cong (λ x → subst coHomK x (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a)) (isSetℕ _ _ _ _)
-- -- -- -- --             ∙∙ substComposite
-- -- -- -- --                 coHomK
-- -- -- -- --                 (sym (+-suc (suc m) (suc n))) (cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))))
-- -- -- -- --                 (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))
-- -- -- -- --     ∙∙ (λ k i j →
-- -- -- -- --             transp (λ i → coHomK ((cong suc (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (i ∨ ~ k))) (~ k)
-- -- -- -- --                (((cong (cong ∣_∣) (sym (rCancel (merid (ptSn (((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k)))))))
-- -- -- -- --             ∙∙  cong (Kn→ΩKn+1 ((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))) (~ k)))
-- -- -- -- --                      (Kn→ΩKn+1 ((cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k))
-- -- -- -- --                         (transp (λ i → coHomK ((cong predℕ (+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m))))) (~ k ∧ i))) k
-- -- -- -- --                           (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
-- -- -- -- --                             (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --             ∙∙ (cong (cong ∣_∣) (rCancel (merid (ptSn ((+-comm (suc (suc m)) (2 + n) ∙ sym (+-suc (suc n) (suc (suc m)))) (~ k))))))) i j))
-- -- -- -- --     ∙∙ inst _ _
-- -- -- -- --     ∙∙ (λ k → (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m))))) (rUnit (inst4 ((((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (cong (
-- -- -- -- --             Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 ((suc m) + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
-- -- -- -- --               (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --          ∙∙
-- -- -- -- --          cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))))) k) k))
-- -- -- -- --     ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
-- -- -- -- --             (λ k → (transportRefl (λ _ _ → ∣ north ∣) (~ k)
-- -- -- -- --                  ∙∙ (λ i → sym ((((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (cong (
-- -- -- -- --             Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 ((suc m) + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
-- -- -- -- --               (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --          ∙∙
-- -- -- -- --          cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))) i)))
-- -- -- -- --          ∙∙ transportRefl (λ _ _ → ∣ north ∣) (~ k)))
-- -- -- -- --     ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
-- -- -- -- --             (λ k → (λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ refl (~ k ∧ i))
-- -- -- -- --                  ∙∙ (λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ (((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (cong (
-- -- -- -- --             Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 ((suc m) + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
-- -- -- -- --               (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --          ∙∙
-- -- -- -- --          cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))) i) (~ k))
-- -- -- -- --                  ∙∙ λ i → congMinner' (suc (suc n)) (suc (suc (suc m))) x₁ x₂ refl (~ k ∧ ~ i))
-- -- -- -- --     ∙∙ cong (flipSquare ∘ cong (cong (subber (suc n) (suc (suc m)))))
-- -- -- -- --             (sym (rUnit (cong (cong (trMap (miner-h (suc (suc n)) (suc (suc (suc m))) (inr x₁) (inr x₂))))
-- -- -- -- --        ((sym (cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))
-- -- -- -- --          ∙∙
-- -- -- -- --          (cong (
-- -- -- -- --             Kn→ΩKn+1 (suc ((suc m) + suc (suc n))))
-- -- -- -- --             (Kn→ΩKn+1 ((suc m) + suc (suc n))
-- -- -- -- --              (subst coHomK (λ i₂ → +-suc (suc m) (suc n) (~ i₂))
-- -- -- -- --               (∪-alt (suc m) n (inl (odd-suc→even x₂)) (inl (odd-suc→even x₁)) b a))))
-- -- -- -- --          ∙∙
-- -- -- -- --          cong (cong ∣_∣) (rCancel (merid (ptSn (suc ((suc m) + suc (suc n)))))))))))

-- -- -- -- -- {-
-- -- -- -- -- anti-com : (n m : ℕ) (x : S₊ (suc n)) (y : S₊ (suc m)) → ∪-help n m x y ≡ subber n m (minner n m (∪-help m n y x))
-- -- -- -- -- anti-com zero zero base base = refl
-- -- -- -- -- anti-com zero zero base (loop i) = refl
-- -- -- -- -- anti-com zero zero (loop i) base = refl
-- -- -- -- -- anti-com zero zero (loop i) (loop j) k = test k i j
-- -- -- -- --   where
-- -- -- -- --   p₁ = (λ i j → ∪-help 0 0 (loop i) (loop j))
-- -- -- -- --   p₂ = (λ i j → -ₖ (∪-help 0 0 (loop j) (loop i)))
-- -- -- -- --   lazy : inv' f p₁ ≡ inv' f p₂
-- -- -- -- --   lazy = {!!} -- refl

-- -- -- -- --   test : Path (Path (Path (coHomK 2) (0ₖ _) (0ₖ _)) refl refl) p₁ λ i j → ((subst coHomK (cong suc (+-comm zero 1 ∙ sym (+-suc zero zero))) (-ₖ (∪-help 0 0 (loop j) (loop i)))))
-- -- -- -- --   test = (sym (Iso.rightInv f p₁) ∙ cong (fun f) lazy) ∙∙ Iso.rightInv f p₂ ∙∙ λ z i j → (transportRefl (-ₖ (∪-help 0 0 (loop j) (loop i))) (~ z))

-- -- -- -- -- anti-com zero (suc m) base north = refl
-- -- -- -- -- anti-com zero (suc m) base south = refl
-- -- -- -- -- anti-com zero (suc m) base (merid a i) = refl
-- -- -- -- -- anti-com zero (suc m) (loop i) north = refl
-- -- -- -- -- anti-com zero (suc m) (loop i) south = refl
-- -- -- -- -- anti-com zero (suc m) (loop i) (merid a j) = {!!}
-- -- -- -- -- anti-com (suc n) zero north base = refl
-- -- -- -- -- anti-com (suc n) zero north (loop i) = refl
-- -- -- -- -- anti-com (suc n) zero south base = refl
-- -- -- -- -- anti-com (suc n) zero south (loop i) = refl
-- -- -- -- -- anti-com (suc n) zero (merid a i) base = refl
-- -- -- -- -- anti-com (suc n) zero (merid a i) (loop j) = {!!}
-- -- -- -- -- anti-com (suc n) (suc m) north north = refl
-- -- -- -- -- anti-com (suc n) (suc m) north south = refl
-- -- -- -- -- anti-com (suc n) (suc m) north (merid a i) = refl
-- -- -- -- -- anti-com (suc n) (suc m) south north = refl
-- -- -- -- -- anti-com (suc n) (suc m) south south = refl
-- -- -- -- -- anti-com (suc n) (suc m) south (merid a i) = refl
-- -- -- -- -- anti-com (suc n) (suc m) (merid a i) north = refl
-- -- -- -- -- anti-com (suc n) (suc m) (merid a i) south = refl
-- -- -- -- -- anti-com (suc n) (suc m) (merid a i) (merid b j) k = fstt (~ k) j i
-- -- -- -- --   where
-- -- -- -- --   minnerId : {k : ℕ} (n m : ℕ) (x : coHomK (suc k))
-- -- -- -- --           → (minner (suc n) (suc m) ∘ minner n m) x ≡ x
-- -- -- -- --   minnerId n m = trElim {!!} {!!}
-- -- -- -- --     where
-- -- -- -- --     re : {k : ℕ} (n m : ℕ) → (a : Susp (S₊ (suc k))) →
-- -- -- -- --       (minner (suc n) (suc m) ∘ minner n m) ∣ a ∣ ≡ ∣ a ∣
-- -- -- -- --     re n m = {!!}

-- -- -- -- --   sndd : (n m : ℕ) → (a : _) → subst coHomK (cong predℕ (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))))
-- -- -- -- --                                                                    (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂))
-- -- -- -- --                                                                      (subber m n a)) ≡ subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) a
-- -- -- -- --   sndd n m a = {!!}
-- -- -- -- --             ∙∙ {!!}
-- -- -- -- --             ∙∙ {!!}

-- -- -- -- --   3rd : (n m : ℕ) → (a : _) → subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (minner m n a) ≡ minner m n (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) a)
-- -- -- -- --   3rd n m a i = transp (λ i₂ → coHomK (+-suc n (suc m) (~ i₂ ∧ ~ i))) i (minner m n (transp (λ i₂ → coHomK (+-suc n (suc m) (~ i₂ ∨ ~ i))) (~ i) a))

-- -- -- -- --   4th : (n m : ℕ) → (a : _) → (sym (cong (cong (minner (suc n) (suc m))) (Kn→ΩKn+10ₖ _))
-- -- -- -- --                               ∙∙ cong (cong (minner (suc n) (suc m))) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a)))
-- -- -- -- --                               ∙∙ cong (cong (minner (suc n) (suc m))) (Kn→ΩKn+10ₖ _)) ≡
-- -- -- -- --                                 sym (cong (cong (minner (suc n) (suc m) ∘ minner m n)) (Kn→ΩKn+10ₖ _))
-- -- -- -- --                               ∙∙ cong (cong (minner (suc n) (suc m) ∘ minner m n)) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) a))
-- -- -- -- --                               ∙∙ cong (cong (minner (suc n) (suc m) ∘ minner m n)) (Kn→ΩKn+10ₖ _)
-- -- -- -- --   4th n m a = {!!}
-- -- -- -- --     where
-- -- -- -- --     t : cong (cong (minner (suc n) (suc m))) (cong ((Kn→ΩKn+1 (suc (n + suc (suc m))))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a))) ≡ {!minner m n a!}
-- -- -- -- --     t = (λ _ i j → minner (suc n) (suc m) (Kn→ΩKn+1 (suc (n + suc (suc m))) (Kn→ΩKn+1 (n + suc (suc m)) (minner m n a) i) j))
-- -- -- -- --      ∙∙ {!!}
-- -- -- -- --      ∙∙ {!!}

-- -- -- -- --   -- trElim {!!} {!λ {north → refl ; south → refl ; (merid a i) → refl}!}

-- -- -- -- --   fstt : cong (cong (subber (suc n) (suc m)))
-- -- -- -- --          (cong (cong (minner (suc n) (suc m)))
-- -- -- -- --           (((λ i₁ j₁ →
-- -- -- -- --                ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
-- -- -- -- --             ∙∙
-- -- -- -- --             (λ i₁ →
-- -- -- -- --                Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- -- -- --                (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                 (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))
-- -- -- -- --                 i₁))
-- -- -- -- --             ∙∙
-- -- -- -- --             (λ i₁ j₁ →
-- -- -- -- --                ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣)))) ≡
-- -- -- -- --                flipSquare ((λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)
-- -- -- -- --                                                           ∙∙ (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                                                                  (Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))))
-- -- -- -- --                                                          ∙∙  λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)
-- -- -- -- --   fstt = cong (cong (cong (subber (suc n) (suc m))))
-- -- -- -- --               (cong-∙∙ (cong (minner (suc n) (suc m)))
-- -- -- -- --                 (λ i₁ j₁ →
-- -- -- -- --                ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
-- -- -- -- --                (cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --                  (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                  (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))))
-- -- -- -- --                (λ i₁ j₁ →
-- -- -- -- --                ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣))
-- -- -- -- --       ∙∙ cong-∙∙ (cong (subber (suc n) (suc m)))
-- -- -- -- --                  (cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣))
-- -- -- -- --                  (cong (cong (minner (suc n) (suc m))) (cong (Kn→ΩKn+1 (suc (m + suc (suc n))))
-- -- -- -- --                  (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- --                  (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a)))))
-- -- -- -- --                  (cong (cong (minner (suc n) (suc m))) λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣)
-- -- -- -- --       ∙∙ (λ k → (λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
-- -- -- -- --                                   ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k))) (~ i₁) j₁ ∣)) i j))
-- -- -- -- --               ∙∙ (λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
-- -- -- -- --                                   (minner (suc n) (suc m) (Kn→ΩKn+1 ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k)
-- -- -- -- --                                     (Kn→ΩKn+1 (cong predℕ (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k)
-- -- -- -- --                                       (transp (λ i → coHomK (predℕ ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (k ∧ i)))) (~ k)
-- -- -- -- --                                               (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (anti-com m n b a k))) i) j)))
-- -- -- -- --               ∙∙ λ i j → transp (λ i → coHomK (cong suc (λ j → (+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) (j ∨ k)) i)) k
-- -- -- -- --                                   ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn ((+-comm (suc m) (suc (suc n)) ∙ sym (+-suc (suc n) (suc m))) k))) i₁ j₁ ∣)) i j))
-- -- -- -- --       ∙∙ (λ k → (λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)) i j))
-- -- -- -- --               ∙∙ (λ i j → minner (suc n) (suc m) ((Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                                     (Kn→ΩKn+1 (n + suc (suc m)) (sndd n m (minner m n (∪-help n m a b)) k) i) j))
-- -- -- -- --               ∙∙ λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)) i j))
-- -- -- -- --       ∙∙ (λ k → (λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣)) i j))
-- -- -- -- --               ∙∙ (λ i j → minner (suc n) (suc m) ((Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                                     (Kn→ΩKn+1 (n + suc (suc m)) (3rd n m (∪-help n m a b) k) i) j))
-- -- -- -- --               ∙∙ λ i j → ((cong (cong (minner (suc n) (suc m))) (λ i₁ j₁ →
-- -- -- -- --                                           ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)) i j))
-- -- -- -- --       ∙∙ 4th n m (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))
-- -- -- -- --       ∙∙ sym (cong-∙∙ (cong (minner (suc n) (suc m) ∘ minner m n)) ((λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) (~ i₁) j₁ ∣))
-- -- -- -- --                                                                (cong (Kn→ΩKn+1 (suc (n + suc (suc m))))
-- -- -- -- --                                                                  (Kn→ΩKn+1 (n + suc (suc m)) (subst coHomK (λ i₂ → +-suc n (suc m) (~ i₂)) (∪-help n m a b))))
-- -- -- -- --                                                                λ i₁ j₁ → ∣ rCancel (merid (ptSn (suc (n + suc (suc m))))) i₁ j₁ ∣)
-- -- -- -- --       ∙∙ {!!}
-- -- -- -- --       ∙∙ inst _ _ -}

-- -- -- -- --   {- (λ i → cong (cong (minner (suc n) (suc m)))
-- -- -- -- --               (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (subst coHomK (sym (+-suc m (suc n))) (indhyp n m a b i)))))
-- -- -- -- --                 ∙∙ (λ i → cong (cong (minner (suc n) (suc m)))
-- -- -- -- --               (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (minnerf n m (∪-help n m a b) i))))
-- -- -- -- --                 ∙∙ (λ i → {!!})
-- -- -- -- --                 ∙∙ {!!}
-- -- -- -- --                 ∙∙ {!!} -}

-- -- -- -- -- --   -* = -ₖ2 {m = suc (suc n) + suc (suc m)} (m + suc (suc (m + n · suc (suc m))))
-- -- -- -- -- --   test : (n m : ℕ) → (a : _) (b : _)
-- -- -- -- -- --        → cong (cong (subber (suc n) (suc m)
-- -- -- -- -- --       ∘ (minner (suc n) (suc m))))
-- -- -- -- -- --        (((λ i₁ j₁ →
-- -- -- -- -- --             ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) (~ i₁) j₁ ∣)
-- -- -- -- -- --          ∙∙
-- -- -- -- -- --          (λ i₁ →
-- -- -- -- -- --             Kn→ΩKn+1 (suc (m + suc (suc n)))
-- -- -- -- -- --             (Kn→ΩKn+1 (m + suc (suc n))
-- -- -- -- -- --              (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a))
-- -- -- -- -- --              i₁))
-- -- -- -- -- --          ∙∙
-- -- -- -- -- --          (λ i₁ j₁ →
-- -- -- -- -- --             ∣ rCancel (merid (ptSn (suc (m + suc (suc n))))) i₁ j₁ ∣))) ≡
-- -- -- -- -- --           {!!}
-- -- -- -- -- --   test n m a b = (λ i → cong (cong (subber (suc n) (suc m))) (cong-∙∙ (cong (minner (suc n) (suc m))) (cong (cong ∣_∣) (sym (rCancel (merid (ptSn _))))) (cong (Kn→ΩKn+1 (suc (m + suc (suc n)))) (Kn→ΩKn+1 (m + suc (suc n)) (subst coHomK (λ i₂ → +-suc m (suc n) (~ i₂)) (∪-help m n b a)))) (cong (cong ∣_∣) (rCancel (merid (ptSn _)))) i)) ∙∙ {!!} ∙∙ {!!} ∙∙ {!!} ∙∙ {!!}


-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) north north = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) north south = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) north (merid a i) = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) south north = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) south south = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) south (merid a i) = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) (merid a i) north = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) (merid a i) south = 0ₖ _
-- -- -- -- -- -- -- ∪-help (suc n) (suc m) (merid a i) (merid b j) = ?
-- -- -- -- -- -- --   hcomp (λ k → λ {(j = i0) → {!!}
-- -- -- -- -- -- --                  ; (j = i1) → {!!}
-- -- -- -- -- -- --                  ; (i = i0) → {!!}
-- -- -- -- -- -- --                  ; (i = i1) → {!!}})
-- -- -- -- -- -- --         {!Kn→ΩKn+1 _ (Kn→ΩKn+1 _ (∪-help n m a b) i) j!} -}

-- -- -- -- -- -- -- ⌣ₖ'' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- -- -- -- -- ⌣ₖ'' zero m x = {!!}
-- -- -- -- -- -- -- ⌣ₖ'' (suc n) m x = {!m!}

-- -- -- -- -- -- -- ⌣ₖ' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- -- -- -- -- ⌣ₖ' zero zero x = (λ y → y ℤ∙ x) , refl
-- -- -- -- -- -- -- ⌣ₖ' zero (suc m) x = ^ₖ x , ^ₖ-base x
-- -- -- -- -- -- -- ⌣ₖ' (suc n) zero x =
-- -- -- -- -- -- --   subst (λ m → coHomK-ptd zero →∙ coHomK-ptd (suc m)) (+-comm zero n)
-- -- -- -- -- -- --         ((λ y → ^ₖ y x) , refl)
-- -- -- -- -- -- -- ⌣ₖ' (suc n) (suc m) =
-- -- -- -- -- -- --   trRec (subst (isOfHLevel (3 + n))
-- -- -- -- -- -- --             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (isOfHLevel↑∙ (suc n) m))
-- -- -- -- -- -- --     (k n m)
-- -- -- -- -- -- -- _⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n + m)
-- -- -- -- -- -- -- _⌣ₖ_ {n = n} {m = m} x = fst (⌣ₖ' n m x)

-- -- -- -- -- -- -- open import Cubical.Data.Sum
-- -- -- -- -- -- -- open import Cubical.Data.Empty renaming (rec to ⊥-rec)
-- -- -- -- -- -- -- open import Cubical.Data.Nat.Order

-- -- -- -- -- -- -- -ₖ2 : {m : ℕ} (n : ℕ) → coHomK m → coHomK m
-- -- -- -- -- -- -- -ₖ2 zero x = x
-- -- -- -- -- -- -- -ₖ2 (suc zero) x = -ₖ x
-- -- -- -- -- -- -- -ₖ2 (suc (suc n)) x = -ₖ2 n x

-- -- -- -- -- -- -- ⌣2 : (n m : ℕ) → (n ≤ m) ⊎ (m < n) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- -- -- -- -- ⌣2 zero m (inl x) y = ^ₖ y , ^ₖ-base y
-- -- -- -- -- -- -- ⌣2 (suc n) zero (inl x) = ⊥-rec (help _ _ (snd x))
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   help : (n m : ℕ) → m + suc n ≡ zero → ⊥
-- -- -- -- -- -- --   help n zero p = ⊥-rec (snotz p)
-- -- -- -- -- -- --   help n (suc m) p = ⊥-rec (snotz p)
-- -- -- -- -- -- -- ⌣2 (suc n) (suc m) (inl x) = trRec (subst (isOfHLevel (3 + n))
-- -- -- -- -- -- --             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (isOfHLevel↑∙ (suc n) m))
-- -- -- -- -- -- --     (k n m)
-- -- -- -- -- -- -- ⌣2 zero m (inr x) y = (λ z → fst (⌣2 zero m (inl (m , +-comm m zero)) y) z) , {!!}
-- -- -- -- -- -- -- ⌣2 (suc n) m (inr x) y = {!!}

-- -- -- -- -- -- -- -ₖ'_ : {n : ℕ} → coHomK n → coHomK n
-- -- -- -- -- -- -- -ₖ'_ {n = zero} x = 0 - x
-- -- -- -- -- -- -- -ₖ'_ {n = suc n} = trMap (help n)
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   help : (n : ℕ) → S₊ (suc n) → S₊ (suc n) 
-- -- -- -- -- -- --   help zero base = base
-- -- -- -- -- -- --   help zero (loop i) = loop (~ i)
-- -- -- -- -- -- --   help (suc n) north = south
-- -- -- -- -- -- --   help (suc n) south = north
-- -- -- -- -- -- --   help (suc n) (merid a i) = merid a (~ i)

-- -- -- -- -- -- -- S1case : S₊ 1 → S₊ 1 → coHomK 2
-- -- -- -- -- -- -- S1case base y = ∣ north ∣
-- -- -- -- -- -- -- S1case (loop i) base = ∣ (merid base ∙ sym (merid base)) i ∣
-- -- -- -- -- -- -- S1case (loop i) (loop j) = ∣ (merid (loop j) ∙ sym (merid base)) i ∣

-- -- -- -- -- -- -- lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
-- -- -- -- -- -- --          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
-- -- -- -- -- -- --                    (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- -- -- -- -- -- -- lem = {!!}

-- -- -- -- -- -- -- lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- -- -- -- -- -- -- lem₂ = {!!}

-- -- -- -- -- -- -- lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- -- -- -- -- -- -- lem₃ = {!!}

-- -- -- -- -- -- -- lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- -- -- -- -- -- -- lem₄ = {!!}


-- -- -- -- -- -- -- test :  (cong (λ x → merid x ∙ sym (merid base)) (loop)) ∙ (cong (λ x → merid base ∙ sym (merid x)) loop) ≡ refl
-- -- -- -- -- -- -- test = sym (cong₂Funct (λ x y → merid x ∙ sym (merid y)) loop loop) ∙ help
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   help : cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) loop loop ≡ refl
-- -- -- -- -- -- --   help = (λ i → cong (λ x → merid x ∙ (sym (merid x))) loop) ∙ rUnit _
-- -- -- -- -- -- --               ∙ (λ i → (λ j → rCancel (merid base) (i ∧ j)) ∙∙ (λ j → rCancel (merid (loop j)) i) ∙∙ λ j → rCancel (merid base) (i ∧ ~ j)) ∙ (λ i → (λ j → rCancel (merid base) (j ∧ ~ i)) ∙∙ refl ∙∙ (λ j → rCancel (merid base) (~ j ∧ ~ i))) ∙ sym (rUnit refl)
-- -- -- -- -- -- --   t2 : (x y : S¹) (p : x ≡ y) → cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) p p ≡ {!!}
-- -- -- -- -- -- --   t2 = {!!}

-- -- -- -- -- -- -- wiho : Path (Path (Path (coHomK 2) ∣ north ∣ ∣ north ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣)) (λ j i →  ∣ (merid (loop (~ j)) ∙ sym (merid base)) i ∣) (λ j i →  ∣ (merid base ∙ sym (merid (loop j))) i ∣)
-- -- -- -- -- -- -- wiho = {!!}



-- -- -- -- -- -- -- S1caseeq : (x y : S₊ 1) → S1case x y ≡ (-ₖ S1case y x)
-- -- -- -- -- -- -- S1caseeq base base = refl
-- -- -- -- -- -- -- S1caseeq base (loop i) j = -ₖ (∣ (rCancel (merid base) (~ j) i) ∣)
-- -- -- -- -- -- -- S1caseeq (loop i) base j = ∣ rCancel (merid base) j i ∣
-- -- -- -- -- -- -- S1caseeq (loop i) (loop j) r =
-- -- -- -- -- -- --   hcomp (λ k → λ { (i = i0) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
-- -- -- -- -- -- --                   ; (i = i1) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
-- -- -- -- -- -- --                   ; (j = i0) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
-- -- -- -- -- -- --                   ; (j = i1) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
-- -- -- -- -- -- --                   ; (r = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ k) i
-- -- -- -- -- -- --                   ; (r = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ k) j})
-- -- -- -- -- -- --         (
-- -- -- -- -- -- --     hcomp (λ k → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
-- -- -- -- -- -- --                     ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
-- -- -- -- -- -- --                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
-- -- -- -- -- -- --                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
-- -- -- -- -- -- --                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- -- -- -- -- -- --                     ; (r = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (sym ((cong ∣_∣ (merid base)))) (~ k) j})
-- -- -- -- -- -- --           (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
-- -- -- -- -- -- --                     ; (i = i1) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
-- -- -- -- -- -- --                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
-- -- -- -- -- -- --                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
-- -- -- -- -- -- --                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- -- -- -- -- -- --                     ; (r = i1) → (wiho k i ∙ sym (cong ∣_∣ (merid base ∙ sym (merid base)))) j})
-- -- -- -- -- -- --                  (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
-- -- -- -- -- -- --                                   ; (i = i1) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
-- -- -- -- -- -- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i -- {!rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j!}
-- -- -- -- -- -- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i -- rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ k))) r i -- rCancel (cong ∣_∣ (merid base)) r i
-- -- -- -- -- -- --                                   ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i -- (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
-- -- -- -- -- -- --                                   ; (r = i1) → ((λ j →  ∣ compPath-filler (merid (loop (~ i))) (sym (merid base)) k j  ∣) ∙ λ j →  ∣ compPath-filler (merid base) (sym (merid base)) k (~ j)  ∣) j})
-- -- -- -- -- -- --                         (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
-- -- -- -- -- -- --                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
-- -- -- -- -- -- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
-- -- -- -- -- -- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
-- -- -- -- -- -- --                                   ; (r = i0) → p₂ (~ k) j i 
-- -- -- -- -- -- --                                   ; (r = i1) → p₁ (~ k) j i})
-- -- -- -- -- -- --                                   (p₁≡p₂ (~ r) j i)))))
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     p₁ : (z i j : I) → coHomK 2
-- -- -- -- -- -- --     p₁ z i j = hfill (λ k → λ { (i = i0) → 0ₖ 2
-- -- -- -- -- -- --                                   ; (i = i1) → 0ₖ 2
-- -- -- -- -- -- --                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) k i
-- -- -- -- -- -- --                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) k i })
-- -- -- -- -- -- --                    (inS ((cong ∣_∣ (merid (loop (~ j))) ∙ sym (cong ∣_∣ (merid base))) i)) z

-- -- -- -- -- -- --     p₂ : (z i j : I) → coHomK 2
-- -- -- -- -- -- --     p₂ z i j =
-- -- -- -- -- -- --       hfill (λ k → λ { (j = i0) → 0ₖ 2
-- -- -- -- -- -- --                                   ; (j = i1) → 0ₖ 2
-- -- -- -- -- -- --                                   ; (i = i0) → rCancel (cong ∣_∣ (merid base)) k j -- ∣ rCancel ((merid base)) k j ∣
-- -- -- -- -- -- --                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) k j }) -- ∣ rCancel ((merid base)) k j ∣})
-- -- -- -- -- -- --                    (inS ((cong ∣_∣ (merid (loop i)) ∙ sym (cong ∣_∣ (merid base))) j)) z -- (∣ (merid (loop i) ∙ sym (merid base)) j ∣)


-- -- -- -- -- -- --     open import Cubical.Foundations.Equiv.HalfAdjoint

-- -- -- -- -- -- --     f : Iso Int (typ ((Ω^ 2) (coHomK-ptd 2)))
-- -- -- -- -- -- --     f = compIso (Iso-Kn-ΩKn+1 0) (invIso (congIso (invIso (Iso-Kn-ΩKn+1 1))))

-- -- -- -- -- -- --     -- reduce everything to a computation: f (λ i j → p₁ i1 i j) ≡ f (λ i j → p₂ i1 i j) holds definitionally
-- -- -- -- -- -- --     p₁≡p₂ : Path (typ ((Ω^ 2) (coHomK-ptd 2))) (λ i j → p₁ i1 i j) (λ i j → p₂ i1 i j)
-- -- -- -- -- -- --     p₁≡p₂ = sym (rightInv f (λ i j → p₁ i1 i j)) ∙ rightInv f (λ i j → p₂ i1 i j)


-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- i = i0 ⊢ S1caseeq base (loop j) r
-- -- -- -- -- -- -- i = i1 ⊢ S1caseeq base (loop j) r
-- -- -- -- -- -- -- j = i0 ⊢ S1caseeq (loop i) base r
-- -- -- -- -- -- -- j = i1 ⊢ S1caseeq (loop i) base r
-- -- -- -- -- -- -- r = i0 ⊢ S1case (loop i) (loop j)
-- -- -- -- -- -- -- r = i1 ⊢ -ₖ S1case (loop j) (loop i)
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- mainCommLem : (n : ℕ) → (x y : S₊ (suc n)) → fst (k n n x) ∣ y ∣ ≡ -ₖ2 ((suc n) · (suc n)) (fst (k n n y) ∣ x ∣)
-- -- -- -- -- -- -- mainCommLem zero base base = refl
-- -- -- -- -- -- -- mainCommLem zero (loop i) base j = Kn→ΩKn+10ₖ 1 j i
-- -- -- -- -- -- -- mainCommLem zero base (loop i) j = -ₖ (Kn→ΩKn+10ₖ 1 (~ j) i)
-- -- -- -- -- -- -- mainCommLem zero (loop r) (loop i) j = {!!}
-- -- -- -- -- -- -- mainCommLem (suc n) x y = {!!}

-- -- -- -- -- -- -- -- (λ z → -ₖ2 (n · m) (subst coHomK (+-comm m n) (fst (⌣2 m n (inl ((suc (fst x)) , (sym (+-suc (fst x) m) ∙ snd x))) z) y))) , {!!}


-- -- -- -- -- -- -- -- _⌣_ : ∀ {ℓ} {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n + m) A
-- -- -- -- -- -- -- -- _⌣_ {n = n} {m = m} = sRec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

-- -- -- -- -- -- -- -- -ₖ̂_ : (n : ℕ) {m : ℕ} → coHomK m → coHomK m
-- -- -- -- -- -- -- -- -ₖ̂ zero = λ x → x
-- -- -- -- -- -- -- -- (-ₖ̂ suc n) {m = m} x = -[ m ]ₖ (-ₖ̂ n) x

-- -- -- -- -- -- -- -- sisi : (n m : ℕ) → (x : coHomK n) (y : coHomK m) → (x ⌣ₖ y) ≡ -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (y ⌣ₖ x))
-- -- -- -- -- -- -- -- sisi zero m = {!!}
-- -- -- -- -- -- -- -- sisi (suc n) zero = {!!}
-- -- -- -- -- -- -- -- sisi (suc n) (suc m) = {!!}


-- -- -- -- -- -- -- -- isOfHLevel↑∙zie : (n m : ℕ) → (x : S₊ (suc n)) → (y : S₊ (suc m)) → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) ∣ y ∣ ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) ∣ y ∣) ∣ x ∣))
-- -- -- -- -- -- -- -- isOfHLevel↑∙zie zero zero x y = {!!}
-- -- -- -- -- -- -- -- isOfHLevel↑∙zie zero (suc zero) = {!!}
-- -- -- -- -- -- -- -- isOfHLevel↑∙zie zero (suc (suc m)) x y = {!!}
-- -- -- -- -- -- -- -- isOfHLevel↑∙zie (suc n) m x y = {!!}

-- -- -- -- -- -- -- -- ptpt : (n m : ℕ) → (x : coHomK n) → (-ₖ̂ (n · m)) (subst coHomK (+-comm m n) (fst (⌣ₖ' m n (snd (coHomK-ptd m))) x)) ≡ 0ₖ _
-- -- -- -- -- -- -- -- ptpt zero zero x = transportRefl (x ℤ∙ 0) ∙ ∙-comm x 0
-- -- -- -- -- -- -- -- ptpt zero (suc m) x = {!!}
-- -- -- -- -- -- -- -- ptpt (suc n) zero = {!refl!}
-- -- -- -- -- -- -- -- ptpt (suc zero) (suc zero) _ = refl
-- -- -- -- -- -- -- -- ptpt (suc zero) (suc (suc m)) _ = {!!}
-- -- -- -- -- -- -- -- ptpt (suc (suc n)) (suc m) _ = {!!}

-- -- -- -- -- -- -- -- test : (n m : ℕ) → (x : coHomK (suc n)) → ⌣ₖ' (suc n) (suc m) x ≡ ((λ y → -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) x))) , ptpt (suc n) (suc m) x)
-- -- -- -- -- -- -- -- test n m = trElim {!!} λ a → ΣPathP ((funExt (λ x → funExt⁻  (cong fst (help x)) a)) , {!!})
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   help : (y : coHomK (suc m)) → Path (S₊∙ (suc n) →∙ coHomK-ptd _) ((λ x → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) y) , {!!}) ((λ x → -ₖ̂_ ((suc n) · (suc m)) ((subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) ∣ x ∣)))) , {!!})
-- -- -- -- -- -- -- --   help = {!!}

-- -- -- -- -- -- -- -- cong-ₖ : (n : ℕ) → (p : typ ((Ω^ 2) (coHomK-ptd 1))) → cong (cong (-ₖ_)) p ≡ {!!}
-- -- -- -- -- -- -- -- cong-ₖ = {!!}

-- -- -- -- -- -- -- -- ptCP∞ : (n m : ℕ) (x : coHomK n) → ⌣ₖ' n m x ≡ ((λ y → -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (fst (⌣ₖ' m n y) x))) , ptpt n m x)
-- -- -- -- -- -- -- -- ptCP∞ zero m x = {!!}
-- -- -- -- -- -- -- -- ptCP∞ (suc n) zero x = {!!}
-- -- -- -- -- -- -- -- ptCP∞ (suc n) (suc m) = trElim {!!} {!!}
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   help : (n m : ℕ) → (s : S₊ (suc n)) (l : _) → fst (k n m s) l ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) l) ∣ s ∣))
-- -- -- -- -- -- -- --   help zero zero s =
-- -- -- -- -- -- -- --     trElim (λ _ → isOfHLevelTrunc 4 _ _)
-- -- -- -- -- -- -- --            λ a → {!!} ∙∙ (λ i → -ₖ transportRefl (fst (k 0 0 a) ∣ s ∣) (~ i)) ∙∙ λ i → -ₖ (subst coHomK (rUnit (λ i → 2) i) (fst (k 0 0 a) ∣ s ∣))
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     r : cong (fst (k zero zero base)) (λ i → ∣ loop i ∣) ≡ cong (λ x → -ₖ (fst (k 0 0 x) ∣ base ∣)) loop
-- -- -- -- -- -- -- --     r i = cong (λ x → -ₖ x) (Kn→ΩKn+10ₖ 1 (~ i))

-- -- -- -- -- -- -- --     l : cong (λ x → fst (k 0 0 x) ∣ base ∣) loop ≡ cong (λ x → -ₖ (fst (k zero zero base) x)) (λ i → ∣ loop i ∣)
-- -- -- -- -- -- -- --     l i = Kn→ΩKn+10ₖ 1 i

-- -- -- -- -- -- -- --     r-l : Square {!λ i j → (fst (k 0 0 (loop (i ∧ j)))) (∣ loop j ∣)!} {!cong (λ x → -ₖ fst (k zero zero base) x) (λ i → ∣ loop i ∣)!} l r
-- -- -- -- -- -- -- --     -- PathP (λ i → {!cong (λ x → fst (k 0 0 x) ∣ base ∣) loop!} ≡ {!!}) l r
-- -- -- -- -- -- -- --     r-l = {!!}

-- -- -- -- -- -- -- --     lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
-- -- -- -- -- -- -- --          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
-- -- -- -- -- -- -- --                   (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- -- -- -- -- -- -- --     lem = {!!}

-- -- -- -- -- -- -- --     lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- -- -- -- -- -- -- --     lem₂ = {!!}

-- -- -- -- -- -- -- --     lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- -- -- -- -- -- -- --     lem₃ = {!!}

-- -- -- -- -- -- -- --     lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- -- -- -- -- -- -- --     lem₄ = {!!}

-- -- -- -- -- -- -- --     characFun≡S¹ : ∀ {ℓ} {A : Type ℓ} (f g : S¹ → S¹ → A)
-- -- -- -- -- -- -- --                   → (p : f base base ≡ g base base)
-- -- -- -- -- -- -- --                   → (ppₗ : PathP (λ i → p i ≡ p i) (cong (f base) loop) (cong (g base) loop))
-- -- -- -- -- -- -- --                   → (ppᵣ : PathP (λ i → p i ≡ p i) (cong (λ x → f x base) loop ) (cong (λ x → g x base) loop))
-- -- -- -- -- -- -- --                   → PathP (λ i → ppₗ i ≡ ppᵣ i) {!λ i j → f (loop i) (loop j)!} {!!}
-- -- -- -- -- -- -- --                   → (s t : S¹) → f s t ≡ g s t
-- -- -- -- -- -- -- --     characFun≡S¹ f g p ppl ppr pp base base = p
-- -- -- -- -- -- -- --     characFun≡S¹ f g p ppl ppr pp base (loop i) j = ppl j i
-- -- -- -- -- -- -- --     characFun≡S¹ f g p ppl ppr pp (loop i) base j = ppr j i
-- -- -- -- -- -- -- --     characFun≡S¹ f g p ppl ppr pp (loop i) (loop k) j = {!!}

-- -- -- -- -- -- -- --     help2 : (s a : S¹) → fst (k zero zero s) ∣ a ∣ ≡ -ₖ (fst (k 0 0 a) ∣ s ∣)
-- -- -- -- -- -- -- --     help2 base base = refl
-- -- -- -- -- -- -- --     help2 base (loop i) j = r j i
-- -- -- -- -- -- -- --     help2 (loop i) base j = l j i
-- -- -- -- -- -- -- --     help2 (loop i) (loop j) s =
-- -- -- -- -- -- -- --       hcomp (λ r → λ { (i = i0) → -ₖ lem (merid base) 3 r (~ s) j
-- -- -- -- -- -- -- --                        ; (i = i1) → -ₖ lem (merid base) 3 r (~ s) j
-- -- -- -- -- -- -- --                        ; (j = i0) → lem (merid base) 3 r s i
-- -- -- -- -- -- -- --                        ; (j = i1) → lem (merid base) 3 r s i
-- -- -- -- -- -- -- --                        ; (s = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ r) i
-- -- -- -- -- -- -- --                        ; (s = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ r) j })
-- -- -- -- -- -- -- --             (hcomp (λ r → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- -- -- -- -- -- -- --                        ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- -- -- -- -- -- -- --                        ; (j = i0) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- -- -- -- -- -- -- --                        ; (j = i1) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- -- -- -- -- -- -- --                        ; (s = i0) → (cong ∣_∣ (merid (loop j)) ∙ cong ∣_∣ (sym (merid base))) i
-- -- -- -- -- -- -- --                        ; (s = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (cong ∣_∣ (sym (merid base))) (~ r) j })
-- -- -- -- -- -- -- --                    (hcomp (λ r → λ { (i = i0) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- -- -- -- -- -- -- --                        ; (i = i1) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- -- -- -- -- -- -- --                        ; (j = i0) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- -- -- -- -- -- -- --                        ; (j = i1) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- -- -- -- -- -- -- --                        ; (s = i0) → {!(cong ∣_∣ (λ i → merid (loop j) (i ∨ ~ r)) ∙ cong ∣_∣ (sym (λ i → merid base (i ∨ ~ r)))) i!}
-- -- -- -- -- -- -- --                        ; (s = i1) → (((cong ∣_∣ (lem₃ (merid base) (sym (merid (loop i))) r))) ∙ sym (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r))) j })
-- -- -- -- -- -- -- --                          {!!}))
-- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- --       help3 : {!!}
-- -- -- -- -- -- -- --       help3 = {!!}
-- -- -- -- -- -- -- --   help zero (suc m) s l = {!!}
-- -- -- -- -- -- -- --   help (suc n) m s l = {!i = i0 ⊢ help2 base (loop j) s
-- -- -- -- -- -- -- -- i = i1 ⊢ help2 base (loop j) s
-- -- -- -- -- -- -- -- j = i0 ⊢ help2 (loop i) base s
-- -- -- -- -- -- -- -- j = i1 ⊢ help2 (loop i) base s
-- -- -- -- -- -- -- -- s = i0 ⊢ fst (k zero zero (loop i))
-- -- -- -- -- -- -- --          ∣ loop j ∣
-- -- -- -- -- -- -- -- s = i1 ⊢ -ₖ
-- -- -- -- -- -- -- --          fst (k 0 0 (loop j)) ∣ loop i ∣!}

-- -- -- -- -- -- -- -- -- ⌣ₖ∙ : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ zero zero = λ x → (λ y → y ℤ∙ x) , refl
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ zero (suc zero) x = (trMap λ {base → base ; (loop i) → intLoop x i}) , refl
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ zero (suc (suc m)) = {!!}
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ (suc n) zero = {!!}
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ (suc zero) (suc m) = {!!}
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ (suc (suc n)) (suc zero) = {!!}
-- -- -- -- -- -- -- -- -- ⌣ₖ∙ (suc (suc n)) (suc (suc m)) = trRec {!isOfHLevel↑∙ (suc n) (suc m)!} {!!}
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   helpME! : Susp (S₊ (suc n)) →
-- -- -- -- -- -- -- -- --       coHomK (suc m) → coHomK (suc (suc (n + (suc m))))
-- -- -- -- -- -- -- -- --   helpME! north x = 0ₖ _
-- -- -- -- -- -- -- -- --   helpME! south x = 0ₖ _
-- -- -- -- -- -- -- -- --   helpME! (merid a i) x = Kn→ΩKn+1 (suc (n + suc m)) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i
-- -- -- -- -- -- -- -- --   {- (λ x → Kn→ΩKn+1 _ (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i) , λ j → (cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) m ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i 
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     help : (n m : ℕ) (a : _) → Kn→ΩKn+1 (suc (n + (suc m)))
-- -- -- -- -- -- -- -- --       (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst (snd (coHomK-ptd (suc m)))) ≡ refl
-- -- -- -- -- -- -- -- --     help n m a = cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m))) -}
