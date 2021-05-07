{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Cup where


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties

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
open import Cubical.Data.Int renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm) hiding (-_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group hiding (Unit ; Int)
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

-ₖ2 : {m : ℕ} (n : ℕ) → coHomK m → coHomK m
-ₖ2 zero x = x
-ₖ2 (suc zero) x = -ₖ x
-ₖ2 (suc (suc n)) x = -ₖ2 n x

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
  (sym (Kn→ΩKn+10ₖ _) ∙∙ cong (Kn→ΩKn+1 _) (sym (∪-help-pt-l n a) ∙∙ cong (λ x → ∪-help n zero a x) loop ∙∙ ∪-help-pt-l n a) ∙∙  Kn→ΩKn+10ₖ _) j i
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
  fst (main n m x) y = fst (∪fst n m y) x -- fst (∪fst n m y) x
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
minner0 {k = zero} (suc zero) (suc (suc m)) = {!minner0 1 m!}
minner0 {k = zero} (suc (suc n)) (suc m) = {!!}
minner0 {k = suc k₁} n m = {!!}

subber-0 : {k : ℕ} (n m : ℕ) → subber n m (minner n m (0ₖ _)) ≡ 0ₖ _
subber-0 = {!!}

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

anti-com zero (suc m) base north = {!!}
anti-com zero (suc m) base south = {!!}
anti-com zero (suc m) base (merid a i) = {!!}
anti-com zero (suc m) (loop i) north = {!!}
anti-com zero (suc m) (loop i) south = {!!}
anti-com zero (suc zero) (loop i) (merid base i₁) = {!!}
anti-com zero (suc zero) (loop i) (merid (loop i₂) i₁) = {!!}
anti-com zero (suc (suc m)) (loop i) (merid a i₁) = {!!}
anti-com (suc n) zero x y = {!!}
anti-com (suc n) (suc m) north north = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) north south = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) north (merid a i) = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) south north = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) south south = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) south (merid a i) = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) (merid a i) north = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) (merid a i) south = sym (subber-0 {k = suc (suc n) + suc (suc m)} (suc n) (suc m))
anti-com (suc n) (suc m) (merid a i) (merid b j) = {!!}
  where
  -* = -ₖ2 {m = suc (suc n) + suc (suc m)} (m + suc (suc (m + n · suc (suc m))))
  test : (n m : ℕ) → (a : _) (b : _) → cong (funExt⁻ ((cong ((∪-help (suc m) (suc n))) (merid b)))) (merid a) ≡ ({!!} ∙∙ cong (funExt⁻ (cong (λ x → {!minner n m !}) (merid b))) (merid a) ∙∙ {!!})
  test = {!)!}


-- {-
-- ∪-help (suc n) (suc m) north north = 0ₖ _
-- ∪-help (suc n) (suc m) north south = 0ₖ _
-- ∪-help (suc n) (suc m) north (merid a i) = 0ₖ _
-- ∪-help (suc n) (suc m) south north = 0ₖ _
-- ∪-help (suc n) (suc m) south south = 0ₖ _
-- ∪-help (suc n) (suc m) south (merid a i) = 0ₖ _
-- ∪-help (suc n) (suc m) (merid a i) north = 0ₖ _
-- ∪-help (suc n) (suc m) (merid a i) south = 0ₖ _
-- ∪-help (suc n) (suc m) (merid a i) (merid b j) = ?
--   hcomp (λ k → λ {(j = i0) → {!!}
--                  ; (j = i1) → {!!}
--                  ; (i = i0) → {!!}
--                  ; (i = i1) → {!!}})
--         {!Kn→ΩKn+1 _ (Kn→ΩKn+1 _ (∪-help n m a b) i) j!} -}

-- ⌣ₖ'' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- ⌣ₖ'' zero m x = {!!}
-- ⌣ₖ'' (suc n) m x = {!m!}

-- ⌣ₖ' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- ⌣ₖ' zero zero x = (λ y → y ℤ∙ x) , refl
-- ⌣ₖ' zero (suc m) x = ^ₖ x , ^ₖ-base x
-- ⌣ₖ' (suc n) zero x =
--   subst (λ m → coHomK-ptd zero →∙ coHomK-ptd (suc m)) (+-comm zero n)
--         ((λ y → ^ₖ y x) , refl)
-- ⌣ₖ' (suc n) (suc m) =
--   trRec (subst (isOfHLevel (3 + n))
--             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (wow (suc n) m))
--     (k n m)
-- _⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n + m)
-- _⌣ₖ_ {n = n} {m = m} x = fst (⌣ₖ' n m x)

-- open import Cubical.Data.Sum
-- open import Cubical.Data.Empty renaming (rec to ⊥-rec)
-- open import Cubical.Data.Nat.Order

-- -ₖ2 : {m : ℕ} (n : ℕ) → coHomK m → coHomK m
-- -ₖ2 zero x = x
-- -ₖ2 (suc zero) x = -ₖ x
-- -ₖ2 (suc (suc n)) x = -ₖ2 n x

-- ⌣2 : (n m : ℕ) → (n ≤ m) ⊎ (m < n) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- ⌣2 zero m (inl x) y = ^ₖ y , ^ₖ-base y
-- ⌣2 (suc n) zero (inl x) = ⊥-rec (help _ _ (snd x))
--   where
--   help : (n m : ℕ) → m + suc n ≡ zero → ⊥
--   help n zero p = ⊥-rec (snotz p)
--   help n (suc m) p = ⊥-rec (snotz p)
-- ⌣2 (suc n) (suc m) (inl x) = trRec (subst (isOfHLevel (3 + n))
--             (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (wow (suc n) m))
--     (k n m)
-- ⌣2 zero m (inr x) y = (λ z → fst (⌣2 zero m (inl (m , +-comm m zero)) y) z) , {!!}
-- ⌣2 (suc n) m (inr x) y = {!!}

-- -ₖ'_ : {n : ℕ} → coHomK n → coHomK n
-- -ₖ'_ {n = zero} x = 0 - x
-- -ₖ'_ {n = suc n} = trMap (help n)
--   where
--   help : (n : ℕ) → S₊ (suc n) → S₊ (suc n) 
--   help zero base = base
--   help zero (loop i) = loop (~ i)
--   help (suc n) north = south
--   help (suc n) south = north
--   help (suc n) (merid a i) = merid a (~ i)

-- S1case : S₊ 1 → S₊ 1 → coHomK 2
-- S1case base y = ∣ north ∣
-- S1case (loop i) base = ∣ (merid base ∙ sym (merid base)) i ∣
-- S1case (loop i) (loop j) = ∣ (merid (loop j) ∙ sym (merid base)) i ∣

-- lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
--          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
--                    (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- lem = {!!}

-- lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- lem₂ = {!!}

-- lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- lem₃ = {!!}

-- lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- lem₄ = {!!}


-- test :  (cong (λ x → merid x ∙ sym (merid base)) (loop)) ∙ (cong (λ x → merid base ∙ sym (merid x)) loop) ≡ refl
-- test = sym (cong₂Funct (λ x y → merid x ∙ sym (merid y)) loop loop) ∙ help
--   where
--   help : cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) loop loop ≡ refl
--   help = (λ i → cong (λ x → merid x ∙ (sym (merid x))) loop) ∙ rUnit _
--               ∙ (λ i → (λ j → rCancel (merid base) (i ∧ j)) ∙∙ (λ j → rCancel (merid (loop j)) i) ∙∙ λ j → rCancel (merid base) (i ∧ ~ j)) ∙ (λ i → (λ j → rCancel (merid base) (j ∧ ~ i)) ∙∙ refl ∙∙ (λ j → rCancel (merid base) (~ j ∧ ~ i))) ∙ sym (rUnit refl)
--   t2 : (x y : S¹) (p : x ≡ y) → cong₂ (λ x y → merid x ∙ (λ i → merid y (~ i))) p p ≡ {!!}
--   t2 = {!!}

-- wiho : Path (Path (Path (coHomK 2) ∣ north ∣ ∣ north ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣) (λ i → ∣ (merid base ∙ sym (merid base)) i ∣)) (λ j i →  ∣ (merid (loop (~ j)) ∙ sym (merid base)) i ∣) (λ j i →  ∣ (merid base ∙ sym (merid (loop j))) i ∣)
-- wiho = {!!}



-- S1caseeq : (x y : S₊ 1) → S1case x y ≡ (-ₖ S1case y x)
-- S1caseeq base base = refl
-- S1caseeq base (loop i) j = -ₖ (∣ (rCancel (merid base) (~ j) i) ∣)
-- S1caseeq (loop i) base j = ∣ rCancel (merid base) j i ∣
-- S1caseeq (loop i) (loop j) r =
--   hcomp (λ k → λ { (i = i0) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
--                   ; (i = i1) → -ₖ lem (merid base) 3 k (~ r) j -- -ₖ (∣ (rCancel (merid base) (~ r) j) ∣)
--                   ; (j = i0) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
--                   ; (j = i1) → lem (merid base) 3 k r i -- ∣ (rCancel (merid base) r i) ∣
--                   ; (r = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ k) i
--                   ; (r = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ k) j})
--         (
--     hcomp (λ k → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
--                     ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ k) (~ r) j
--                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
--                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
--                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
--                     ; (r = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (sym ((cong ∣_∣ (merid base)))) (~ k) j})
--           (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
--                     ; (i = i1) → rCancel (cong ∣_∣ (merid base ∙ sym (merid base))) (~ r) j
--                     ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i
--                     ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i
--                     ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
--                     ; (r = i1) → (wiho k i ∙ sym (cong ∣_∣ (merid base ∙ sym (merid base)))) j})
--                  (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
--                                   ; (i = i1) → rCancel (cong ∣_∣ (compPath-filler (merid base) (sym (merid base)) k)) (~ r) j -- rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j
--                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) r i -- {!rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) k)) (~ r) j!}
--                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) r i -- rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ k))) r i -- rCancel (cong ∣_∣ (merid base)) r i
--                                   ; (r = i0) → (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i -- (cong ∣_∣ (merid (loop j)) ∙ sym ((cong ∣_∣ (merid base)))) i
--                                   ; (r = i1) → ((λ j →  ∣ compPath-filler (merid (loop (~ i))) (sym (merid base)) k j  ∣) ∙ λ j →  ∣ compPath-filler (merid base) (sym (merid base)) k (~ j)  ∣) j})
--                         (hcomp (λ k → λ { (i = i0) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
--                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) (~ r ∨ ~ k) j
--                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
--                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) (r ∨ ~ k) i
--                                   ; (r = i0) → p₂ (~ k) j i 
--                                   ; (r = i1) → p₁ (~ k) j i})
--                                   (p₁≡p₂ (~ r) j i)))))
--     where
--     p₁ : (z i j : I) → coHomK 2
--     p₁ z i j = hfill (λ k → λ { (i = i0) → 0ₖ 2
--                                   ; (i = i1) → 0ₖ 2
--                                   ; (j = i0) → rCancel (cong ∣_∣ (merid base)) k i
--                                   ; (j = i1) → rCancel (cong ∣_∣ (merid base)) k i })
--                    (inS ((cong ∣_∣ (merid (loop (~ j))) ∙ sym (cong ∣_∣ (merid base))) i)) z

--     p₂ : (z i j : I) → coHomK 2
--     p₂ z i j =
--       hfill (λ k → λ { (j = i0) → 0ₖ 2
--                                   ; (j = i1) → 0ₖ 2
--                                   ; (i = i0) → rCancel (cong ∣_∣ (merid base)) k j -- ∣ rCancel ((merid base)) k j ∣
--                                   ; (i = i1) → rCancel (cong ∣_∣ (merid base)) k j }) -- ∣ rCancel ((merid base)) k j ∣})
--                    (inS ((cong ∣_∣ (merid (loop i)) ∙ sym (cong ∣_∣ (merid base))) j)) z -- (∣ (merid (loop i) ∙ sym (merid base)) j ∣)


--     open import Cubical.Foundations.Equiv.HalfAdjoint

--     f : Iso Int (typ ((Ω^ 2) (coHomK-ptd 2)))
--     f = compIso (Iso-Kn-ΩKn+1 0) (invIso (congIso (invIso (Iso-Kn-ΩKn+1 1))))

--     -- reduce everything to a computation: f (λ i j → p₁ i1 i j) ≡ f (λ i j → p₂ i1 i j) holds definitionally
--     p₁≡p₂ : Path (typ ((Ω^ 2) (coHomK-ptd 2))) (λ i j → p₁ i1 i j) (λ i j → p₂ i1 i j)
--     p₁≡p₂ = sym (rightInv f (λ i j → p₁ i1 i j)) ∙ rightInv f (λ i j → p₂ i1 i j)


-- {-
-- i = i0 ⊢ S1caseeq base (loop j) r
-- i = i1 ⊢ S1caseeq base (loop j) r
-- j = i0 ⊢ S1caseeq (loop i) base r
-- j = i1 ⊢ S1caseeq (loop i) base r
-- r = i0 ⊢ S1case (loop i) (loop j)
-- r = i1 ⊢ -ₖ S1case (loop j) (loop i)
-- -}

-- mainCommLem : (n : ℕ) → (x y : S₊ (suc n)) → fst (k n n x) ∣ y ∣ ≡ -ₖ2 ((suc n) · (suc n)) (fst (k n n y) ∣ x ∣)
-- mainCommLem zero base base = refl
-- mainCommLem zero (loop i) base j = Kn→ΩKn+10ₖ 1 j i
-- mainCommLem zero base (loop i) j = -ₖ (Kn→ΩKn+10ₖ 1 (~ j) i)
-- mainCommLem zero (loop r) (loop i) j = {!!}
-- mainCommLem (suc n) x y = {!!}

-- -- (λ z → -ₖ2 (n · m) (subst coHomK (+-comm m n) (fst (⌣2 m n (inl ((suc (fst x)) , (sym (+-suc (fst x) m) ∙ snd x))) z) y))) , {!!}


-- -- _⌣_ : ∀ {ℓ} {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n + m) A
-- -- _⌣_ {n = n} {m = m} = sRec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

-- -- -ₖ̂_ : (n : ℕ) {m : ℕ} → coHomK m → coHomK m
-- -- -ₖ̂ zero = λ x → x
-- -- (-ₖ̂ suc n) {m = m} x = -[ m ]ₖ (-ₖ̂ n) x

-- -- sisi : (n m : ℕ) → (x : coHomK n) (y : coHomK m) → (x ⌣ₖ y) ≡ -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (y ⌣ₖ x))
-- -- sisi zero m = {!!}
-- -- sisi (suc n) zero = {!!}
-- -- sisi (suc n) (suc m) = {!!}


-- -- wowzie : (n m : ℕ) → (x : S₊ (suc n)) → (y : S₊ (suc m)) → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) ∣ y ∣ ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) ∣ y ∣) ∣ x ∣))
-- -- wowzie zero zero x y = {!!}
-- -- wowzie zero (suc zero) = {!!}
-- -- wowzie zero (suc (suc m)) x y = {!!}
-- -- wowzie (suc n) m x y = {!!}

-- -- ptpt : (n m : ℕ) → (x : coHomK n) → (-ₖ̂ (n · m)) (subst coHomK (+-comm m n) (fst (⌣ₖ' m n (snd (coHomK-ptd m))) x)) ≡ 0ₖ _
-- -- ptpt zero zero x = transportRefl (x ℤ∙ 0) ∙ ∙-comm x 0
-- -- ptpt zero (suc m) x = {!!}
-- -- ptpt (suc n) zero = {!refl!}
-- -- ptpt (suc zero) (suc zero) _ = refl
-- -- ptpt (suc zero) (suc (suc m)) _ = {!!}
-- -- ptpt (suc (suc n)) (suc m) _ = {!!}

-- -- test : (n m : ℕ) → (x : coHomK (suc n)) → ⌣ₖ' (suc n) (suc m) x ≡ ((λ y → -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) x))) , ptpt (suc n) (suc m) x)
-- -- test n m = trElim {!!} λ a → ΣPathP ((funExt (λ x → funExt⁻  (cong fst (help x)) a)) , {!!})
-- --   where
-- --   help : (y : coHomK (suc m)) → Path (S₊∙ (suc n) →∙ coHomK-ptd _) ((λ x → fst (⌣ₖ' (suc n) (suc m) ∣ x ∣) y) , {!!}) ((λ x → -ₖ̂_ ((suc n) · (suc m)) ((subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) y) ∣ x ∣)))) , {!!})
-- --   help = {!!}

-- -- cong-ₖ : (n : ℕ) → (p : typ ((Ω^ 2) (coHomK-ptd 1))) → cong (cong (-ₖ_)) p ≡ {!!}
-- -- cong-ₖ = {!!}

-- -- ptCP∞ : (n m : ℕ) (x : coHomK n) → ⌣ₖ' n m x ≡ ((λ y → -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (fst (⌣ₖ' m n y) x))) , ptpt n m x)
-- -- ptCP∞ zero m x = {!!}
-- -- ptCP∞ (suc n) zero x = {!!}
-- -- ptCP∞ (suc n) (suc m) = trElim {!!} {!!}
-- --   where
-- --   help : (n m : ℕ) → (s : S₊ (suc n)) (l : _) → fst (k n m s) l ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) l) ∣ s ∣))
-- --   help zero zero s =
-- --     trElim (λ _ → isOfHLevelTrunc 4 _ _)
-- --            λ a → {!!} ∙∙ (λ i → -ₖ transportRefl (fst (k 0 0 a) ∣ s ∣) (~ i)) ∙∙ λ i → -ₖ (subst coHomK (rUnit (λ i → 2) i) (fst (k 0 0 a) ∣ s ∣))
-- --     where
-- --     r : cong (fst (k zero zero base)) (λ i → ∣ loop i ∣) ≡ cong (λ x → -ₖ (fst (k 0 0 x) ∣ base ∣)) loop
-- --     r i = cong (λ x → -ₖ x) (Kn→ΩKn+10ₖ 1 (~ i))

-- --     l : cong (λ x → fst (k 0 0 x) ∣ base ∣) loop ≡ cong (λ x → -ₖ (fst (k zero zero base) x)) (λ i → ∣ loop i ∣)
-- --     l i = Kn→ΩKn+10ₖ 1 i

-- --     r-l : Square {!λ i j → (fst (k 0 0 (loop (i ∧ j)))) (∣ loop j ∣)!} {!cong (λ x → -ₖ fst (k zero zero base) x) (λ i → ∣ loop i ∣)!} l r
-- --     -- PathP (λ i → {!cong (λ x → fst (k 0 0 x) ∣ base ∣) loop!} ≡ {!!}) l r
-- --     r-l = {!!}

-- --     lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
-- --          → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
-- --                   (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
-- --     lem = {!!}

-- --     lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
-- --     lem₂ = {!!}

-- --     lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
-- --     lem₃ = {!!}

-- --     lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
-- --     lem₄ = {!!}

-- --     characFun≡S¹ : ∀ {ℓ} {A : Type ℓ} (f g : S¹ → S¹ → A)
-- --                   → (p : f base base ≡ g base base)
-- --                   → (ppₗ : PathP (λ i → p i ≡ p i) (cong (f base) loop) (cong (g base) loop))
-- --                   → (ppᵣ : PathP (λ i → p i ≡ p i) (cong (λ x → f x base) loop ) (cong (λ x → g x base) loop))
-- --                   → PathP (λ i → ppₗ i ≡ ppᵣ i) {!λ i j → f (loop i) (loop j)!} {!!}
-- --                   → (s t : S¹) → f s t ≡ g s t
-- --     characFun≡S¹ f g p ppl ppr pp base base = p
-- --     characFun≡S¹ f g p ppl ppr pp base (loop i) j = ppl j i
-- --     characFun≡S¹ f g p ppl ppr pp (loop i) base j = ppr j i
-- --     characFun≡S¹ f g p ppl ppr pp (loop i) (loop k) j = {!!}

-- --     help2 : (s a : S¹) → fst (k zero zero s) ∣ a ∣ ≡ -ₖ (fst (k 0 0 a) ∣ s ∣)
-- --     help2 base base = refl
-- --     help2 base (loop i) j = r j i
-- --     help2 (loop i) base j = l j i
-- --     help2 (loop i) (loop j) s =
-- --       hcomp (λ r → λ { (i = i0) → -ₖ lem (merid base) 3 r (~ s) j
-- --                        ; (i = i1) → -ₖ lem (merid base) 3 r (~ s) j
-- --                        ; (j = i0) → lem (merid base) 3 r s i
-- --                        ; (j = i1) → lem (merid base) 3 r s i
-- --                        ; (s = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ r) i
-- --                        ; (s = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ r) j })
-- --             (hcomp (λ r → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- --                        ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
-- --                        ; (j = i0) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- --                        ; (j = i1) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
-- --                        ; (s = i0) → (cong ∣_∣ (merid (loop j)) ∙ cong ∣_∣ (sym (merid base))) i
-- --                        ; (s = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (cong ∣_∣ (sym (merid base))) (~ r) j })
-- --                    (hcomp (λ r → λ { (i = i0) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- --                        ; (i = i1) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
-- --                        ; (j = i0) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- --                        ; (j = i1) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
-- --                        ; (s = i0) → {!(cong ∣_∣ (λ i → merid (loop j) (i ∨ ~ r)) ∙ cong ∣_∣ (sym (λ i → merid base (i ∨ ~ r)))) i!}
-- --                        ; (s = i1) → (((cong ∣_∣ (lem₃ (merid base) (sym (merid (loop i))) r))) ∙ sym (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r))) j })
-- --                          {!!}))
-- --       where
-- --       help3 : {!!}
-- --       help3 = {!!}
-- --   help zero (suc m) s l = {!!}
-- --   help (suc n) m s l = {!i = i0 ⊢ help2 base (loop j) s
-- -- i = i1 ⊢ help2 base (loop j) s
-- -- j = i0 ⊢ help2 (loop i) base s
-- -- j = i1 ⊢ help2 (loop i) base s
-- -- s = i0 ⊢ fst (k zero zero (loop i))
-- --          ∣ loop j ∣
-- -- s = i1 ⊢ -ₖ
-- --          fst (k 0 0 (loop j)) ∣ loop i ∣!}

-- -- -- ⌣ₖ∙ : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- -- -- ⌣ₖ∙ zero zero = λ x → (λ y → y ℤ∙ x) , refl
-- -- -- ⌣ₖ∙ zero (suc zero) x = (trMap λ {base → base ; (loop i) → intLoop x i}) , refl
-- -- -- ⌣ₖ∙ zero (suc (suc m)) = {!!}
-- -- -- ⌣ₖ∙ (suc n) zero = {!!}
-- -- -- ⌣ₖ∙ (suc zero) (suc m) = {!!}
-- -- -- ⌣ₖ∙ (suc (suc n)) (suc zero) = {!!}
-- -- -- ⌣ₖ∙ (suc (suc n)) (suc (suc m)) = trRec {!wow (suc n) (suc m)!} {!!}
-- -- --   where
-- -- --   helpME! : Susp (S₊ (suc n)) →
-- -- --       coHomK (suc m) → coHomK (suc (suc (n + (suc m))))
-- -- --   helpME! north x = 0ₖ _
-- -- --   helpME! south x = 0ₖ _
-- -- --   helpME! (merid a i) x = Kn→ΩKn+1 (suc (n + suc m)) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i
-- -- --   {- (λ x → Kn→ΩKn+1 _ (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i) , λ j → (cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) m ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i 
-- -- --     where
-- -- --     help : (n m : ℕ) (a : _) → Kn→ΩKn+1 (suc (n + (suc m)))
-- -- --       (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst (snd (coHomK-ptd (suc m)))) ≡ refl
-- -- --     help n m a = cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m))) -}
