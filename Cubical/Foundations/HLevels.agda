{-

Basic theory about h-levels/n-types:

- Basic properties of isContr, isProp and isSet (definitions are in Prelude)

- Hedberg's theorem can be found in Cubical/Relation/Nullary/DecidableEq

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HAEquiv      using (congEquiv)
open import Cubical.Foundations.Univalence   using (ua; univalence)

open import Cubical.Data.Sigma    using (ΣPathP; sigmaPath→pathSigma; pathSigma≡sigmaPath; _Σ≡T_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y : A
    n : ℕ

-- uses an inlined version of +-comm to avoid cyclic imports from using Cubical.Data.Nat.Properties
private
  +-zero : ∀ m → m + 0 ≡ m
  +-zero zero = refl
  +-zero (suc m) = cong suc (+-zero m)

  +-suc : ∀ m n → m + suc n ≡ suc (m + n)
  +-suc zero    n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm m zero = +-zero m
  +-comm m (suc n) = (+-suc m n) ∙ (cong suc (+-comm m n))

hProp hSet hGroupoid h2Groupoid : ∀ ℓ → Type (ℓ-suc ℓ)
hProp ℓ = Σ (Type ℓ) isProp
hSet ℓ = Σ (Type ℓ) isSet
hGroupoid ℓ = Σ (Type ℓ) isGroupoid
h2Groupoid ℓ = Σ (Type ℓ) is2Groupoid

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

HLevel : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
HLevel ℓ n = Σ[ A ∈ Type ℓ ] (isOfHLevel n A)

inhProp→isContr : A → isProp A → isContr A
inhProp→isContr x h = x , h x

isContrPartial→isContr : ∀ {ℓ} {A : Type ℓ}
                       → (extend : ∀ φ → Partial φ A → A)
                       → (∀ u → u ≡ (extend i1 λ { _ → u}))
                       → isContr A
isContrPartial→isContr {A = A} extend law
  = ex , λ y → law ex ∙ (λ i → Aux.v y i) ∙ sym (law y)
    where ex = extend i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial φ A
            u = λ { (i = i0) → ex ; (i = i1) → y }
            v = extend φ u

-- Dependent h-level over a type

isOfHLevelDep : ℕ → {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isOfHLevelDep 0 {A = A} B = {a : A} → Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a ≡ a') → PathP (λ i → B (p i)) b b')
isOfHLevelDep 1 {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 ≡ a1)  → PathP (λ i → B (p i)) b0 b1
isOfHLevelDep (suc (suc  n)) {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) → isOfHLevelDep (suc n) {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1)

isOfHLevel→isOfHLevelDep : (n : ℕ)
  → {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isOfHLevel n (B a)) → isOfHLevelDep n {A = A} B
isOfHLevel→isOfHLevelDep 0 h {a} =
  (h a .fst , λ b' p → isProp→PathP (λ i → isContr→isProp (h (p i))) (h a .fst) b')
isOfHLevel→isOfHLevelDep 1 h = λ b0 b1 p → isProp→PathP (λ i → h (p i)) b0 b1
isOfHLevel→isOfHLevelDep (suc (suc n)) {A = A} {B} h {a0} {a1} b0 b1 =
  isOfHLevel→isOfHLevelDep (suc n) (λ p → helper a1 p b1)
  where
  helper : (a1 : A) (p : a0 ≡ a1) (b1 : B a1) →
    isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1)
  helper a1 p b1 = J
                     (λ a1 p → ∀ b1 → isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1))
                     (λ _ → h _ _ _) p b1

-- Fillers for cubes from h-level

isSet→isSet' : isSet A → isSet' A
isSet→isSet' {A = A} Aset a₀₋ a₁₋ a₋₀ a₋₁ =
  transport⁻ (PathP≡Path (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋) (Aset _ _ _ _)

isSet'→isSet : isSet' A → isSet A
isSet'→isSet {A = A} Aset' x y p q = Aset' p q refl refl

isGroupoid→isGroupoid' : {A : Type ℓ} → isGroupoid A → isGroupoid' A
isGroupoid→isGroupoid' {A = A} Agpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  transport⁻ (PathP≡Path (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋)
    (isGroupoid→isPropSquare _ _ _ _ _ _)
  where
  isGroupoid→isPropSquare :
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → isProp (Square a₀₋ a₁₋ a₋₀ a₋₁)
  isGroupoid→isPropSquare a₀₋ a₁₋ a₋₀ a₋₁ =
    transport⁻
      (cong isProp (PathP≡Path (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋))
      (Agpd _ _ _ _)

isGroupoid'→isGroupoid : isGroupoid' A → isGroupoid A
isGroupoid'→isGroupoid Agpd' x y p q r s = Agpd' r s refl refl refl refl

-- hlevels are preserved by retracts (and consequently equivalences)

retractIsContr
  : ∀ {B : Type ℓ}
  → (f : A → B) (g : B → A)
  → (h : retract f g)
  → (v : isContr B) → isContr A
retractIsContr f g h (b , p) = (g b , λ x → (cong g (p (f x))) ∙ (h x))

retractIsProp
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isProp B → isProp A
retractIsProp f g h p x y i =
  hcomp
    (λ j → λ
      { (i = i0) → h x j
      ; (i = i1) → h y j})
    (g (p (f x) (f y) i))

retractIsOfHLevel
  : (n : ℕ) {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isOfHLevel n B → isOfHLevel n A
retractIsOfHLevel 0 = retractIsContr
retractIsOfHLevel 1 = retractIsProp
retractIsOfHLevel (suc (suc n)) f g h ofLevel x y =
  retractIsOfHLevel (suc n)
    (cong f)
    (λ q i →
      hcomp
        (λ j → λ
          { (i = i0) → h x j
          ; (i = i1) → h y j})
        (g (q i)))
    (λ p k i →
      hcomp
        (λ j → λ
          { (i = i0) → h x (j ∨ k)
          ; (i = i1) → h y (j ∨ k)
          ; (k = i1) → p i})
        (h (p i) k))
    (ofLevel (f x) (f y))

hLevelRespectEquiv : {A : Type ℓ} {B : Type ℓ'} → (n : ℕ) → A ≃ B → isOfHLevel n A → isOfHLevel n B
hLevelRespectEquiv n eq = retractIsOfHLevel n (invEq eq) (eq .fst) (retEq eq)

-- hlevel of path and dependent path types

isProp→isPropPathP : {A : I → Type ℓ} (isPropA : ∀ i → isProp (A i))
                    (g : A i0) (h : A i1)
                   → isProp (PathP A g h)
isProp→isPropPathP {A = A} isPropA g h =
  transport⁻ (λ i → isProp (PathP≡Path A g h i)) (isProp→isSet (isPropA i1) _ _)

isProp→isContrPathP : {A : I → Type ℓ} (isPropA : ∀ i → isProp (A i))
                    (g : A i0) (h : A i1)
                   → isContr (PathP A g h)
isProp→isContrPathP isPropA g h =
  inhProp→isContr (isProp→PathP isPropA g h) (isProp→isPropPathP isPropA g h)
  -- inhProp→isContr (isProp→PathP (λ i → isPropB (m i)) g h) (isProp→isPropPathP isPropB m g h)

isProp→isContr≡ : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContr≡ isPropA x y = inhProp→isContr (isPropA x y) (isProp→isSet isPropA x y)

isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContrPath cA = isProp→isContr≡ (isContr→isProp cA)

-- h-level of Σ-types

isContrSigma
  : isContr A
  → ((x : A) → isContr (B x))
  → isContr (Σ[ x ∈ A ] B x)
isContrSigma {A = A} {B = B} (a , p) q =
  let h : (x : A) (y : B x) → (q x) .fst ≡ y
      h x y = (q x) .snd y
  in (( a , q a .fst)
     , ( λ x i → p (x .fst) i
       , h (p (x .fst) i) (transp (λ j → B (p (x .fst) (i ∨ ~ j))) i (x .snd)) i))

ΣProp≡
  : ((x : A) → isProp (B x)) → {u v : Σ[ a ∈ A ] B a}
  → (p : u .fst ≡ v .fst) → u ≡ v
ΣProp≡ pB {u} {v} p i = (p i) , isProp→PathP (λ i → pB (p i)) (u .snd) (v .snd) i

isPropSigma : isProp A → ((x : A) → isProp (B x)) → isProp (Σ[ x ∈ A ] B x)
isPropSigma pA pB t u = ΣProp≡ pB (pA (t .fst) (u .fst))

isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x))
  → isOfHLevel n (Σ A B)
isOfHLevelΣ 0 = isContrSigma
isOfHLevelΣ 1 = isPropSigma
isOfHLevelΣ {B = B} (suc (suc n)) h1 h2 x y =
  let h3 : isOfHLevel (suc n) (x Σ≡T y)
      h3 = isOfHLevelΣ (suc n) (h1 (fst x) (fst y)) λ p → h2 (p i1)
                       (subst B p (snd x)) (snd y)
  in transport (λ i → isOfHLevel (suc n) (pathSigma≡sigmaPath x y (~ i))) h3

-- h-level of Π-types

propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
propPi h f0 f1 i x = h x (f0 x) (f1 x) i

hLevelPi
  : ∀ n
  → ((x : A) → isOfHLevel n (B x))
  → isOfHLevel n ((x : A) → B x)
hLevelPi 0 h = (λ x → fst (h x)) , λ f i y → snd (h y) (f y) i
hLevelPi {B = B} 1 h f g i x = (h x) (f x) (g x) i
hLevelPi (suc (suc n)) h f g =
  subst (isOfHLevel (suc n)) funExtPath (hLevelPi (suc n) λ x → h x (f x) (g x))

isSetPi : ((x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetPi Bset = hLevelPi 2 (λ a → Bset a)

-- lower h-levels imply higher h-levels

hLevelSuc : (n : ℕ) (A : Type ℓ) → isOfHLevel n A → isOfHLevel (suc n) A
hLevelSuc 0 A = isContr→isProp
hLevelSuc 1 A = isProp→isSet
hLevelSuc (suc (suc n)) A h a b = hLevelSuc (suc n) (a ≡ b) (h a b)

hLevelPath : (n : ℕ) → isOfHLevel n A → (x y : A) → isOfHLevel n (x ≡ y)
hLevelPath 0 h x y = isContrPath h x y
hLevelPath 1 h x y = hLevelSuc zero _ (isProp→isContr≡ h x y)
hLevelPath (suc (suc n)) h x y = hLevelSuc (suc n) _ (h x y)

hLevelLift : (m : ℕ) (hA : isOfHLevel n A) → isOfHLevel (m + n) A
hLevelLift zero hA = hA
hLevelLift {A = A} (suc m) hA = hLevelSuc _ A (hLevelLift m hA)

-- h-level of isOfHLevel

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsOfHLevel : (n : ℕ) (A : Type ℓ) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 A = isPropIsContr
isPropIsOfHLevel 1 A = isPropIsProp
isPropIsOfHLevel (suc (suc n)) A f g i a b =
  isPropIsOfHLevel (suc n) (a ≡ b) (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet {A = A} = isPropIsOfHLevel 2 A

-- h-level of A ≃ B and A ≡ B

hLevel≃ : ∀ n → {A B : Type ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≃ B)
hLevel≃ zero {A = A} {B = B} hA hB = A≃B , contr
  where
  A≃B : A ≃ B
  A≃B = isoToEquiv (iso (λ _ → fst hB) (λ _ → fst hA) (snd hB ) (snd hA))

  contr : (y : A ≃ B) → A≃B ≡ y
  contr y = ΣProp≡ isPropIsEquiv (funExt (λ a → snd hB (fst y a)))

hLevel≃ (suc n) hA hB =
  isOfHLevelΣ (suc n) (hLevelPi (suc n) (λ _ → hB))
              (λ a → subst (λ n → isOfHLevel n (isEquiv a)) (+-comm n 1) (hLevelLift n (isPropIsEquiv a)))

hLevel≡ : ∀ n → {A B : Type ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≡ B)
hLevel≡ n hA hB = hLevelRespectEquiv n (invEquiv univalence) (hLevel≃ n hA hB)

-- h-level of HLevel

HLevel≡ : ∀ {A B : Type ℓ} {hA : isOfHLevel n A} {hB : isOfHLevel n B} →
          (A ≡ B) ≡ ((A , hA) ≡ (B , hB))
HLevel≡ {n = n} {A = A} {B = B} {hA} {hB} =
 isoToPath (iso intro elim intro-elim elim-intro)
  where
    intro : A ≡ B → (A , hA) ≡ (B , hB)
    intro eq = ΣProp≡ (λ A → isPropIsOfHLevel n _) eq

    elim : (A , hA) ≡ (B , hB) → A ≡ B
    elim = cong fst

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim eq = cong ΣPathP (ΣProp≡ (λ e →
      J (λ B e →
           ∀ k → (x y : PathP (λ i → isOfHLevel n (e i)) hA k) → x ≡ y)
        (λ k → isProp→isSet (isPropIsOfHLevel n _) _ _) e hB) refl)

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = refl

isPropHContr : isProp (HLevel ℓ 0)
isPropHContr x y = ΣProp≡ (λ _ → isPropIsContr) ((hLevel≡ 0 (x .snd) (y .snd) .fst))

hLevelHLevel : ∀ n → isOfHLevel (suc n) (HLevel ℓ n)
hLevelHLevel 0 = isPropHContr
hLevelHLevel (suc n) x y = subst (λ e → isOfHLevel (suc n) e) HLevel≡ (hLevel≡ (suc n) (snd x) (snd y))

isSetHProp : isSet (hProp ℓ)
isSetHProp = hLevelHLevel 1

-- h-level of lifted type

isOfHLevelLift : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} → isOfHLevel n A → isOfHLevel n (Lift {j = ℓ'} A)
isOfHLevelLift n = retractIsOfHLevel n lower lift λ _ → refl
