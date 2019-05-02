{-

Basic theory about h-levels/n-types:

- Basic properties of isContr, isProp and isSet (definitions are in Prelude)

- Hedberg's theorem can be found in Cubical/Relation/Nullary/DecidableEq

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.HLevels where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HAEquiv      using (congEquiv)
open import Cubical.Foundations.Equiv        using (isoToEquiv; isPropIsEquiv; retEq; invEquiv)
open import Cubical.Foundations.Univalence   using (univalence)

open import Cubical.Data.Sigma  using (ΣPathP; sigmaPath→pathSigma; pathSigma≡sigmaPath; _Σ≡T_)
open import Cubical.Data.Nat    using (ℕ; zero; suc; _+_; +-comm)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y : A
    n : ℕ

hProp : Type (ℓ-suc ℓ)
hProp {ℓ} = Σ (Type ℓ) isProp

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc n) A = (x y : A) → isOfHLevel n (x ≡ y)

HLevel : ℕ → Type (ℓ-suc ℓ)
HLevel {ℓ} n = Σ[ A ∈ Type ℓ ] (isOfHLevel n A)

inhProp→isContr : A → isProp A → isContr A
inhProp→isContr x h = x , h x

isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

-- A retract of a contractible type is contractible
retractIsContr
  : ∀ {B : Type ℓ}
  → (f : A → B) (g : B → A)
  → (h : (x : A) → g (f x) ≡ x)
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

isProp→isPropPathP : (∀ a → isProp (B a))
                   → (m : x ≡ y) (g : B x) (h : B y)
                   → isProp (PathP (λ i → B (m i)) g h)
isProp→isPropPathP {B = B} {x = x} isPropB m = J P d m where
  P : ∀ σc → x ≡ σc → _
  P _ m = ∀ g h → isProp (PathP (λ i → B (m i)) g h)
  d : P x refl
  d = isProp→isSet (isPropB x)

isProp→isContrPathP : (∀ a → isProp (B a))
                    → (m : x ≡ y) (g : B x) (h : B y)
                    → isContr (PathP (λ i → B (m i)) g h)
isProp→isContrPathP isPropB m g h =
  inhProp→isContr (isProp→PathP isPropB m g h) (isProp→isPropPathP isPropB m g h)

isProp→isContr≡ : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContr≡ isPropA x y = inhProp→isContr (isPropA x y) (isProp→isSet isPropA x y)

isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContrPath cA = isProp→isContr≡ (isContr→isProp cA)

-- Π preserves propositionality in the following sense:
propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
propPi h f0 f1 i x = h x (f0 x) (f1 x) i

ΣProp≡
  : ((x : A) → isProp (B x)) → {u v : Σ[ a ∈ A ] B a}
  → (p : u .fst ≡ v .fst) → u ≡ v
ΣProp≡ pB {u} {v} p i = (p i) , isProp→PathP pB p (u .snd) (v .snd) i

isPropSigma : isProp A → ((x : A) → isProp (B x)) → isProp (Σ[ x ∈ A ] B x)
isPropSigma pA pB t u = ΣProp≡ pB (pA (t .fst) (u .fst))

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

isSet→isSet' : isSet A → isSet' A
isSet→isSet' {A = A} Aset {x} {y} {z} {w} p q r s =
  J (λ (z : A) (r : x ≡ z) → ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : z ≡ w) → PathP (λ i → Path A (r i) (s i) ) p q) helper r s p q
  where
    helper : ∀ {w : A} (s : y ≡ w) (p : x ≡ y) (q : x ≡ w) → PathP (λ i → Path A x (s i)) p q
    helper {w} s p q = J (λ (w : A) (s : y ≡ w) → ∀ p q → PathP (λ i → Path A x (s i)) p q) (λ p q → Aset x y p q) s p q

isSet'→isSet : isSet' A → isSet A
isSet'→isSet {A = A} Aset' x y p q = Aset' p q refl refl

hLevelSuc : (n : ℕ) (A : Type ℓ) → isOfHLevel n A → isOfHLevel (suc n) A
hLevelSuc 0 A = isContr→isProp
hLevelSuc 1 A = isProp→isSet
hLevelSuc (suc (suc n)) A h a b = hLevelSuc (suc n) (a ≡ b) (h a b)

hLevelLift : (m : ℕ) (hA : isOfHLevel n A) → isOfHLevel (m + n) A
hLevelLift zero hA = hA
hLevelLift {A = A} (suc m) hA = hLevelSuc _ A (hLevelLift m hA)

isPropIsOfHLevel : (n : ℕ) (A : Type ℓ) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 A = isPropIsContr
isPropIsOfHLevel 1 A = isPropIsProp
isPropIsOfHLevel (suc (suc n)) A f g i a b =
  isPropIsOfHLevel (suc n) (a ≡ b) (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet {A = A} = isPropIsOfHLevel 2 A

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

-- H-level for Σ-types

isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x))
  → isOfHLevel n (Σ A B)
isOfHLevelΣ zero h1 h2 =
  let center = (fst h1 , fst (h2 (fst h1))) in
  let p : ∀ x → center ≡ x
      p = λ x → sym (sigmaPath→pathSigma _ _ (sym (snd h1 (fst x)) , sym (snd (h2 (fst h1)) _)))
  in (center , p)
isOfHLevelΣ 1 h1 h2 x y = sigmaPath→pathSigma x y ((h1 _ _) , (h2 _ _ _))
isOfHLevelΣ {B = B} (suc (suc n)) h1 h2 x y =
  let h3 : isOfHLevel (suc n) (x Σ≡T y)
      h3 = isOfHLevelΣ (suc n) (h1 (fst x) (fst y)) λ p → h2 (p i1)
                       (subst B p (snd x)) (snd y)
  in transport (λ i → isOfHLevel (suc n) (pathSigma≡sigmaPath x y (~ i))) h3

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

hLevelRespectEquiv : {A : Type ℓ} {B : Type ℓ'} → (n : ℕ) → A ≃ B → isOfHLevel n A → isOfHLevel n B
hLevelRespectEquiv 0 eq hA =
  ( fst eq (fst hA)
  , λ b → cong (fst eq) (snd hA (eq .snd .equiv-proof b .fst .fst)) ∙ eq .snd .equiv-proof b .fst .snd)
hLevelRespectEquiv 1 eq hA x y i =
  hcomp (λ j → λ { (i = i0) → retEq eq x j ; (i = i1) → retEq eq y j })
        (cong (eq .fst) (hA (invEquiv eq .fst x) (invEquiv eq .fst y)) i)
hLevelRespectEquiv {A = A} {B = B} (suc (suc n)) eq hA x y =
  hLevelRespectEquiv (suc n) (invEquiv (congEquiv (invEquiv eq))) (hA _ _)

hLevel≡ : ∀ n → {A B : Type ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≡ B)
hLevel≡ n hA hB = hLevelRespectEquiv n (invEquiv univalence) (hLevel≃ n hA hB)

hLevelHLevel1 : isProp (HLevel {ℓ = ℓ} 0)
hLevelHLevel1 x y = ΣProp≡ (λ _ → isPropIsContr) ((hLevel≡ 0 (x .snd) (y .snd) .fst))

hLevelHLevelSuc : ∀ n → isOfHLevel (suc (suc n)) (HLevel {ℓ = ℓ} (suc n))
hLevelHLevelSuc n x y = subst (λ e → isOfHLevel (suc n) e) HLevel≡ (hLevel≡ (suc n) (snd x) (snd y))

hProp≡HLevel1 : hProp {ℓ} ≡ HLevel {ℓ} 1
hProp≡HLevel1 {ℓ} = isoToPath (iso intro elim intro-elim elim-intro)
  where
    intro : hProp {ℓ} → HLevel {ℓ} 1
    intro h = fst h , snd h

    elim : HLevel 1 → hProp
    elim h = (fst h) , (snd h)

    intro-elim : ∀ h → intro (elim h) ≡ h
    intro-elim h = ΣProp≡ (λ _ → isPropIsOfHLevel 1 _) refl

    elim-intro : ∀ h → elim (intro h) ≡ h
    elim-intro h = ΣProp≡ (λ _ → isPropIsProp) refl

isSetHProp : isSet (hProp {ℓ = ℓ})
isSetHProp = subst (λ X → isOfHLevel 2 X) (sym hProp≡HLevel1) (hLevelHLevelSuc 0)


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

isOfHLevelLift : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} → isOfHLevel n A → isOfHLevel n (Lift {j = ℓ'} A)
isOfHLevelLift n = retractIsOfHLevel n lower lift λ _ → refl
