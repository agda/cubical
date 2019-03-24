{-

Basic properties about Σ-types

- Characterization of equality in Σ-types using transport ([pathSigma≡sigmaPath])
- HLevel of Σ-types ([isOfHLevelΣ])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Properties where

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Nat

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : (a : A) → Set ℓ'


Σ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
     {x y : Σ A B}  →
     Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≡ {A = A} {B = B} {x} {y} = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)) → x ≡ y
    intro eq = λ i → (fst eq i) , (snd eq i)

    elim : x ≡ y → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y ))
    elim eq = (λ i → fst (eq i)) , λ i → snd (eq i)

    intro-elim : ∀ eq → intro (elim eq) ≡ eq
    intro-elim eq = refl

    elim-intro : ∀ eq → elim (intro eq) ≡ eq
    elim-intro eq = refl

ΣProp≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
         {x y : Σ A B}  → (∀ a → isProp (B a)) →
         fst x ≡ fst y → x ≡ y
ΣProp≡ {B = B} {x = x} {y = y} Bprop eq i =
  eq i , toPathP {A = λ i → B (eq i)} {snd x} {snd y} (Bprop _ _ _) i


-- TODO: should be moved
HLevel≡ : ∀ {ℓ} {n} {A B : Set ℓ} {hA : isOfHLevel n A} {hB : isOfHLevel n B} →
          (A ≡ B) ≃ ((A , hA) ≡ (B , hB))
HLevel≡ {n = n} {A = A} {B = B} {hA} {hB} =
 isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro : A ≡ B → (A , hA) ≡ (B , hB)
    intro eq = ΣProp≡ (λ A → isPropIsOfHLevel n _) eq

    elim : (A , hA) ≡ (B , hB) → A ≡ B
    elim = cong fst

    intro-elim : ∀ x → intro (elim x) ≡ x
    intro-elim eq = cong (fst Σ≡) (ΣProp≡ (λ e →
      J (λ B e →
           ∀ k → (x y : PathP (λ i → isOfHLevel n (e i)) hA k) → x ≡ y)
        (λ k → isProp→isSet (isPropIsOfHLevel n _) _ _) e hB) refl)

    elim-intro : ∀ x → elim (intro x) ≡ x
    elim-intro eq = refl



-- Alternative version for path in Σ-types, as in the HoTT book

sigmaPathTransport : (a b : Σ A B) → Set _
sigmaPathTransport {B = B} a b =
  Σ (fst a ≡ fst b) (λ p → transport (λ i → B (p i)) (snd a) ≡ snd b)

_Σ≡T_ : (a b : Σ A B) → Set _
a Σ≡T b = sigmaPathTransport a b

-- now we prove that the alternative path space a Σ≡ b is equal to the usual path space a ≡ b

-- forward direction

private
  pathSigma-π1 : {a b : Σ A B} → a ≡ b → fst a ≡ fst b
  pathSigma-π1 p i = fst (p i)

  filler-π2 : {a b : Σ A B} → (p : a ≡ b) → I → (i : I) → B (fst (p i))
  filler-π2 {B = B} {a = a} p i =
    fill (λ i → B (fst (p i)))
         (λ t → λ { (i = i0) → coe0→i (λ j → B (fst (p j))) t (snd a)
                  ; (i = i1) → snd (p t) })
         (inS (snd a))

  pathSigma-π2 : {a b : Σ A B} → (p : a ≡ b) →
    subst B (pathSigma-π1 p) (snd a) ≡ snd b
  pathSigma-π2 p i = filler-π2 p i i1

pathSigma→sigmaPath : (a b : Σ A B) → a ≡ b → a Σ≡T b
pathSigma→sigmaPath _ _ p = (pathSigma-π1 p , pathSigma-π2 p)

-- backward direction

private
  filler-comp : (a b : Σ A B) → a Σ≡T b → I → I → Σ A B
  filler-comp {B = B} a b (p , q) i =
    hfill (λ t → λ { (i = i0) → a
                   ; (i = i1) → (p i1 , q t) })
          (inS (p i , coe0→i (λ j → B (p j)) i (snd a)))

sigmaPath→pathSigma : (a b : Σ A B) → a Σ≡T b → (a ≡ b)
sigmaPath→pathSigma a b x i = filler-comp a b x i i1

-- first homotopy

private
  homotopy-π1 : (a b : Σ A B) →
    ∀ (x : a Σ≡T b) → pathSigma-π1 (sigmaPath→pathSigma a b x) ≡ fst x
  homotopy-π1 a b x i j = fst (filler-comp a b x j (~ i))

  homotopy-π2 : (a b : Σ A B) → (p : a Σ≡T b) → (i : I) →
             (transport (λ j → B (fst (filler-comp a b p j i))) (snd a) ≡ snd b)
  homotopy-π2 {B = B} a b p i j =
    comp (λ t → B (fst (filler-comp a b p t (i ∨ j))))
         (λ t → λ { (j = i0) → coe0→i (λ t → B (fst (filler-comp a b p t i)))
                                      t (snd a)
                  ; (j = i1) → snd (sigmaPath→pathSigma a b p t)
                  ; (i = i0) → snd (filler-comp a b p t j)
                  ; (i = i1) → filler-π2 (sigmaPath→pathSigma a b p) j t })
         (inS (snd a))

pathSigma→sigmaPath→pathSigma : {a b : Σ A B} →
  ∀ (x : a Σ≡T b) → pathSigma→sigmaPath _ _ (sigmaPath→pathSigma a b x) ≡ x
pathSigma→sigmaPath→pathSigma {a = a} p i =
  (homotopy-π1 a _ p i , homotopy-π2 a _ p (~ i))

-- second homotopy

sigmaPath→pathSigma→sigmaPath : {a b : Σ A B} →
  ∀ (x : a ≡ b) → sigmaPath→pathSigma a b (pathSigma→sigmaPath _ _ x) ≡ x
sigmaPath→pathSigma→sigmaPath {B = B} {a = a} {b = b} p i j =
  hcomp (λ t → λ { (i = i1) → (fst (p j) , filler-π2 p t j)
                 ; (i = i0) → filler-comp a b (pathSigma→sigmaPath _ _ p) j t
                 ; (j = i0) → (fst a , snd a)
                 ; (j = i1) → (fst b , filler-π2 p t i1) })
        (fst (p j) , coe0→i (λ k → B (fst (p k))) j (snd a))

pathSigma≡sigmaPath : (a b : Σ A B) → (a ≡ b) ≡ (a Σ≡T b)
pathSigma≡sigmaPath a b =
  isoToPath (iso (pathSigma→sigmaPath a b)
                 (sigmaPath→pathSigma a b)
                 (pathSigma→sigmaPath→pathSigma {a = a})
                 sigmaPath→pathSigma→sigmaPath)


-- H-level for Σ-types

isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x)) → isOfHLevel n (Σ A B)
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

discreteΣ : Discrete A → ((a : A) → Discrete (B a)) → Discrete (Σ A B)
discreteΣ {B = B} Adis Bdis (a0 , b0) (a1 , b1) = discreteΣ' (Adis a0 a1)
  where
    discreteΣ' : Dec (a0 ≡ a1) → Dec ((a0 , b0) ≡ (a1 , b1))
    discreteΣ' (yes p) = J (λ a1 p → ∀ b1 → Dec ((a0 , b0) ≡ (a1 , b1))) (discreteΣ'') p b1
      where
        discreteΣ'' : (b1 : B a0) → Dec ((a0 , b0) ≡ (a0 , b1))
        discreteΣ'' b1 with Bdis a0 b0 b1
        ... | (yes q) = yes (transport (ua Σ≡) (refl , q))
        ... | (no ¬q) = no (λ r → ¬q (subst (λ X → PathP (λ i → B (X i)) b0 b1) (Discrete→isSet Adis a0 a0 (cong fst r) refl) (cong snd r)))
    discreteΣ' (no ¬p) = no (λ r → ¬p (cong fst r))

-- TODO: could be moved
hLevel≃ : ∀ {ℓ} n → {A B : Set ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≃ B)
hLevel≃ zero {A = A} {B = B} hA hB = A≃B , contr
  where
  A≃B : A ≃ B
  A≃B = isoToEquiv (iso (λ _ → fst hB) (λ _ → fst hA) (snd hB ) (snd hA))

  contr : (y : A ≃ B) → A≃B ≡ y
  contr y = ΣProp≡ isPropIsEquiv (funExt (λ a → snd hB (fst y a)))
hLevel≃ (suc n) hA hB =
  isOfHLevelΣ (suc n) (hLevelPi (suc n) (λ _ → hB))
              (λ a → subst (λ n → isOfHLevel n (isEquiv a)) (+-comm n 1) (hLevelLift n (isPropIsEquiv a)))
