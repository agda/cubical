{-

Basic properties about Σ-types

- Characterization of equality in Σ-types using transport ([pathSigma≡sigmaPath])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Properties where

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.Unit.Base

private
  variable
    ℓ : Level
    A : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ


ΣPathP : ∀ {x y}
  → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y))
  → x ≡ y
ΣPathP eq i = fst eq i , snd eq i

Σ≡ : {x y : Σ A B}  →
     Σ (fst x ≡ fst y) (λ p → PathP (λ i → B (p i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≡ {A = A} {B = B} {x} {y} = isoToEquiv (iso intro elim intro-elim elim-intro)
  where
    intro = ΣPathP

    elim : x ≡ y → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y ))
    elim eq = (λ i → fst (eq i)) , (λ i → snd (eq i))

    intro-elim : ∀ eq → intro (elim eq) ≡ eq
    intro-elim eq = refl

    elim-intro : ∀ eq → elim (intro eq) ≡ eq
    elim-intro eq = refl

ΣProp≡ : ((x : A) → isProp (B x)) → {u v : Σ A B}
       → (p : u .fst ≡ v .fst) → u ≡ v
ΣProp≡ pB {u} {v} p i = (p i) , isProp→PathP (λ i → pB (p i)) (u .snd) (v .snd) i

-- Alternative version for path in Σ-types, as in the HoTT book

sigmaPathTransport : (a b : Σ A B) → Type _
sigmaPathTransport {B = B} a b =
  Σ (fst a ≡ fst b) (λ p → transport (λ i → B (p i)) (snd a) ≡ snd b)

_Σ≡T_ : (a b : Σ A B) → Type _
a Σ≡T b = sigmaPathTransport a b

-- now we prove that the alternative path space a Σ≡ b is equal to the usual path space a ≡ b

-- forward direction

private
  pathSigma-π1 : {a b : Σ A B} → a ≡ b → fst a ≡ fst b
  pathSigma-π1 p i = fst (p i)

  filler-π2 : {a b : Σ A B} → (p : a ≡ b) → I → (i : I) → B (fst (p i))
  filler-π2 {B = B} {a = a} p i =
    fill (λ i → B (fst (p i)))
         (λ t → λ { (i = i0) → transport-filler (λ j → B (fst (p j))) (snd a) t
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
          (inS (p i , transport-filler (λ j → B (p j)) (snd a) i))

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
         (λ t → λ { (j = i0) → transport-filler (λ t → B (fst (filler-comp a b p t i)))
                                                (snd a) t
                  ; (j = i1) → snd (sigmaPath→pathSigma a b p t)
                  ; (i = i0) → snd (filler-comp a b p t j)
                  ; (i = i1) → filler-π2 (sigmaPath→pathSigma a b p) j t })
         (snd a)

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
        (fst (p j) , transport-filler (λ k → B (fst (p k))) (snd a) j)

pathSigma≡sigmaPath : (a b : Σ A B) → (a ≡ b) ≡ (a Σ≡T b)
pathSigma≡sigmaPath a b =
  isoToPath (iso (pathSigma→sigmaPath a b)
                 (sigmaPath→pathSigma a b)
                 (pathSigma→sigmaPath→pathSigma {a = a})
                 sigmaPath→pathSigma→sigmaPath)

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

Σ-contractFst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (c : isContr A)
  → Σ A B ≃ B (c .fst)
Σ-contractFst {B = B} c =
  isoToEquiv
    (iso
      (λ {(a , b) → subst B (sym (c .snd a)) b})
      (c .fst ,_)
      (λ b →
        cong (λ p → subst B p b) (isProp→isSet (isContr→isProp c) _ _ _ _)
        ∙ transportRefl _)
      (λ {(a , b) →
        sigmaPath→pathSigma _ _ (c .snd a , transportTransport⁻ (cong B (c .snd a)) _)}))

-- a special case of the above
ΣUnit : ∀ {ℓ} (A : Unit → Type ℓ) → Σ Unit A ≃ A tt
ΣUnit A = isoToEquiv (iso snd (λ { x → (tt , x) }) (λ _ → refl) (λ _ → refl))

assocΣ : (Σ[ (a , b) ∈ Σ A B ] C a b) ≃ (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
assocΣ = isoToEquiv (iso (λ { ((x , y) , z) → (x , (y , z)) })
                         (λ { (x , (y , z)) → ((x , y) , z) })
                         (λ _ → refl) (λ _ → refl))

congΣEquiv : (∀ a → B a ≃ B' a) → Σ A B ≃ Σ A B'
congΣEquiv h =
  isoToEquiv (iso (λ { (x , y)   → (x , equivFun (h x) y) })
                  (λ { (x , y)   → (x , invEq    (h x) y) })
                  (λ { (x , y) i → (x , retEq    (h x) y i) })
                  (λ { (x , y) i → (x , secEq    (h x) y i) }))

PiΣ : ((a : A) → Σ[ b ∈ B a ] C a b) ≃ (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
PiΣ = isoToEquiv (iso (λ f → fst ∘ f , snd ∘ f)
                      (λ (f , g) → (λ x → f x , g x))
                      (λ _ → refl) (λ _ → refl))

swapΣEquiv : ∀ {ℓ'} (A : Type ℓ) (B : Type ℓ') → A × B ≃ B × A
swapΣEquiv A B = isoToEquiv (iso (λ x → x .snd , x .fst) (λ z → z .snd , z .fst) (\ _ → refl) (\ _ → refl))
