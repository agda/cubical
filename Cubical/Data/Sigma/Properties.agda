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
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.Unit.Base

private
  variable
    ℓ : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

mapʳ : (∀ {a} → B a → B' a) → Σ A B → Σ A B'
mapʳ f (a , b) = (a , f b)

mapˡ : {B : Type ℓ} → (f : A → A') → Σ A (λ _ → B) → Σ A' (λ _ → B)
mapˡ f (a , b) = (f a , b)


ΣPathP : ∀ {x y}
  → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y))
  → x ≡ y
ΣPathP eq i = fst eq i , snd eq i

Σ-split-iso : {x y : Σ A B}
  → Iso (Σ[ q ∈ fst x ≡ fst y ] (PathP (λ i → B (q i)) (snd x) (snd y)))
         (x ≡ y)
Iso.fun (Σ-split-iso) = ΣPathP
Iso.inv (Σ-split-iso) eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
Iso.rightInv (Σ-split-iso) x = refl {x = x}
Iso.leftInv (Σ-split-iso) x = refl {x = x}

Σ≃ : {x y : Σ A B}  →
     Σ (fst x ≡ fst y) (λ p → PathP (λ i → B (p i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≃ {A = A} {B = B} {x} {y} = isoToEquiv (Σ-split-iso)

Σ≡ : {a a' : A} {b : B a} {b' : B a'} → (Σ (a ≡ a') (λ q → PathP (λ i → B (q i)) b b')) ≡ ((a , b) ≡ (a' , b'))
Σ≡ = isoToPath Σ-split-iso -- ua Σ≃

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
        ... | (yes q) = yes (transport (ua Σ≃) (refl , q))
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

Σ-ap-iso₁ : ∀ {ℓ} {ℓ'} {A A' : Type ℓ} {B : A' → Type ℓ'}
          → (isom : Iso A A')
          → Iso (Σ A (B ∘ (Iso.fun isom)))
                (Σ A' B)
Iso.fun (Σ-ap-iso₁ isom) x = (Iso.fun isom) (x .fst) , x .snd
Iso.inv (Σ-ap-iso₁ {B = B} isom) x = (Iso.inv isom) (x .fst) , subst B (sym (ε' (x .fst))) (x .snd)
  where
    ε' = fst (vogt isom)
Iso.rightInv (Σ-ap-iso₁ {B = B} isom) (x , y) = ΣPathP (ε' x ,
  transport
    (sym (PathP≡Path (λ j → cong B (ε' x) j) (subst B (sym (ε' x)) y) y))
    (subst B (ε' x) (subst B (sym (ε' x)) y)
      ≡⟨ sym (substComposite B (sym (ε' x)) (ε' x) y) ⟩
    subst B ((sym (ε' x)) ∙ (ε' x)) y
      ≡⟨ (cong (λ a → subst B a y) (lCancel (ε' x))) ⟩
    subst B refl y
      ≡⟨ substRefl {B = B} y ⟩
    y ∎))
  where
    ε' = fst (vogt isom)
Iso.leftInv (Σ-ap-iso₁ {A = A} {B = B} isom@(iso f g ε η)) (x , y) = ΣPathP (η x ,
  transport
    (sym (PathP≡Path (λ j → cong B (cong f (η x)) j) (subst B (sym (ε' (f x))) y) y))
    (subst B (cong f (η x)) (subst B (sym (ε' (f x))) y)
      ≡⟨ sym (substComposite B (sym (ε' (f x))) (cong f (η x)) y) ⟩
    subst B (sym (ε' (f x)) ∙ (cong f (η x))) y
      ≡⟨ cong (λ a → subst B a y) (lem x) ⟩
    subst B (refl) y
      ≡⟨ substRefl {B = B} y ⟩
    y ∎))
  where
    ε' = fst (vogt isom)
    γ = snd (vogt isom)

    lem : (x : A) → sym (ε' (f x)) ∙ cong f (η x) ≡ refl
    lem x = cong (λ a → sym (ε' (f x)) ∙ a) (γ x) ∙ lCancel (ε' (f x))

Σ-ap₁ : (isom : A ≡ A') → Σ A (B ∘ transport isom) ≡ Σ A' B
Σ-ap₁ isom = isoToPath (Σ-ap-iso₁ (pathToIso isom))

Σ-ap-iso₂ : ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')
Iso.fun (Σ-ap-iso₂ isom) (x , y) = x , Iso.fun (isom x) y
Iso.inv (Σ-ap-iso₂ isom) (x , y') = x , Iso.inv (isom x) y'
Iso.rightInv (Σ-ap-iso₂ isom) (x , y) = ΣPathP (refl , Iso.rightInv (isom x) y)
Iso.leftInv (Σ-ap-iso₂ isom) (x , y') = ΣPathP (refl , Iso.leftInv (isom x) y')

Σ-ap₂ : ((x : A) → B x ≡ B' x) → Σ A B ≡ Σ A B'
Σ-ap₂ isom = isoToPath (Σ-ap-iso₂ (pathToIso ∘ isom))

Σ-ap-iso :
  ∀ {ℓ ℓ'} {A A' : Type ℓ}
  → {B : A → Type ℓ'} {B' : A' → Type ℓ'}
  → (isom : Iso A A')
  → ((x : A) → Iso (B x) (B' (Iso.fun isom x)))
  ------------------------
  → Iso (Σ A B) (Σ A' B')
Σ-ap-iso isom isom' = compIso (Σ-ap-iso₂ isom') (Σ-ap-iso₁ isom)

Σ-ap :
  ∀ {ℓ ℓ'} {X X' : Type ℓ} {Y : X → Type ℓ'} {Y' : X' → Type ℓ'}
  → (isom : X ≡ X')
  → ((x : X) → Y x ≡ Y' (transport isom x))
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap isom isom' = isoToPath (Σ-ap-iso (pathToIso isom) (pathToIso ∘ isom'))

Σ-ap' :
  ∀ {ℓ ℓ'} {X X' : Type ℓ} {Y : X → Type ℓ'} {Y' : X' → Type ℓ'}
  → (isom : X ≡ X')
  → (PathP (λ i → isom i → Type ℓ') Y Y')
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap'  {ℓ} {ℓ'} isom isom' = cong₂ (λ (a : Type ℓ) (b : a → Type ℓ') → Σ a λ x → b x) isom isom'
