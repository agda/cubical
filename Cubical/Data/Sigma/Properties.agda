{-

Basic properties about Σ-types

- Characterization of equality in Σ-types using transport ([ΣPath≡pathΣ])

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

open Iso

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

Σ-iso : {x y : Σ A B}
  → Iso (Σ[ q ∈ fst x ≡ fst y ] (PathP (λ i → B (q i)) (snd x) (snd y)))
        (x ≡ y)
fun Σ-iso = ΣPathP
inv Σ-iso eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
rightInv Σ-iso x = refl {x = x}
leftInv Σ-iso x = refl {x = x}

Σ≃ : {x y : Σ A B} →
     Σ (fst x ≡ fst y) (λ p → PathP (λ i → B (p i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≃ = isoToEquiv Σ-iso

Σ≡ : {x y : Σ A B} → (Σ (fst x ≡ fst y) (λ q → PathP (λ i → B (q i)) (snd x) (snd y))) ≡ (x ≡ y)
Σ≡ = ua Σ≃

ΣProp≡ : ((x : A) → isProp (B x)) → {u v : Σ A B}
       → (p : u .fst ≡ v .fst) → u ≡ v
ΣProp≡ pB {u} {v} p i = (p i) , isProp→PathP (λ i → pB (p i)) (u .snd) (v .snd) i

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
          → Iso (Σ A (B ∘ (fun isom)))
                (Σ A' B)
fun (Σ-ap-iso₁ isom) x = (fun isom) (x .fst) , x .snd
inv (Σ-ap-iso₁ {B = B} isom) x = (inv isom) (x .fst) , subst B (sym (ε' (x .fst))) (x .snd)
  where
    ε' = isHAEquiv.ret (snd (iso→HAEquiv isom))
rightInv (Σ-ap-iso₁ {B = B} isom) (x , y) = ΣPathP (ε' x ,
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
    ε' = isHAEquiv.ret (snd (iso→HAEquiv isom))
leftInv (Σ-ap-iso₁ {A = A} {B = B} isom@(iso f g ε η)) (x , y) = ΣPathP (η x ,
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
    ε' = isHAEquiv.ret (snd (iso→HAEquiv isom))
    γ = isHAEquiv.com (snd (iso→HAEquiv isom))

    lem : (x : A) → sym (ε' (f x)) ∙ cong f (η x) ≡ refl
    lem x = cong (λ a → sym (ε' (f x)) ∙ a) (γ x) ∙ lCancel (ε' (f x))

Σ-ap₁ : (p : A ≡ A') → Σ A (B ∘ transport p) ≡ Σ A' B
Σ-ap₁ {B = B} p i = Σ (p i) (B ∘ transp (λ j → p (i ∨ j)) i)

Σ-ap-iso₂ : ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')
fun (Σ-ap-iso₂ isom) (x , y) = x , fun (isom x) y
inv (Σ-ap-iso₂ isom) (x , y') = x , inv (isom x) y'
rightInv (Σ-ap-iso₂ isom) (x , y) = ΣPathP (refl , rightInv (isom x) y)
leftInv (Σ-ap-iso₂ isom) (x , y') = ΣPathP (refl , leftInv (isom x) y')

Σ-ap₂ : ((x : A) → B x ≡ B' x) → Σ A B ≡ Σ A B'
Σ-ap₂ {A = A} p i = Σ[ x ∈ A ] (p x i)

Σ-ap-iso :
  ∀ {ℓ ℓ'} {A A' : Type ℓ}
  → {B : A → Type ℓ'} {B' : A' → Type ℓ'}
  → (isom : Iso A A')
  → ((x : A) → Iso (B x) (B' (fun isom x)))
  ------------------------
  → Iso (Σ A B) (Σ A' B')
Σ-ap-iso isom isom' = compIso (Σ-ap-iso₂ isom') (Σ-ap-iso₁ isom)

Σ-ap' :
  ∀ {ℓ ℓ'} {X X' : Type ℓ} {Y : X → Type ℓ'} {Y' : X' → Type ℓ'}
  → (isom : X ≡ X')
  → (PathP (λ i → isom i → Type ℓ') Y Y')
  ----------
  → (Σ X Y)
  ≡ (Σ X' Y')
Σ-ap'  {ℓ} {ℓ'} isom isom' = cong₂ (λ (a : Type ℓ) (b : a → Type ℓ') → Σ a λ x → b x) isom isom'

-- Alternative version for path in Σ-types, as in the HoTT book

ΣPathTransport : (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b =
  Σ (fst a ≡ fst b) (λ p → transport (λ i → B (p i)) (snd a) ≡ snd b)

_Σ≡T_ : (a b : Σ A B) → Type _
a Σ≡T b = ΣPathTransport a b

ΣPath≃pathΣ : (a b : Σ A B) → (a Σ≡T b) ≃ (a ≡ b)
ΣPath≃pathΣ {B = B} a b =
  compEquiv (isoToEquiv (Σ-ap-iso₂ λ p → invIso (equivToIso (PathP≃Path (λ i → B (p i)) _ _)))) Σ≃

ΣPath→pathΣ : (a b : Σ A B) → (a Σ≡T b) → (a ≡ b)
ΣPath→pathΣ a b = ΣPath≃pathΣ a b .fst

pathΣ→ΣPath : (a b : Σ A B) → (a ≡ b) → (a Σ≡T b)
pathΣ→ΣPath a b = invEq (ΣPath≃pathΣ a b)

ΣPath≡pathΣ : (a b : Σ A B) → (a Σ≡T b) ≡ (a ≡ b)
ΣPath≡pathΣ a b = ua (ΣPath≃pathΣ a b)

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
        ΣPath≃pathΣ _ _ .fst (c .snd a , transportTransport⁻ (cong B (c .snd a)) _)}))

-- a special case of the above
ΣUnit : ∀ {ℓ} (A : Unit → Type ℓ) → Σ Unit A ≃ A tt
ΣUnit A = isoToEquiv (iso snd (λ { x → (tt , x) }) (λ _ → refl) (λ _ → refl))

