{- Basic theory about transport:

- transport is invertible
- transport is an equivalence ([transportEquiv])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

-- Direct definition of transport filler, note that we have to
-- explicitly tell Agda that the type is constant (like in CHM)
transpFill : ∀ {ℓ} {A : Type ℓ}
             (φ : I)
             (A : (i : I) → Type ℓ [ φ ↦ (λ _ → A) ])
             (u0 : outS (A i0))
           → --------------------------------------
             PathP (λ i → outS (A i)) u0 (transp (λ i → outS (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → outS (A (i ∧ j))) (~ i ∨ φ) u0

transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ p = transport (λ i → p (~ i))

subst⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) → B y → B x
subst⁻ B p pa = transport⁻ (λ i → B (p i)) pa

transport-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-fillerExt p i x = transport-filler p x i

transport⁻-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → p i → A) (λ x → x) (transport⁻ p)
transport⁻-fillerExt p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → p i → B) (transport p) (λ x → x)
transport-fillerExt⁻ p = symP (transport⁻-fillerExt (sym p))

transport⁻-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → B → p i) (transport⁻ p) (λ x → x)
transport⁻-fillerExt⁻ p = symP (transport-fillerExt (sym p))


transport⁻-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : B)
                   → PathP (λ i → p (~ i)) x (transport⁻ p x)
transport⁻-filler p x = transport-filler (λ i → p (~ i)) x

transport⁻Transport : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (a : A) →
                          transport⁻ p (transport p a) ≡ a
transport⁻Transport p a j = transport⁻-fillerExt p (~ j) (transport-fillerExt p (~ j) a)

transportTransport⁻ : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (b : B) →
                        transport p (transport⁻ p b) ≡ b
transportTransport⁻ p b j = transport-fillerExt⁻ p j (transport⁻-fillerExt⁻ p j b)

-- Transport is an equivalence
isEquivTransport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} {B = B} p =
  transport (λ i → isEquiv (transport-fillerExt p i)) (idIsEquiv A)

transportEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
transportEquiv p = (transport p , isEquivTransport p)

transpEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → ∀ i → p i ≃ B
transpEquiv P i .fst = transp (λ j → P (i ∨ j)) i
transpEquiv P i .snd
  = transp (λ k → isEquiv (transp (λ j → P (i ∨ (j ∧ k))) (i ∨ ~ k)))
      i (idIsEquiv (P i))

uaTransportη : ∀ {ℓ} {A B : Type ℓ} (P : A ≡ B) → ua (transportEquiv P) ≡ P
uaTransportη P i j
  = Glue (P i1) λ where
      (j = i0) → P i0 , transportEquiv P
      (i = i1) → P j , transpEquiv P j
      (j = i1) → P i1 , idEquiv (P i1)

pathToIso : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → Iso A B
pathToIso x = iso (transport x) (transport⁻ x) (transportTransport⁻ x) (transport⁻Transport x)

isInjectiveTransport : ∀ {ℓ : Level} {A B : Type ℓ} {p q : A ≡ B}
  → transport p ≡ transport q → p ≡ q
isInjectiveTransport {p = p} {q} α i =
  hcomp
    (λ j → λ
      { (i = i0) → secEq univalence p j
      ; (i = i1) → secEq univalence q j
      })
    (invEq univalence ((λ a → α i a) , t i))
  where
  t : PathP (λ i → isEquiv (λ a → α i a)) (pathToEquiv p .snd) (pathToEquiv q .snd)
  t = isProp→PathP (λ i → isPropIsEquiv (λ a → α i a)) _ _

isSet-subst : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
                → (isSet-A : isSet A)
                → ∀ {a : A}
                → (p : a ≡ a) → (x : B a) → subst B p x ≡ x
isSet-subst {B = B} isSet-A p x = subst (λ p′ → subst B p′ x ≡ x) (isSet-A _ _ refl p) (substRefl {B = B} x)

-- substituting along a composite path is equivalent to substituting twice
substComposite : ∀ {ℓ ℓ′} {A : Type ℓ} → (B : A → Type ℓ′)
                 → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                 → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite B p q Bx i =
  transport (cong B (compPath-filler' p q (~ i))) (transport-fillerExt (cong B p) i Bx)

-- substitution commutes with morphisms in slices
substCommSlice : ∀ {ℓ ℓ′} {A : Type ℓ}
                 → (B C : A → Type ℓ′)
                 → (F : ∀ i → B i → C i)
                 → {x y : A} (p : x ≡ y) (u : B x)
                 → subst C p (F x u) ≡ F y (subst B p u)
substCommSlice B C F p Bx i =
  transport-fillerExt⁻ (cong C p) i (F _ (transport-fillerExt (cong B p) i Bx))
