{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.Logic where

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude as FP
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration as Fib
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isPropΠ2; isSetΠ; isSetHProp; isOfHLevelΣ; isPropΣ) public
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)

open import Cubical.Relation.Nullary hiding (¬_)

infix 10 ¬_
infixr 8 _⊔_
infixr 8 _⊔′_
infixr 8 _⊓_
infixr 8 _⊓′_
infixr 6 _⇒_
infixr 4 _⇔_
infix 30 _≡ₚ_
infix 30 _≢ₚ_

infix 2 ∃[]-syntax
infix 2 ∃[∶]-syntax

infix 2 ∀[∶]-syntax
infix 2 ∀[]-syntax

infix 2 ⇒∶_⇐∶_
infix 2 ⇐∶_⇒∶_

--------------------------------------------------------------------------------
-- The type hProp of mere propositions
-- the definition hProp is given in Foundations.HLevels
-- hProp ℓ = Σ (Type ℓ) isProp

private
  variable
    ℓ ℓ' ℓ'' : Level
    P Q R : hProp ℓ
    A B C : Type ℓ

[_] : hProp ℓ → Type ℓ
[_] = fst

∥_∥ₚ : Type ℓ → hProp ℓ
∥ A ∥ₚ = ∥ A ∥ , propTruncIsProp

_≡ₚ_ : (x y : A) → hProp _
x ≡ₚ y = ∥ x ≡ y ∥ₚ

hProp≡ : [ P ] ≡ [ Q ] → P ≡ Q
hProp≡ p = Σ≡Prop (\ _ → isPropIsProp) p

--------------------------------------------------------------------------------
-- Logical implication of mere propositions

_⇒_ : (A : hProp ℓ) → (B : hProp ℓ') → hProp _
A ⇒ B = ([ A ] → [ B ]) , isPropΠ λ _ → B .snd

⇔toPath : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
⇔toPath {P = P} {Q = Q} P⇒Q Q⇒P = hProp≡ (isoToPath
  (iso P⇒Q Q⇒P (λ b → Q .snd (P⇒Q (Q⇒P b)) b) λ a → P .snd (Q⇒P (P⇒Q a)) a))

pathTo⇒ : P ≡ Q → [ P ⇒ Q ]
pathTo⇒ p x = subst fst  p x

pathTo⇐ : P ≡ Q → [ Q ⇒ P ]
pathTo⇐ p x = subst fst (sym p) x

substₚ : {x y : A} (B : A → hProp ℓ) → [ x ≡ₚ y ⇒ B x ⇒ B y ]
substₚ {x = x} {y = y} B = PropTrunc.elim (λ _ → isPropΠ λ _ → B y .snd) (subst (fst ∘ B))

--------------------------------------------------------------------------------
-- Mixfix notations for ⇔-toPath
-- see ⊔-identityˡ and ⊔-identityʳ for the difference

⇒∶_⇐∶_ : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
⇒∶_⇐∶_ = ⇔toPath

⇐∶_⇒∶_ : [ Q ⇒ P ] → [ P ⇒ Q ] → P ≡ Q
⇐∶ g ⇒∶ f  = ⇔toPath f g
--------------------------------------------------------------------------------
-- False and True

⊥ : hProp _
⊥ = ⊥.⊥ , λ ()

⊤ : hProp _
⊤ = Unit , (λ _ _ _ → tt)

--------------------------------------------------------------------------------
-- Pseudo-complement of mere propositions

¬_ : hProp ℓ → hProp _
¬ A = ([ A ] → ⊥.⊥) , isPropΠ λ _ → ⊥.isProp⊥

_≢ₚ_ : (x y : A) → hProp _
x ≢ₚ y = ¬ x ≡ₚ y

--------------------------------------------------------------------------------
-- Disjunction of mere propositions

_⊔′_ : Type ℓ → Type ℓ' → Type _
A ⊔′ B = ∥ A ⊎ B ∥

_⊔_ : hProp ℓ → hProp ℓ' → hProp _
P ⊔ Q = ∥ [ P ] ⊎ [ Q ] ∥ₚ

inl : A → A ⊔′ B
inl x = ∣ ⊎.inl x ∣

inr : B → A ⊔′ B
inr x = ∣ ⊎.inr x ∣

⊔-elim : (P : hProp ℓ) (Q : hProp ℓ') (R : [ P ⊔ Q ] → hProp ℓ'')
  → (∀ x → [ R (inl x) ]) → (∀ y → [ R (inr y) ]) → (∀ z → [ R z ])
⊔-elim _ _ R P⇒R Q⇒R = PropTrunc.elim (snd ∘ R) (⊎.elim P⇒R Q⇒R)

--------------------------------------------------------------------------------
-- Conjunction of mere propositions
_⊓′_ : Type ℓ → Type ℓ' → Type _
A ⊓′ B = A × B

_⊓_ : hProp ℓ → hProp ℓ' → hProp _
A ⊓ B = [ A ] ⊓′ [ B ] , isOfHLevelΣ 1 (A .snd) (\ _ → B .snd)

⊓-intro : (P : hProp ℓ) (Q : [ P ] → hProp ℓ') (R : [ P ] → hProp ℓ'')
       → (∀ a → [ Q a ]) → (∀ a → [ R a ]) → (∀ (a : [ P ]) → [ Q a ⊓ R a ] )
⊓-intro _ _ _ = \ f g a → f a , g a

--------------------------------------------------------------------------------
-- Logical bi-implication of mere propositions

_⇔_ : hProp ℓ → hProp ℓ' → hProp _
A ⇔ B = (A ⇒ B) ⊓ (B ⇒ A)

--------------------------------------------------------------------------------
-- Universal Quantifier


∀[∶]-syntax : (A → hProp ℓ) → hProp _
∀[∶]-syntax {A = A} P = (∀ x → [ P x ]) , isPropΠ (snd ∘ P)

∀[]-syntax : (A → hProp ℓ) → hProp _
∀[]-syntax {A = A} P = (∀ x → [ P x ]) , isPropΠ (snd ∘ P)

syntax ∀[∶]-syntax {A = A} (λ a → P) = ∀[ a ∶ A ] P
syntax ∀[]-syntax (λ a → P)          = ∀[ a ] P
--------------------------------------------------------------------------------
-- Existential Quantifier


∃[]-syntax : (A → hProp ℓ) → hProp _
∃[]-syntax {A = A} P = ∥ Σ A (fst ∘ P) ∥ₚ

∃[∶]-syntax : (A → hProp ℓ) → hProp _
∃[∶]-syntax {A = A} P = ∥ Σ A (fst ∘ P) ∥ₚ

syntax ∃[∶]-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P
syntax ∃[]-syntax (λ x → P) = ∃[ x ] P
--------------------------------------------------------------------------------
-- Decidable mere proposition

Decₚ : (P : hProp ℓ) → hProp ℓ
Decₚ P = Dec [ P ] , isPropDec (snd P)

--------------------------------------------------------------------------------
-- Negation commutes with truncation

∥¬A∥≡¬∥A∥ : (A : Type ℓ) → ∥ (A → ⊥.⊥) ∥ₚ ≡ (¬ ∥ A ∥ₚ)
∥¬A∥≡¬∥A∥ _ =
  ⇒∶ (λ ¬A A → PropTrunc.elim (λ _ → ⊥.isProp⊥)
    (PropTrunc.elim (λ _ → isPropΠ λ _ → ⊥.isProp⊥) (λ ¬p p → ¬p p) ¬A) A)
  ⇐∶ λ ¬p → ∣ (λ p → ¬p ∣ p ∣) ∣

--------------------------------------------------------------------------------
-- (hProp, ⊔, ⊥) is a bounded ⊔-semilattice

⊔-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'')
  → P ⊔ (Q ⊔ R) ≡ (P ⊔ Q) ⊔ R
⊔-assoc P Q R =
  ⇒∶ ⊔-elim P (Q ⊔ R) (λ _ → (P ⊔ Q) ⊔ R)
    (inl ∘ inl)
    (⊔-elim Q R (λ _ → (P ⊔ Q) ⊔ R) (inl ∘ inr) inr)

  ⇐∶ assoc2
  where
    assoc2 : (A ⊔′ B) ⊔′ C → A ⊔′ (B ⊔′ C)
    assoc2 ∣ ⊎.inr a ∣              = ∣ ⊎.inr ∣ ⊎.inr a ∣ ∣
    assoc2 ∣ ⊎.inl ∣ ⊎.inr b ∣ ∣  = ∣ ⊎.inr ∣ ⊎.inl b ∣ ∣
    assoc2 ∣ ⊎.inl ∣ ⊎.inl c ∣ ∣  = ∣ ⊎.inl c ∣
    assoc2 ∣ ⊎.inl (squash x y i) ∣ = propTruncIsProp (assoc2 ∣ ⊎.inl x ∣) (assoc2 ∣ ⊎.inl y ∣) i
    assoc2 (squash x y i)             = propTruncIsProp (assoc2 x) (assoc2 y) i

⊔-idem : (P : hProp ℓ) → P ⊔ P ≡ P
⊔-idem P =
  ⇒∶ (⊔-elim P P (\ _ → P) (\ x → x) (\ x → x))
  ⇐∶ inl

⊔-comm : (P : hProp ℓ) (Q : hProp ℓ') → P ⊔ Q ≡ Q ⊔ P
⊔-comm P Q =
  ⇒∶ (⊔-elim P Q (\ _ → (Q ⊔ P)) inr inl)
  ⇐∶ (⊔-elim Q P (\ _ → (P ⊔ Q)) inr inl)

⊔-identityˡ : (P : hProp ℓ) → ⊥ ⊔ P ≡ P
⊔-identityˡ P =
  ⇒∶ (⊔-elim ⊥ P (λ _ → P) (λ ()) (λ x → x))
  ⇐∶ inr

⊔-identityʳ : (P : hProp ℓ) → P ⊔ ⊥ ≡ P
⊔-identityʳ P = ⇔toPath (⊔-elim P ⊥ (λ _ → P) (λ x → x) λ ()) inl

--------------------------------------------------------------------------------
-- (hProp, ⊓, ⊤) is a bounded ⊓-lattice

⊓-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'')
  → P ⊓ Q ⊓ R ≡ (P ⊓ Q) ⊓ R
⊓-assoc _ _ _ =
  ⇒∶ (λ {(x , (y , z)) →  (x , y) , z})
  ⇐∶ (λ {((x , y) , z) → x , (y , z) })

⊓-comm : (P : hProp ℓ) (Q : hProp ℓ') → P ⊓ Q ≡ Q ⊓ P
⊓-comm _ _ = ⇔toPath (\ p → p .snd , p .fst) (\ p → p .snd , p .fst)

⊓-idem : (P : hProp ℓ) → P ⊓ P ≡ P
⊓-idem _ = ⇔toPath fst (λ x → x , x)

⊓-identityˡ : (P : hProp ℓ) → ⊤ ⊓ P ≡ P
⊓-identityˡ _ = ⇔toPath snd λ x → tt , x

⊓-identityʳ : (P : hProp ℓ) → P ⊓ ⊤ ≡ P
⊓-identityʳ _ = ⇔toPath fst λ x → x , tt

--------------------------------------------------------------------------------
-- Distributive laws

⇒-⊓-distrib : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⇒ (Q ⊓ R) ≡ (P ⇒ Q) ⊓ (P ⇒ R)
⇒-⊓-distrib _ _ _ =
  ⇒∶ (λ f → (fst ∘ f) , (snd ∘ f))
  ⇐∶ (λ { (f , g) x → f x , g x})

⊓-⊔-distribˡ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⊓ (Q ⊔ R) ≡ (P ⊓ Q) ⊔ (P ⊓ R)
⊓-⊔-distribˡ P Q R =
  ⇒∶ (λ { (x , a) → ⊔-elim Q R (λ _ → (P ⊓ Q) ⊔ (P ⊓ R))
        (λ y → ∣ ⊎.inl (x , y) ∣ )
        (λ z → ∣ ⊎.inr (x , z) ∣ ) a })

  ⇐∶ ⊔-elim (P ⊓ Q) (P ⊓ R) (λ _ → P ⊓ Q ⊔ R)
       (λ y → fst y , inl (snd y))
       (λ z → fst z , inr (snd z))

⊔-⊓-distribˡ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → P ⊔ (Q ⊓ R) ≡ (P ⊔ Q) ⊓ (P ⊔ R)
⊔-⊓-distribˡ P Q R =
  ⇒∶ ⊔-elim P (Q ⊓ R) (λ _ → (P ⊔ Q) ⊓ (P ⊔ R) )
    (\ x → inl x , inl x) (\ p → inr (p .fst) , inr (p .snd))

  ⇐∶ (λ { (x , y) → ⊔-elim P R (λ _ → P ⊔ Q ⊓ R) inl
      (λ z → ⊔-elim P Q (λ _ → P ⊔ Q ⊓ R) inl (λ y → inr (y , z)) x) y })

⊓-∀-distrib :  (P : A → hProp ℓ) (Q : A → hProp ℓ')
  → (∀[ a ∶ A ] P a) ⊓ (∀[ a ∶ A ] Q a) ≡ (∀[ a ∶ A ] (P a ⊓ Q a))
⊓-∀-distrib P Q =
  ⇒∶ (λ {(p , q) a → p a , q a})
  ⇐∶ λ pq → (fst ∘ pq ) , (snd ∘ pq)

--------------------------------------------------------------------------------
-- Introduce the "powerset" of a type in the style of Escardó's lecture notes:
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#propositionalextensionality

ℙ : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
ℙ {ℓ} X = X → hProp ℓ

_∈_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∈ A = [ A x ]

_⊆_ : {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-isProp : {X : Type ℓ} (A : ℙ X) (x : X) → isProp (x ∈ A)
∈-isProp A x = (A x) .snd

⊆-isProp : {X : Type ℓ} (A B : ℙ X) → isProp (A ⊆ B)
⊆-isProp A B = isPropΠ2 (λ x _ → ∈-isProp B x)

⊆-refl : {X : Type ℓ} (A : ℙ X) → A ⊆ A
⊆-refl A x = idfun (x ∈ A)


⊆-refl-consequence : {X : Type ℓ} (A B : ℙ X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence {X} A B p = subst (λ B → (A ⊆ B)) p (⊆-refl A) , subst (λ A → (B ⊆ A)) (sym p) (⊆-refl B)


⊆-extensionality : {X : Type ℓ} (A B : ℙ X)
                 → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) i x = ⇔toPath {P = (A x)} {Q = (B x)} (φ x) (ψ x) i


powersets-are-sets : {X : Type ℓ} → isSet (ℙ X)
powersets-are-sets {X = X} = isSetΠ (λ _ → isSetHProp)

⊆-extensionalityEquiv : {X : Type ℓ} (A B : ℙ X)
                      → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → powersets-are-sets A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))


-- We show that the powerset is the subtype classifier
-- i.e. ℙ X ≃ Σ[A ∈ Type ℓ] (A ↪ X)
Embedding→Subset : {X : Type ℓ} → Σ[ A ∈ Type ℓ ] (A ↪ X) → ℙ X
Embedding→Subset (_ , f , isPropFiber) x = fiber f x , isPropFiber x

Subset→Embedding : {X : Type ℓ} → ℙ X → Σ[ A ∈ Type ℓ ] (A ↪ X)
Subset→Embedding {X = X} A = D , f , ψ
 where
  D = Σ[ x ∈ X ] x ∈ A

  f : D → X
  f d = d .fst

  ψ : hasPropFibers f
  ψ x ((y , y∈A) , y≡x) ((z , z∈A) , z≡x) = ΣPathP (r , q)
   where
    p : y ≡ z
    p = y≡x ∙ sym z≡x

    r : (y , y∈A) ≡ (z , z∈A)
    r = Σ≡Prop (∈-isProp A) p

    q : PathP (λ i → p i ≡ x) y≡x z≡x
    q i j = hcomp (λ k → λ { (j = i1) → x
                           ; (i = i0) → y≡x j
                           ; (i = i1) → z≡x (~ k ∨ j) })
                  (y≡x (i ∨ j))


Subset→Embedding→Subset : {X : Type ℓ} → section (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Subset→Embedding→Subset _ = funExt λ x → Σ≡Prop (λ _ → FP.isPropIsProp) (ua (Fib.FiberIso.fiberEquiv _ x))

Embedding→Subset→Embedding : {X : Type ℓ} → retract (Embedding→Subset {ℓ} {X}) (Subset→Embedding {ℓ} {X})
Embedding→Subset→Embedding {ℓ = ℓ} {X = X} (A , f , ψ) = cong (Σ-assoc .fst) p
 where
 χ = Subset→Embedding (Embedding→Subset (A , f , ψ)) .snd .snd

 p : (((Σ[ x ∈ X ] fiber f x) , fst) , χ) ≡ ((A , f) , ψ)
 p = Σ≡Prop (λ _ → hasPropFibersIsProp) ((equivToIso (Fib.fibrationEquiv X ℓ)) .Iso.leftInv (A , f))




Subset≃Embedding : {X : Type ℓ} → ℙ X ≃ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≃Embedding = isoToEquiv (iso Subset→Embedding Embedding→Subset Embedding→Subset→Embedding Subset→Embedding→Subset)

Subset≡Embedding : {X : Type ℓ} → ℙ X ≡ (Σ[ A ∈ Type ℓ ] (A ↪ X))
Subset≡Embedding = ua Subset≃Embedding
