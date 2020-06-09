{-

Basic properties about Σ-types

- Action of Σ on functions ([map-fst], [map-snd])
- Characterization of equality in Σ-types using dependent paths ([ΣPath{Iso,≃,≡}PathΣ], [Σ≡Prop])
- Proof that discrete types are closed under Σ ([discreteΣ])
- Commutativity and associativity ([swapΣEquiv, Σ-assoc])
- Distributivity of Π over Σ ([PiΣ])
- Action of Σ on isomorphisms, equivalences, and paths ([Σ-cong-fst], [Σ-cong-snd], ...)
- Characterization of equality in Σ-types using transport ([ΣPathTransport{≃,≡}PathΣ])
- Σ with a contractible base is its fiber ([Σ-contractFst, ΣUnit])

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
    ℓ ℓ' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

map-fst : {B : Type ℓ} → (f : A → A') → Σ A (λ _ → B) → Σ A' (λ _ → B)
map-fst f (a , b) = (f a , b)

map-snd : (∀ {a} → B a → B' a) → Σ A B → Σ A B'
map-snd f (a , b) = (a , f b)

-- Characterization of paths in Σ using dependent paths

ΣPathP : ∀ {x y}
  → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y))
  → x ≡ y
ΣPathP eq i = fst eq i , snd eq i

ΣPathIsoPathΣ : {x y : Σ A B}
  → Iso (Σ[ q ∈ fst x ≡ fst y ] (PathP (λ i → B (q i)) (snd x) (snd y)))
        (x ≡ y)
fun ΣPathIsoPathΣ = ΣPathP
inv ΣPathIsoPathΣ eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
rightInv ΣPathIsoPathΣ x = refl {x = x}
leftInv ΣPathIsoPathΣ x = refl {x = x}

ΣPath≃PathΣ : {x y : Σ A B}
  → Σ (fst x ≡ fst y) (λ p → PathP (λ i → B (p i)) (snd x) (snd y)) ≃
    (x ≡ y)
ΣPath≃PathΣ = isoToEquiv ΣPathIsoPathΣ

ΣPath≡PathΣ : {x y : Σ A B} → (Σ (fst x ≡ fst y) (λ q → PathP (λ i → B (q i)) (snd x) (snd y))) ≡ (x ≡ y)
ΣPath≡PathΣ = ua ΣPath≃PathΣ

Σ≡Prop : ((x : A) → isProp (B x)) → {u v : Σ A B}
       → (p : u .fst ≡ v .fst) → u ≡ v
Σ≡Prop pB {u} {v} p i = (p i) , isProp→PathP (λ i → pB (p i)) (u .snd) (v .snd) i

-- Σ of discrete types

discreteΣ : Discrete A → ((a : A) → Discrete (B a)) → Discrete (Σ A B)
discreteΣ {B = B} Adis Bdis (a0 , b0) (a1 , b1) = discreteΣ' (Adis a0 a1)
  where
    discreteΣ' : Dec (a0 ≡ a1) → Dec ((a0 , b0) ≡ (a1 , b1))
    discreteΣ' (yes p) = J (λ a1 p → ∀ b1 → Dec ((a0 , b0) ≡ (a1 , b1))) (discreteΣ'') p b1
      where
        discreteΣ'' : (b1 : B a0) → Dec ((a0 , b0) ≡ (a0 , b1))
        discreteΣ'' b1 with Bdis a0 b0 b1
        ... | (yes q) = yes (transport ΣPath≡PathΣ (refl , q))
        ... | (no ¬q) = no (λ r → ¬q (subst (λ X → PathP (λ i → B (X i)) b0 b1) (Discrete→isSet Adis a0 a0 (cong fst r) refl) (cong snd r)))
    discreteΣ' (no ¬p) = no (λ r → ¬p (cong fst r))

swapΣEquiv : A × A' ≃ A' × A
swapΣEquiv = isoToEquiv (iso (λ x → x .snd , x .fst) (λ z → z .snd , z .fst) (\ _ → refl) (\ _ → refl))

Σ-assoc : (Σ[ (a , b) ∈ Σ A B ] C a b) ≃ (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
Σ-assoc = isoToEquiv (iso (λ { ((x , y) , z) → (x , (y , z)) })
                          (λ { (x , (y , z)) → ((x , y) , z) })
                          (λ _ → refl) (λ _ → refl))

PiΣ : ((a : A) → Σ[ b ∈ B a ] C a b) ≃ (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
PiΣ = isoToEquiv (iso (λ f → fst ∘ f , snd ∘ f)
                      (λ (f , g) → (λ x → f x , g x))
                      (λ _ → refl) (λ _ → refl))

Σ-cong-iso-fst : (isom : Iso A A') → Iso (Σ A (B ∘ (fun isom))) (Σ A' B)
fun (Σ-cong-iso-fst isom) x = (fun isom) (x .fst) , x .snd
inv (Σ-cong-iso-fst {B = B} isom) x = (inv isom) (x .fst) , subst B (sym (ε' (x .fst))) (x .snd)
  where
    ε' = isHAEquiv.ret (snd (iso→HAEquiv isom))
rightInv (Σ-cong-iso-fst {B = B} isom) (x , y) = ΣPathP (ε' x ,
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
leftInv (Σ-cong-iso-fst {A = A} {B = B} isom@(iso f g ε η)) (x , y) = ΣPathP (η x ,
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

Σ-cong-equiv-fst : (e : A ≃ A') → Σ A (B ∘ equivFun e) ≃ Σ A' B
Σ-cong-equiv-fst e = isoToEquiv (Σ-cong-iso-fst (equivToIso e))

Σ-cong-fst : (p : A ≡ A') → Σ A (B ∘ transport p) ≡ Σ A' B
Σ-cong-fst {B = B} p i = Σ (p i) (B ∘ transp (λ j → p (i ∨ j)) i)

Σ-cong-iso-snd : ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')
fun (Σ-cong-iso-snd isom) (x , y) = x , fun (isom x) y
inv (Σ-cong-iso-snd isom) (x , y') = x , inv (isom x) y'
rightInv (Σ-cong-iso-snd isom) (x , y) = ΣPathP (refl , rightInv (isom x) y)
leftInv (Σ-cong-iso-snd isom) (x , y') = ΣPathP (refl , leftInv (isom x) y')

Σ-cong-equiv-snd : (∀ a → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-cong-equiv-snd h = isoToEquiv (Σ-cong-iso-snd (equivToIso ∘ h))

Σ-cong-snd : ((x : A) → B x ≡ B' x) → Σ A B ≡ Σ A B'
Σ-cong-snd {A = A} p i = Σ[ x ∈ A ] (p x i)

Σ-cong-iso : {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
  → (isom : Iso A A')
  → ((x : A) → Iso (B x) (B' (fun isom x)))
  ------------------------
  → Iso (Σ A B) (Σ A' B')
Σ-cong-iso isom isom' = compIso (Σ-cong-iso-snd isom') (Σ-cong-iso-fst isom)

Σ-cong' : {A A' : Type ℓ} {Y : A → Type ℓ'} {Y' : A' → Type ℓ'}
  → (p : A ≡ A')
  → (PathP (λ i → p i → Type ℓ') Y Y')
  ----------
  → (Σ A Y)
  ≡ (Σ A' Y')
Σ-cong' p p' = cong₂ (λ (a : Type _) (b : a → Type _) → Σ a λ x → b x) p p'

-- Alternative version for path in Σ-types, as in the HoTT book

ΣPathTransport : (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b =
  Σ (fst a ≡ fst b) (λ p → transport (λ i → B (p i)) (snd a) ≡ snd b)

ΣPathTransport≃PathΣ : (a b : Σ A B) → ΣPathTransport a b ≃ (a ≡ b)
ΣPathTransport≃PathΣ {B = B} a b =
  compEquiv
    (isoToEquiv (Σ-cong-iso-snd λ p → invIso (equivToIso (PathP≃Path (λ i → B (p i)) _ _))))
    ΣPath≃PathΣ

ΣPathTransport→PathΣ : (a b : Σ A B) → ΣPathTransport a b → (a ≡ b)
ΣPathTransport→PathΣ a b = ΣPathTransport≃PathΣ a b .fst

PathΣ→ΣPathTransport : (a b : Σ A B) → (a ≡ b) → ΣPathTransport a b
PathΣ→ΣPathTransport a b = invEq (ΣPathTransport≃PathΣ a b)

ΣPathTransport≡PathΣ : (a b : Σ A B) → ΣPathTransport a b ≡ (a ≡ b)
ΣPathTransport≡PathΣ a b = ua (ΣPathTransport≃PathΣ a b)

Σ-contractFst : (c : isContr A) → Σ A B ≃ B (c .fst)
Σ-contractFst {B = B} c =
  isoToEquiv
    (iso
      (λ {(a , b) → subst B (sym (c .snd a)) b})
      (c .fst ,_)
      (λ b →
        cong (λ p → subst B p b) (isProp→isSet (isContr→isProp c) _ _ _ _)
        ∙ transportRefl _)
      (λ {(a , b) →
        ΣPathTransport≃PathΣ _ _ .fst (c .snd a , transportTransport⁻ (cong B (c .snd a)) _)}))

-- a special case of the above
ΣUnit : ∀ {ℓ} (A : Unit → Type ℓ) → Σ Unit A ≃ A tt
ΣUnit A = isoToEquiv (iso snd (λ { x → (tt , x) }) (λ _ → refl) (λ _ → refl))

