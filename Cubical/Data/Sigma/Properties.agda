{-

Basic properties about Σ-types

- Action of Σ on functions ([map-fst], [map-snd])
- Characterization of equality in Σ-types using dependent paths ([ΣPath{Iso,≃,≡}PathΣ], [Σ≡Prop])
- Proof that discrete types are closed under Σ ([discreteΣ])
- Commutativity and associativity ([Σ-swap-*, Σ-assoc-*])
- Distributivity of Π over Σ ([Σ-Π-*])
- Action of Σ on isomorphisms, equivalences, and paths ([Σ-cong-fst], [Σ-cong-snd], ...)
- Characterization of equality in Σ-types using transport ([ΣPathTransport{≃,≡}PathΣ])
- Σ with a contractible base is its fiber ([Σ-contractFst, ΣUnit])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
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
open import Cubical.Data.Unit.Base

open Iso

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

map-fst : {B : Type ℓ} → (f : A → A') → A × B → A' × B
map-fst f (a , b) = (f a , b)

map-snd : (∀ {a} → B a → B' a) → Σ A B → Σ A B'
map-snd f (a , b) = (a , f b)

-- Characterization of paths in Σ using dependent paths

ΣPathP : ∀ {x y}
       → Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y)
       → x ≡ y
ΣPathP eq i = fst eq i , snd eq i


ΣPathIsoPathΣ : {x y : Σ A B}
              → Iso (Σ[ p ∈ fst x ≡ fst y ] (PathP (λ i → B (p i)) (snd x) (snd y)))
                    (x ≡ y)
fun ΣPathIsoPathΣ        = ΣPathP
inv ΣPathIsoPathΣ eq     = (λ i → fst (eq i)) , (λ i → snd (eq i))
rightInv ΣPathIsoPathΣ _ = refl
leftInv ΣPathIsoPathΣ _  = refl

ΣPathPIsoPathPΣ : {A : I → Type ℓ} → {B : ∀ i → A i → Type ℓ' }
                      → {a : Σ (A i0) (B i0)} → {b : Σ (A i1) (B i1)}
                      → Iso (Σ[ p ∈ (PathP A (fst a) (fst b)) ]
                                  (PathP (λ i → B i (p i)) (snd a) (snd b)))
                            (PathP (λ i → Σ (A i) (B i)) a b)
ΣPathPIsoPathPΣ =
  iso (λ x i → _ , (snd x i)) (λ x → _ , (λ i → snd (x i)))
       (λ _ → refl) λ _ → refl

ΣPath≃PathΣ : {x y : Σ A B}
            → (Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y))
            ≃ (x ≡ y)
ΣPath≃PathΣ = isoToEquiv ΣPathIsoPathΣ

ΣPath≡PathΣ : {x y : Σ A B}
            → (Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y))
            ≡ (x ≡ y)
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

Σ-swap-Iso : Iso (A × A') (A' × A)
fun Σ-swap-Iso (x , y) = (y , x)
inv Σ-swap-Iso (x , y) = (y , x)
rightInv Σ-swap-Iso _ = refl
leftInv Σ-swap-Iso _  = refl

Σ-swap-≃ : A × A' ≃ A' × A
Σ-swap-≃ = isoToEquiv Σ-swap-Iso

Σ-assoc-Iso : Iso (Σ[ (a , b) ∈ Σ A B ] C a b) (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
fun Σ-assoc-Iso ((x , y) , z) = (x , (y , z))
inv Σ-assoc-Iso (x , (y , z)) = ((x , y) , z)
rightInv Σ-assoc-Iso _ = refl
leftInv Σ-assoc-Iso _  = refl

Σ-assoc-≃ : (Σ[ (a , b) ∈ Σ A B ] C a b) ≃ (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
Σ-assoc-≃ = isoToEquiv Σ-assoc-Iso

Σ-Π-Iso : Iso ((a : A) → Σ[ b ∈ B a ] C a b) (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
fun Σ-Π-Iso f         = (fst ∘ f , snd ∘ f)
inv Σ-Π-Iso (f , g) x = (f x , g x)
rightInv Σ-Π-Iso _    = refl
leftInv Σ-Π-Iso _     = refl

Σ-Π-≃ : ((a : A) → Σ[ b ∈ B a ] C a b) ≃ (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
Σ-Π-≃ = isoToEquiv Σ-Π-Iso

Σ-cong-iso-fst : (isom : Iso A A') → Iso (Σ A (B ∘ fun isom)) (Σ A' B)
fun (Σ-cong-iso-fst isom) x = fun isom (x .fst) , x .snd
inv (Σ-cong-iso-fst {B = B} isom) x = inv isom (x .fst) , subst B (sym (ε (x .fst))) (x .snd)
  where
  ε = isHAEquiv.ret (snd (iso→HAEquiv isom))
rightInv (Σ-cong-iso-fst {B = B} isom) (x , y) = ΣPathP (ε x , toPathP goal)
  where
  ε = isHAEquiv.ret (snd (iso→HAEquiv isom))
  goal : subst B (ε x) (subst B (sym (ε x)) y) ≡ y
  goal = sym (substComposite B (sym (ε x)) (ε x) y)
      ∙∙ cong (λ x → subst B x y) (lCancel (ε x))
      ∙∙ substRefl {B = B} y
leftInv (Σ-cong-iso-fst {A = A} {B = B} isom@(iso f _ _ η)) (x , y) = ΣPathP (η x , toPathP goal)
  where
  ε = isHAEquiv.ret (snd (iso→HAEquiv isom))
  γ = isHAEquiv.com (snd (iso→HAEquiv isom))

  lem : (x : A) → sym (ε (f x)) ∙ cong f (η x) ≡ refl
  lem x = cong (λ a → sym (ε (f x)) ∙ a) (γ x) ∙ lCancel (ε (f x))

  goal : subst B (cong f (η x)) (subst B (sym (ε (f x))) y) ≡ y
  goal = sym (substComposite B (sym (ε (f x))) (cong f (η x)) y)
      ∙∙ cong (λ a → subst B a y) (lem x)
      ∙∙ substRefl {B = B} y

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

Σ-cong-iso : (isom : Iso A A')
           → ((x : A) → Iso (B x) (B' (fun isom x)))
           → Iso (Σ A B) (Σ A' B')
Σ-cong-iso isom isom' = compIso (Σ-cong-iso-snd isom') (Σ-cong-iso-fst isom)

Σ-cong' : (p : A ≡ A') → PathP (λ i → p i → Type ℓ') B B' → Σ A B ≡ Σ A' B'
Σ-cong' p p' = cong₂ (λ (A : Type _) (B : A → Type _) → Σ A B) p p'

-- Alternative version for path in Σ-types, as in the HoTT book

ΣPathTransport : (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b = Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b

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
