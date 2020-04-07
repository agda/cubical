{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.FunExtEquiv
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Monoid


private
  variable
    ℓ ℓ' : Level

group-axiom : (X : Type ℓ) → monoid-structure X → Type ℓ
group-axiom G ((e , _·_) , _) = ((x : G) → Σ G (λ x' → (x · x' ≡ e) × (x' · x ≡ e)))

group-structure : Type ℓ → Type ℓ
group-structure = add-to-structure (monoid-structure) group-axiom

Groups : Type (ℓ-suc ℓ)
Groups {ℓ} = TypeWithStr ℓ group-structure

-- Extracting components of a group

⟨_⟩ : Groups {ℓ} → Type ℓ
⟨ (G , _) ⟩ = G

id : (G : Groups {ℓ}) → ⟨ G ⟩
id (_ , ((e , _) , _) , _) = e

group-operation : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
group-operation (_ , ((_ , f) , _) , _) = f

infixl 20 group-operation
syntax group-operation G x y = x ·⟨ G ⟩ y

group-is-set : (G : Groups {ℓ}) → isSet ⟨ G ⟩
group-is-set (_ , (_ , (P , _)) , _) = P

group-assoc : (G : Groups {ℓ})
            → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
group-assoc (_ , (_ , (_ , P , _)) , _) = P

group-runit : (G : Groups {ℓ})
            → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (id G) ≡ x
group-runit (_ , (_ , (_ , _ , P , _)) , _) = P

group-lunit : (G : Groups {ℓ})
            → (x : ⟨ G ⟩) → (id G) ·⟨ G ⟩ x ≡ x
group-lunit (_ , (_ , (_ , _ , _ , P)) , _) = P

group-Σinv : (G : Groups {ℓ})
           → (x : ⟨ G ⟩) → Σ (⟨ G ⟩) (λ x' → (x ·⟨ G ⟩ x' ≡ (id G)) × (x' ·⟨ G ⟩ x ≡ (id G)))
group-Σinv (_ , _ , P) = P

-- Defining the inverse function

inv : (G : Groups {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩
inv (_ , _ , P) x = fst (P x)

group-rinv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → x ·⟨ G ⟩ (inv G x) ≡ id G
group-rinv (_ , _ , P) x = fst (snd (P x))

group-linv : (G : Groups {ℓ})
               → (x : ⟨ G ⟩) → (inv G x) ·⟨ G ⟩ x ≡ id G
group-linv (_ , _ , P) x = snd (snd (P x))

-- Iso for groups are those for monoids

group-iso : StrIso group-structure ℓ
group-iso = add-to-iso monoid-structure monoid-iso group-axiom

-- Auxiliary lemmas for subtypes (taken from Escardo)

to-Σ-≡ : {X : Type ℓ} {A : X → Type ℓ'} {σ τ : Σ X A}
       → (Σ (fst σ ≡ fst τ) λ p → PathP (λ i → A (p i)) (snd σ) (snd τ))
       → σ ≡ τ
to-Σ-≡ (eq , p) = λ i → eq i , p i

to-subtype-≡ : {X : Type ℓ} {A : X → Type ℓ'} {x y : X}
               {a : A x} {b : A y}
             → ((x : X) → isProp (A x))
             → x ≡ y
             → Path (Σ X (λ x → A x)) (x , a) (y , b)
to-subtype-≡  {x = x} {y} {a} {b} f eq = to-Σ-≡ (eq , toPathP (f y _ b))
-- TODO: this proof without toPathP?

-- Group axiom isProp

group-axiom-isProp : (X : Type ℓ)
                   → (s : monoid-structure X)
                   → isProp (group-axiom X s)
group-axiom-isProp X (((e , _·_) , s@(isSet , assoc , rid , lid))) = isPropPi γ
  where
    γ : (x : X) → isProp (Σ X (λ x' → (x · x' ≡ e) × (x' · x ≡ e)))
    γ x (y , a , q) (z , p , b) = to-subtype-≡ u t
      where      
        t : y ≡ z
        t = inv-lemma X e _·_ s x y z q p

        u : (x' : X) → isProp ((x · x' ≡ e) × (x' · x ≡ e))
        u x' = isPropΣ (isSet _ _)
               (λ _ →   isSet _ _)

-- Group paths equivalent to equality

group-is-SNS : SNS {ℓ} group-structure group-iso
group-is-SNS = add-axioms-SNS monoid-structure monoid-iso
               group-axiom group-axiom-isProp monoid-is-SNS

GroupPath : (M N : Groups {ℓ}) → (M ≃[ group-iso ] N) ≃ (M ≡ N)
GroupPath M N = SIP group-structure group-iso group-is-SNS M N

-- Trying to improve isomorphisms to only have to preserve
-- _·_

group-iso' : StrIso group-structure ℓ
group-iso' G S f =
  (x y : ⟨ G ⟩) → equivFun f (x ·⟨ G ⟩ y) ≡ equivFun f x ·⟨ S ⟩ equivFun f y

-- Trying to reduce isomorphisms to simpler ones
-- First we prove that both notions of group-iso are equal
-- since both are props and there is are functions from
-- one to the other

-- Functions

group-iso→group-iso' : (G S : Groups {ℓ}) (f : ⟨ G ⟩ ≃ ⟨ S ⟩)
                     → group-iso G S f → group-iso' G S f
group-iso→group-iso' G S f γ = snd γ

group-iso'→group-iso : (G S : Groups {ℓ}) (f : ⟨ G ⟩ ≃ ⟨ S ⟩)
                     → group-iso' G S f → group-iso G S f
group-iso'→group-iso G S f γ = η , γ
  where
  g : ⟨ G ⟩ → ⟨ S ⟩
  g = equivFun f

  e : ⟨ G ⟩
  e = id G

  d : ⟨ S ⟩
  d = id S

  δ : g e ≡ g e ·⟨ S ⟩ g e
  δ = g e ≡⟨ cong g (sym (group-lunit G _)) ⟩
      g (e ·⟨ G ⟩ e) ≡⟨ γ e e ⟩
      g e ·⟨ S ⟩ g e ∎

  η : g e ≡ d
  η = g e                                   ≡⟨ sym (group-runit S _) ⟩
      g e ·⟨ S ⟩ d                          ≡⟨ cong (λ - → g e ·⟨ S ⟩ -) (sym (group-rinv S _)) ⟩
      g e ·⟨ S ⟩ (g e ·⟨ S ⟩ (inv S (g e))) ≡⟨ group-assoc S _ _ _ ⟩
     (g e ·⟨ S ⟩ g e) ·⟨ S ⟩ (inv S (g e))  ≡⟨ cong (λ - → group-operation S - (inv S (g e))) (sym δ) ⟩
      g e ·⟨ S ⟩ (inv S (g e))              ≡⟨ group-rinv S _ ⟩
      d ∎

-- Both are Props

isProp-Iso : (G S : Groups {ℓ}) (f : ⟨ G ⟩ ≃ ⟨ S ⟩) → isProp (group-iso G S f)
isProp-Iso G S f = isPropΣ (group-is-set S _ _)
                   (λ _ → isPropPi (λ x → isPropPi λ y → group-is-set S _ _))

isProp-Iso' : (G S : Groups {ℓ}) (f : ⟨ G ⟩ ≃ ⟨ S ⟩) → isProp (group-iso' G S f)
isProp-Iso' G S f = isPropPi (λ x → isPropPi λ y → group-is-set S _ _)

-- Propositional equality 

to-Prop-≡ : {X Y : Type ℓ} (f : X → Y) (g : Y → X)
          → isProp X → isProp Y
          → X ≡ Y
to-Prop-≡ {ℓ} {X} {Y} f g p q = isoToPath (iso f g aux₂ aux₁)
  where
  aux₁ : (x : X) → g (f x) ≡ x
  aux₁ x = p _ _

  aux₂ : (y : Y) → f (g y) ≡ y
  aux₂ y = q _ _

-- Finally both are equal

group-iso'≡group-iso : group-iso' {ℓ} ≡ group-iso
group-iso'≡group-iso = funExt₃ γ
  where
    γ : ∀ (G S : Groups {ℓ}) (f : ⟨ G ⟩ ≃ ⟨ S ⟩)
      → group-iso' G S f ≡ group-iso G S f
    γ G S f = to-Prop-≡ (group-iso'→group-iso G S f)
                        (group-iso→group-iso' G S f)
                        (isProp-Iso' G S f)
                        (isProp-Iso  G S f)

-- And Finally we have what we wanted

group-is-SNS' : SNS {ℓ} group-structure group-iso'
group-is-SNS' = transport γ group-is-SNS
  where
  γ : SNS {ℓ} group-structure group-iso ≡ SNS {ℓ} group-structure group-iso'
  γ = cong (SNS group-structure) (sym group-iso'≡group-iso)

GroupPath' : (M N : Groups {ℓ}) → (M ≃[ group-iso' ] N) ≃ (M ≡ N)
GroupPath' M N = SIP group-structure group-iso' group-is-SNS' M N

---------------------------------------------------------------------
-- Abelians group (just add one axiom and prove that it is a hProp)
---------------------------------------------------------------------

abelian-group-axiom : (X : Type ℓ) → group-structure X → Type ℓ
abelian-group-axiom G (((_ , _·_), _), _) = (x y : G) → x · y ≡ y · x


abelian-group-structure : Type ℓ → Type ℓ
abelian-group-structure = add-to-structure (group-structure) abelian-group-axiom

AbGroups : Type (ℓ-suc ℓ)
AbGroups {ℓ} = TypeWithStr ℓ abelian-group-structure

abelian-group-iso : StrIso abelian-group-structure ℓ
abelian-group-iso = add-to-iso group-structure group-iso abelian-group-axiom

abelian-group-axiom-isProp : (X : Type ℓ)
                           → (s : group-structure X)
                           → isProp (abelian-group-axiom X s)
abelian-group-axiom-isProp X ((_ , (group-isSet , _)) , _) =
  isPropPi (λ x → isPropPi λ y → group-isSet _ _)

abelian-group-is-SNS : SNS {ℓ} abelian-group-structure abelian-group-iso
abelian-group-is-SNS = add-axioms-SNS group-structure group-iso
               abelian-group-axiom abelian-group-axiom-isProp group-is-SNS

AbGroupPath : (M N : AbGroups {ℓ}) → (M ≃[ abelian-group-iso ] N) ≃ (M ≡ N)
AbGroupPath M N = SIP abelian-group-structure abelian-group-iso abelian-group-is-SNS M N
