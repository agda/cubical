{-# OPTIONS --cubical --no-import-sorts  #-}

module SyntheticReals.Utils where -- thing that currently do not belong anywhere and do not have many dependencies

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

⊎-swap : ∀{x : Type ℓ} {y : Type ℓ'} → x ⊎ y → y ⊎ x
⊎-swap (inl x) = inr x
⊎-swap (inr x) = inl x

swap : ∀{x : Type ℓ} {y : Type ℓ'} → x × y → y × x
swap (x , y) = (y , x)

curry : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → (b : B a) → Type ℓ''}
        → ((p : Σ A B) → C (fst p) (snd p))
        → ((x : A) → (y : B x) → C x y)
curry f x y = f (x , y)

-- NOTE: this is non-hProp logic

-- contraposition : {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ¬ Q → ¬ P
-- contraposition f ¬q p = ⊥-elim (¬q (f p))

deMorgan₂' : {P : Type ℓ} {Q : Type ℓ'} → ¬(P ⊎ Q) → (¬ P) × (¬ Q)
deMorgan₂' {P = P} {Q = Q} ¬[p⊎q] = (λ p → ⊥-elim (¬[p⊎q] (inl p))) , λ q → ⊥-elim (¬[p⊎q] (inr q))

deMorgan₂-back' : {P : Type ℓ} {Q : Type ℓ'} → (¬ P) × (¬ Q) → ¬(P ⊎ Q)
deMorgan₂-back' (¬p , ¬q) (inl p) = ¬p p
deMorgan₂-back' (¬p , ¬q) (inr q) = ¬q q

-- hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
-- hPropRel A B ℓ' = A → B → hProp ℓ'

{- NOTE: there is also `Relation.Binary.PropositionalEquality` where they write:

-- Inspect can be used when you want to pattern match on the result r
-- of some expression e, and you also need to "remember" that r ≡ e.

-- See README.Inspect for an explanation of how/why to use this.

record Reveal_·_is_ {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

-}

{- NOTE: an example is

plus-eq-with : ∀ m n → Plus-eq m n (m + n)
plus-eq-with m n with m + n | inspect (m +_) n
... | zero  | [ m+n≡0   ] = m+n≡0⇒m≡0 m m+n≡0 , m+n≡0⇒n≡0 m m+n≡0
... | suc p | [ m+n≡1+p ] = m+n≡1+p

-} -- so this looks like a mechanism for "@-pattern-disribution over `with` cases"

record !_ {ℓ} (X : Type ℓ) : Type ℓ where
  inductive
  constructor !!_ -- map "into"   `!!_  : X → ! X`
  field !!!_ : X  -- map "out of" `!!!_ : ! X → X`
  infix 1 !!!_

open !_ public -- brings !!!_ into scope
infix 1 !!_
infix 1 !_

!-iso : ∀{ℓ} {X : Type ℓ} → Iso (! X) X
Iso.fun      !-iso = !!!_
Iso.inv      !-iso = !!_
Iso.rightInv !-iso = λ      x  → refl
Iso.leftInv  !-iso = λ{ (!! x) → refl }

!-≡ : ∀{ℓ} {X : Type ℓ} → (! X) ≡ X
!-≡ {X = X} = isoToPath !-iso

!-equiv : ∀{ℓ} {X : Type ℓ} → (! X) ≃ X
!-equiv = !!!_ , λ where .equiv-proof x → ((!! x) , refl) , λ{ ((!! y) , p) → λ i → (!! p (~ i)) , (λ j → p (~ i ∨ j)) }

-- `A unfold refl to B` checks `A` and `B` to be definitionally equal (with `refl`) and then uses `B`
--   this allows for a nicer Goal/Have at the very beginning of implementing and when using something
unfold' : ∀{ℓ A} → (x y : A) → _≡_ {ℓ} x y → _
unfold' x y p = y
infix -8 unfold'
syntax unfold' x y p = x unfold p to y
{-# DISPLAY unfold' x y p = p #-}
