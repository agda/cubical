{-

This file contains:

  - Classical propositional logic and provability
  - Properties of classical propositional logic
  - Equivalence relation on formulas in terms of provability
  - Definition of Lindenbaum-Tarski algebra
  - Proof that the Lindenbaum-Tarski algebra is a Boolean algebra
  - Proof of soundness

-}


module Cubical.Algebra.LindenbaumTarski where


open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

open import Cubical.Relation.Binary.Base

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base

open import Cubical.Algebra.DistLattice.Base



infix  35  _∧_
infix  30  _∨_
infixl 36  ¬_
infix  20  _⊢_
infix  23  _∷_



data Formula : Type where
  const : ℕ      → Formula
  _∧_   : Formula → Formula → Formula
  _∨_   : Formula → Formula → Formula
  ¬_    : Formula → Formula
  ⊥     : Formula
  ⊤     : Formula


data ctxt : Type where
  ∅    : ctxt
  _∷_  : ctxt → Formula → ctxt


data _∈_ : Formula → ctxt → Type where
  Z  : ∀ {Γ ϕ}   → ϕ ∈ Γ ∷ ϕ
  S  : ∀ {Γ ϕ ψ} → ϕ ∈ Γ
                 → ϕ ∈ Γ ∷ ψ


-- Provability
data _⊢_ : ctxt → Formula → Type where
  ∧-I : {Γ : ctxt} {ϕ ψ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ψ
      → Γ ⊢ ϕ ∧ ψ

  ∧-E₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ϕ

  ∧-E₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ ∧ ψ
       → Γ ⊢ ψ

  ∨-I₁ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ψ
       → Γ ⊢ ϕ ∨ ψ

  ∨-I₂ : {Γ : ctxt} {ϕ ψ : Formula}
       → Γ ⊢ ϕ
       → Γ ⊢ ϕ ∨ ψ

  ∨-E : {Γ : ctxt} {ϕ ψ γ : Formula}
      → Γ ⊢ ϕ ∨ ψ
      → Γ ∷ ϕ ⊢ γ
      → Γ ∷ ψ ⊢ γ
      → Γ ⊢ γ

  ¬-I : {Γ : ctxt} {ϕ : Formula}
      → Γ ∷ ϕ ⊢ ⊥
      → Γ ⊢ ¬ ϕ

  ¬-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ϕ
      → Γ ⊢ ¬ ϕ
      → Γ ⊢ ⊥

  ⊥-E : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ⊥
      → Γ ⊢ ϕ

  ⊤-I : {Γ : ctxt}
      → Γ ⊢ ⊤

  axiom : {Γ : ctxt} {ϕ : Formula}
        → ϕ ∈ Γ
        → Γ ⊢ ϕ

  LEM : {Γ : ctxt} {ϕ : Formula}
      → Γ ⊢ ¬ ϕ ∨ ϕ

  weakening : {Γ : ctxt} {ϕ ψ : Formula}
            → Γ ⊢ ψ
            → Γ ∷ ϕ ⊢ ψ


module _ {Γ : ctxt} where

  -- Implication
  infix  22  _⇒_
  _⇒_ : Formula → Formula → Formula
  ϕ ⇒ ψ = ¬ ϕ ∨ ψ


  -- Useful lemmas
  mp : ∀ {Γ : ctxt} {ϕ ψ : Formula} → Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ → Γ ⊢ ψ
  mp x y = ∨-E x (⊥-E (¬-E (weakening y) (axiom Z))) (axiom Z)

  deduct : ∀ {Γ : ctxt} {ϕ ψ : Formula} → Γ ∷ ϕ ⊢ ψ → Γ ⊢ ϕ ⇒ ψ
  deduct x = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ x)

  cut : ∀ {ϕ ψ γ : Formula} → Γ ⊢ ϕ ⇒ γ → Γ ⊢ γ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ
  cut x y = ∨-E x
                (∨-I₂ (axiom Z))
                (∨-E (weakening y)
                     (⊥-E (¬-E (axiom (S Z)) (axiom Z)))
                     (∨-I₁ (axiom Z)))


{-

  Defining relation where two formulas are related
  if they are provably equivalent.

-}

  _∼_ : Formula → Formula → Type
  ϕ ∼ ψ = (Γ ⊢ ϕ ⇒ ψ) × (Γ ⊢ ψ ⇒ ϕ)

  ∼-refl : ∀ (ϕ : Formula) → ϕ ∼ ϕ
  ∼-refl _ = (LEM , LEM)

  ∼-sym : ∀ {ϕ ψ : Formula} → ϕ ∼ ψ → ψ ∼ ϕ
  ∼-sym (A , B) = (B , A)

  ∼-trans : ∀ {ϕ ψ γ : Formula} → ϕ ∼ γ → γ ∼ ψ → ϕ ∼ ψ
  ∼-trans (x₁ , x₂) (y₁ , y₂) = (cut x₁ y₁ , cut y₂ x₂)


{-

  Properties of propositional calculus

-}

  ∧Comm : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  ∧Comm = (∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm)) ,
          (∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm))
    where
      comm : ∀ {ϕ ψ : Formula} → Γ ∷ ϕ ∧ ψ ⊢ ψ ∧ ϕ
      comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))

  ∨Comm : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  ∨Comm = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm) ,
          ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm)
    where
      comm : {ϕ ψ : Formula} → Γ ∷ ϕ ∨ ψ ⊢ ψ ∨ ϕ
      comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))

  ∧Assoc : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ∧Assoc = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ assoc1) ,
           ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ assoc2)
    where
      assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
      assoc1 = ∧-I (∧-I (∧-E₁ (axiom Z)) (∧-E₁ (∧-E₂ (axiom Z))))
                   (∧-E₂ (∧-E₂ (axiom Z)))
      assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
      assoc2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
                   (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                   (∧-E₂ (axiom Z)))

  ∨Assoc : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ∨Assoc = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ assoc1) ,
           ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ assoc2)
    where
      assoc1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
      assoc1 = ∨-E (axiom Z)
                   (∨-I₂ (∨-I₂ (axiom Z)))
                   (∨-E (axiom Z)
                        (∨-I₂ (∨-I₁ (axiom Z)))
                        (∨-I₁ (axiom Z)))
      assoc2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
      assoc2 = ∨-E (axiom Z)
                   (∨-E (axiom Z)
                        (∨-I₂ (axiom Z))
                        (∨-I₁ (∨-I₂ (axiom Z))))
                   (∨-I₁ (∨-I₁ (axiom Z)))

  ∧Dist : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧Dist = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist1) ,
          ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist2)
    where
      dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∧ (ψ ∨ γ) ⊢ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
      dist1 = ∨-E (∧-E₂ (axiom Z))
                  (∨-I₂ (∧-I (∧-E₁ (axiom (S Z))) (axiom Z)))
                  (∨-I₁ (∧-I (∧-E₁ (axiom (S Z))) (axiom Z)))
      dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∧ ψ) ∨ (ϕ ∧ γ) ⊢ ϕ ∧ (ψ ∨ γ)
      dist2 = ∧-I (∨-E (axiom Z)
                       (∧-E₁ (axiom Z))
                       (∧-E₁ (axiom Z)))
                  (∨-E (axiom Z)
                       (∨-I₂ (∧-E₂ (axiom Z)))
                       (∨-I₁ (∧-E₂ (axiom Z))))

  ∨Dist : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨Dist = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist1) ,
          ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist2)
    where
      dist1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∨ (ψ ∧ γ) ⊢ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
      dist1 = ∨-E (axiom Z)
                  (∧-I (∨-I₂ (axiom Z))
                       (∨-I₂ (axiom Z)))
                  (∧-I (∨-I₁ (∧-E₁ (axiom Z)))
                       (∨-I₁ (∧-E₂ (axiom Z))))
      dist2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∨ ψ) ∧ (ϕ ∨ γ) ⊢ ϕ ∨ (ψ ∧ γ)
      dist2 = ∨-E (∧-E₁ (axiom Z))
                  (∨-I₂ (axiom Z))
                  (∨-E (∧-E₂ (axiom (S Z)))
                       (∨-I₂ (axiom Z))
                       (∨-I₁ (∧-I (axiom (S Z)) (axiom Z))))

  ∧Absorb : ∀ {ϕ ψ : Formula} → ϕ ∧ (ϕ ∨ ψ) ∼ ϕ
  ∧Absorb = (deduct (∧-E₁ (axiom Z))) ,
            (deduct (∧-I (axiom Z) (∨-I₂ (axiom Z))))

  ∨Absorb : ∀ {ϕ ψ : Formula} → (ϕ ∧ ψ) ∨ ψ ∼ ψ
  ∨Absorb = (deduct (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z))) ,
            (deduct (∨-I₁ (axiom Z)))

  ∧Id : ∀ {ϕ : Formula} → ϕ ∧ ⊤ ∼ ϕ
  ∧Id = (deduct (∧-E₁ (axiom Z)) ,
        (deduct (∧-I (axiom Z) ⊤-I)))

  ∨Id : ∀ {ϕ : Formula} → ϕ ∨ ⊥ ∼ ϕ
  ∨Id = (deduct (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)))) ,
        (deduct (∨-I₂ (axiom Z)))

  ∧Complement : ∀ {ϕ : Formula} → ϕ ∧ ¬ ϕ ∼ ⊥
  ∧Complement = (deduct (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)))) ,
                (deduct (⊥-E (axiom Z)))

  ∨Complement : ∀ {ϕ : Formula} → ¬ ϕ ∨ ϕ ∼ ⊤
  ∨Complement = (deduct ⊤-I , deduct LEM)


{-

  Lindenbaum-Tarski algebra is defined as the quotioent
  algebra obtained by factoring the algebra of formulas
  by the above defined equivalence relation.

-}

  LindenbaumTarski : Type
  LindenbaumTarski = Formula / _∼_

  infixl 25 ¬/_

  _∧/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∧/ B = setQuotBinOp ∼-refl ∼-refl _∧_ ∼-respects-∧ A B
    where
      ∼-respects-∧ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∧ ψ) ∼ (ϕ' ∧ ψ')
      ∼-respects-∧ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) =
        deduct (∧-I (mp (weakening x₁) (∧-E₁ (axiom Z))) (mp (weakening y₁) (∧-E₂ (axiom Z)))) ,
        deduct (∧-I (mp (weakening x₂) (∧-E₁ (axiom Z))) (mp (weakening y₂) (∧-E₂ (axiom Z))))

  _∨/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∨/ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B
    where
      ∼-respects-∨ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∨ ψ) ∼ (ϕ' ∨ ψ')
      ∼-respects-∨ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) =
        deduct (∨-E (axiom Z)
                    (∨-I₂ (mp (weakening (weakening x₁)) (axiom Z)))
                    (∨-I₁ (mp (weakening (weakening y₁)) (axiom Z)))) ,
        deduct (∨-E (axiom Z)
                    (∨-I₂ (mp (weakening (weakening x₂)) (axiom Z)))
                    (∨-I₁ (mp (weakening (weakening y₂)) (axiom Z))))

  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
    where
      ∼-respects-¬ : ∀ (ϕ ϕ' : Formula) → ϕ ∼ ϕ' → (¬ ϕ) ∼ (¬ ϕ')
      ∼-respects-¬ ϕ ϕ' (x₁ , x₂) =
        deduct (¬-I (¬-E (mp (weakening (weakening x₁))
                             (mp (weakening (weakening x₂))
                                 (axiom Z)))
                         (⊥-E (¬-E (mp (weakening (weakening x₂))
                                       (axiom Z))
                                   (axiom (S Z)))))) ,
        deduct (¬-I (¬-E (mp (weakening (weakening x₂))
                             (mp (weakening (weakening x₁))
                                 (axiom Z)))
                         (⊥-E (¬-E (mp (weakening (weakening x₁))
                                       (axiom Z))
                                   (axiom (S Z))))))

  ⊤/ : LindenbaumTarski
  ⊤/ = [ ⊤ ]

  ⊥/ : LindenbaumTarski
  ⊥/ = [ ⊥ ]


{-

  By showing the Lindenbaum-Tarski algebra can be viewed as
  a complemented distributive lattice, we prove that it is
  also a Boolean algebra.

-}

  -- LT distributive lattice
  LindenbaumTarski-DistLattice : DistLattice _
  LindenbaumTarski-DistLattice = makeDistLattice∧lOver∨l
                                 ⊥/ ⊤/ _∨/_ _∧/_
                                 isSet-LT
                                 ∨/Assoc ∨/Id ∨/Comm
                                 ∧/Assoc ∧/Id ∧/Comm ∧/Absorb ∧/Dist
    where
      isSet-LT : ∀ (A B : LindenbaumTarski) → isProp(A ≡ B)
      isSet-LT A B = squash/ _ _

      ∧/Comm : ∀ (A B : LindenbaumTarski) → A ∧/ B ≡ B ∧/ A
      ∧/Comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∧Comm

      ∨/Comm : ∀ (A B : LindenbaumTarski) → A ∨/ B ≡ B ∨/ A
      ∨/Comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∨Comm

      ∧/Assoc : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∧/ C) ≡ (A ∧/ B) ∧/ C
      ∧/Assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∧Assoc

      ∨/Assoc : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∨/ C) ≡ (A ∨/ B) ∨/ C
      ∨/Assoc = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∨Assoc

      ∧/Dist : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∨/ C) ≡ (A ∧/ B) ∨/ (A ∧/ C)
      ∧/Dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∧Dist

      ∨/Dist : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∧/ C) ≡ (A ∨/ B) ∧/ (A ∨/ C)
      ∨/Dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∨Dist

      ∧/Absorb : ∀ (A B : LindenbaumTarski) → A ∧/ (A ∨/ B) ≡ A
      ∧/Absorb = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∧Absorb

      ∨/Absorb : ∀ (A B : LindenbaumTarski) → (A ∧/ B) ∨/ B ≡ B
      ∨/Absorb = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∨Absorb

      ∨/Id : ∀ (A : LindenbaumTarski) → A ∨/ ⊥/ ≡ A
      ∨/Id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∨Id

      ∧/Id : ∀ (A : LindenbaumTarski) → A ∧/ ⊤/ ≡ A
      ∧/Id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∧Id


  open DistLatticeStr (snd LindenbaumTarski-DistLattice)

  -- Complemented
  LindenbaumTarski-DistLattice-supremum :
    (A : fst LindenbaumTarski-DistLattice)
    → ¬/ A ∨l A ≡ 1l
  LindenbaumTarski-DistLattice-supremum A = ∨/Complement A
    where
      ∨/Complement : ∀ (A : LindenbaumTarski) → ¬/ A ∨/ A ≡ ⊤/
      ∨/Complement = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∨Complement


  LindenbaumTarski-DistLattice-infimum :
    (A : fst LindenbaumTarski-DistLattice)
    → A ∧l ¬/ A ≡ 0l
  LindenbaumTarski-DistLattice-infimum A = ∧/Complement A
    where
      ∧/Complement : ∀ (A : LindenbaumTarski) → A ∧/ ¬/ A ≡ ⊥/
      ∧/Complement = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∧Complement


{-
  Soundness

  If ϕ provable, then [ϕ] ≡ [⊤]
-}

  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (deduct ⊤-I , deduct (weakening x))
