{-# OPTIONS --cubical --safe #-}
module Cubical.LindenbaumTarski where


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
infix  22  _⇒_ 



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
            
--  exchange : {Γ : ctxt} {ϕ ψ γ : Formula}
--           → (Γ ∷ ϕ) ∷ ψ ⊢ γ
--           → (Γ ∷ ψ) ∷ ϕ ⊢ γ
           
--  contraction : {Γ : ctxt} {ϕ ψ : Formula}
--              → (Γ ∷ ϕ) ∷ ϕ ⊢ ψ
--              → (Γ ∷ ϕ) ⊢ ψ


-- Implication
_⇒_ : Formula → Formula → Formula
ϕ ⇒ ψ = ¬ ϕ ∨ ψ


module _ {Γ : ctxt} where


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

  ∧-comm : ∀ {ϕ ψ : Formula} → ϕ ∧ ψ ∼ ψ ∧ ϕ
  ∧-comm = (∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm)) ,
           (∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm))
    where
      comm : ∀ {ϕ ψ : Formula} → Γ ∷ ϕ ∧ ψ ⊢ ψ ∧ ϕ
      comm = ∧-I (∧-E₂ (axiom Z)) (∧-E₁ (axiom Z))


  ∨-comm : ∀ {ϕ ψ : Formula} → ϕ ∨ ψ ∼ ψ ∨ ϕ
  ∨-comm = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm) ,
           ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ comm)
    where
      comm : {ϕ ψ : Formula} → Γ ∷ ϕ ∨ ψ ⊢ ψ ∨ ϕ
      comm = ∨-E (axiom Z) (∨-I₁ (axiom Z)) (∨-I₂ (axiom Z))

  ∧-ass : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∧ γ) ∼ (ϕ ∧ ψ) ∧ γ
  ∧-ass = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ ass1) ,
          ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ ass2)
    where
      ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∧ (ψ ∧ γ) ⊢ (ϕ ∧ ψ) ∧ γ
      ass1 = ∧-I (∧-I (∧-E₁ (axiom Z)) (∧-E₁ (∧-E₂ (axiom Z))))
                 (∧-E₂ (∧-E₂ (axiom Z)))           
      ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∧ ψ) ∧ γ ⊢ ϕ ∧ (ψ ∧ γ)
      ass2 = ∧-I (∧-E₁ (∧-E₁ (axiom Z)))
                 (∧-I (∧-E₂ (∧-E₁ (axiom Z)))
                 (∧-E₂ (axiom Z)))


  ∨-ass : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∨ γ) ∼ (ϕ ∨ ψ) ∨ γ
  ∨-ass = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ ass1) ,
          ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ ass2)
    where
      ass1 : ∀ {ϕ ψ γ : Formula} → Γ ∷ ϕ ∨ (ψ ∨ γ) ⊢ (ϕ ∨ ψ) ∨ γ
      ass1 = ∨-E (axiom Z)
                   (∨-I₂ (∨-I₂ (axiom Z)))
                   (∨-E (axiom Z)
                        (∨-I₂ (∨-I₁ (axiom Z)))
                        (∨-I₁ (axiom Z)))                             
      ass2 : ∀ {ϕ ψ γ : Formula} → Γ ∷ (ϕ ∨ ψ) ∨ γ ⊢ ϕ ∨ (ψ ∨ γ)
      ass2 = ∨-E (axiom Z)
                   (∨-E (axiom Z)
                        (∨-I₂ (axiom Z))
                        (∨-I₁ (∨-I₂ (axiom Z))))
                   (∨-I₁ (∨-I₁ (axiom Z)))

  ∧-dist : ∀ {ϕ ψ γ : Formula} → ϕ ∧ (ψ ∨ γ) ∼ (ϕ ∧ ψ) ∨ (ϕ ∧ γ)
  ∧-dist = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist1) ,
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

  ∨-dist : ∀ {ϕ ψ γ : Formula} → ϕ ∨ (ψ ∧ γ) ∼ (ϕ ∨ ψ) ∧ (ϕ ∨ γ)
  ∨-dist = ∨-E LEM (∨-I₂ (axiom Z)) (∨-I₁ dist1) ,
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


  ∧-abs : ∀ {ϕ ψ : Formula} → ϕ ∧ (ϕ ∨ ψ) ∼ ϕ 
  ∧-abs = (deduct (∧-E₁ (axiom Z))) ,
          (deduct (∧-I (axiom Z) (∨-I₂ (axiom Z))))
  

  ∨-abs : ∀ {ϕ ψ : Formula} → (ϕ ∧ ψ) ∨ ψ ∼ ψ
  ∨-abs = (deduct (∨-E (axiom Z) (∧-E₂ (axiom Z)) (axiom Z))) ,
          (deduct (∨-I₁ (axiom Z)))


  ∧-id : ∀ {ϕ : Formula} → ϕ ∧ ⊤ ∼ ϕ
  ∧-id = (deduct (∧-E₁ (axiom Z)) ,
         (deduct (∧-I (axiom Z) ⊤-I)))


  ∨-id : ∀ {ϕ : Formula} → ϕ ∨ ⊥ ∼ ϕ
  ∨-id = (deduct (∨-E (axiom Z) (axiom Z) (⊥-E (axiom Z)))) ,
         (deduct (∨-I₂ (axiom Z)))


  ∧-comp : ∀ {ϕ : Formula} → ϕ ∧ ¬ ϕ ∼ ⊥
  ∧-comp = (deduct (¬-E (∧-E₁ (axiom Z)) (∧-E₂ (axiom Z)))) ,
           (deduct (⊥-E (axiom Z))) 

  ∨-comp : ∀ {ϕ : Formula} → ¬ ϕ ∨ ϕ ∼ ⊤
  ∨-comp = (deduct ⊤-I , deduct LEM)


  ∼-respects-∧ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∧ ψ) ∼ (ϕ' ∧ ψ')
  ∼-respects-∧ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) =
    deduct (∧-I (mp (weakening x₁) (∧-E₁ (axiom Z))) (mp (weakening y₁) (∧-E₂ (axiom Z)))) ,
    deduct (∧-I (mp (weakening x₂) (∧-E₁ (axiom Z))) (mp (weakening y₂) (∧-E₂ (axiom Z))))


  ∼-respects-∨ : ∀ (ϕ ϕ' ψ ψ' : Formula) → ϕ ∼ ϕ' → ψ ∼ ψ' → (ϕ ∨ ψ) ∼ (ϕ' ∨ ψ')
  ∼-respects-∨ ϕ ϕ' ψ ψ' (x₁ , x₂) (y₁ , y₂) =
    deduct (∨-E (axiom Z)
                (∨-I₂ (mp (weakening (weakening x₁)) (axiom Z)))
                (∨-I₁ (mp (weakening (weakening y₁)) (axiom Z)))) ,
    deduct (∨-E (axiom Z)
                (∨-I₂ (mp (weakening (weakening x₂)) (axiom Z)))
                (∨-I₁ (mp (weakening (weakening y₂)) (axiom Z))))


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

  _∨/_ : LindenbaumTarski → LindenbaumTarski → LindenbaumTarski
  A ∨/ B = setQuotBinOp ∼-refl ∼-refl _∨_ ∼-respects-∨ A B

  ¬/_ : LindenbaumTarski → LindenbaumTarski
  ¬/ A = setQuotUnaryOp ¬_ ∼-respects-¬ A
  
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
                                 ⊥/
                                 ⊤/
                                 _∨/_
                                 _∧/_
                                 isSet-LT
                                 ∨/-ass
                                 ∨/-id
                                 ∨/-comm
                                 ∧/-ass
                                 ∧/-id
                                 ∧/-comm
                                 ∧/-abs
                                 ∧/-dist
    where
      isSet-LT : ∀ (A B : LindenbaumTarski) → isProp(A ≡ B)
      isSet-LT A B = squash/ _ _

      ∧/-comm : ∀ (A B : LindenbaumTarski) → A ∧/ B ≡ B ∧/ A
      ∧/-comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∧-comm

      ∨/-comm : ∀ (A B : LindenbaumTarski) → A ∨/ B ≡ B ∨/ A
      ∨/-comm = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∨-comm

      ∧/-ass : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∧/ C) ≡ (A ∧/ B) ∧/ C
      ∧/-ass = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∧-ass

      ∨/-ass : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∨/ C) ≡ (A ∨/ B) ∨/ C
      ∨/-ass = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∨-ass

      ∧/-dist : ∀ (A B C : LindenbaumTarski) → A ∧/ (B ∨/ C) ≡ (A ∧/ B) ∨/ (A ∧/ C)
      ∧/-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∧-dist

      ∨/-dist : ∀ (A B C : LindenbaumTarski) → A ∨/ (B ∧/ C) ≡ (A ∨/ B) ∧/ (A ∨/ C)
      ∨/-dist = elimProp3 (λ _ _ _ → squash/ _ _) λ _ _ _ → eq/ _ _ ∨-dist

      ∧/-abs : ∀ (A B : LindenbaumTarski) → A ∧/ (A ∨/ B) ≡ A
      ∧/-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∧-abs

      ∨/-abs : ∀ (A B : LindenbaumTarski) → (A ∧/ B) ∨/ B ≡ B
      ∨/-abs = elimProp2 (λ _ _ → squash/ _ _) λ _ _ → eq/ _ _ ∨-abs

      ∨/-id : ∀ (A : LindenbaumTarski) → A ∨/ ⊥/ ≡ A
      ∨/-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∨-id

      ∧/-id : ∀ (A : LindenbaumTarski) → A ∧/ ⊤/ ≡ A
      ∧/-id = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∧-id


  open DistLatticeStr (snd LindenbaumTarski-DistLattice)

  -- Complemented
  LindenbaumTarski-DistLattice-supremum : (A : fst LindenbaumTarski-DistLattice) → ¬/ A ∨l A ≡ 1l
  LindenbaumTarski-DistLattice-supremum A = ∨/-comp A
    where
      ∨/-comp : ∀ (A : LindenbaumTarski) → ¬/ A ∨/ A ≡ ⊤/
      ∨/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∨-comp


  LindenbaumTarski-DistLattice-infimum : (A : fst LindenbaumTarski-DistLattice) → A ∧l ¬/ A ≡ 0l
  LindenbaumTarski-DistLattice-infimum A = ∧/-comp A
    where
      ∧/-comp : ∀ (A : LindenbaumTarski) → A ∧/ ¬/ A ≡ ⊥/
      ∧/-comp = elimProp (λ _ → squash/ _ _) λ _ → eq/ _ _ ∧-comp


{-
  Soundness
  
  #TODO?:
    * truth valuation v : Formula → {0,1}
    * function h : LT → {0,1}
    * h([x]) = v(x) homomorphism ⇔ h([x]) truth valuation
-}
    
  sound : ∀ {ϕ : Formula} → Γ ⊢ ϕ → [ ϕ ] ≡ ⊤/
  sound x = eq/ _ _ (deduct ⊤-I , deduct (weakening x))
