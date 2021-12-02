{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ : Level

module Units (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 private R = fst R'

 inverseUniqueness : (r : R) → isProp (Σ[ r' ∈ R ] r · r' ≡ 1r)
 inverseUniqueness r (r' , rr'≡1) (r'' , rr''≡1) = Σ≡Prop (λ _ → is-set _ _) path
  where
  path : r' ≡ r''
  path = r'             ≡⟨ sym (·Rid _) ⟩
         r' · 1r        ≡⟨ cong (r' ·_) (sym rr''≡1) ⟩
         r' · (r · r'') ≡⟨ ·Assoc _ _ _ ⟩
         (r' · r) · r'' ≡⟨ cong (_· r'') (·-comm _ _) ⟩
         (r · r') · r'' ≡⟨ cong (_· r'') rr'≡1 ⟩
         1r · r''       ≡⟨ ·Lid _ ⟩
         r''            ∎


 Rˣ : ℙ R
 Rˣ r = (Σ[ r' ∈ R ] r · r' ≡ 1r) , inverseUniqueness r

 -- some notation using instance arguments
 _⁻¹ : (r : R) → ⦃ r ∈ Rˣ ⦄ → R
 _⁻¹ r ⦃ r∈Rˣ ⦄ = r∈Rˣ .fst

 infix 9 _⁻¹

 -- some results about inverses
 ·-rinv : (r : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r · r ⁻¹ ≡ 1r
 ·-rinv r ⦃ r∈Rˣ ⦄ = r∈Rˣ .snd

 ·-linv : (r : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r ⁻¹ · r ≡ 1r
 ·-linv r ⦃ r∈Rˣ ⦄ = ·-comm _ _ ∙ r∈Rˣ .snd


 RˣMultClosed : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄
              → (r · r') ∈ Rˣ
 RˣMultClosed r r' = (r ⁻¹ · r' ⁻¹) , path
  where
  path : r · r' · (r ⁻¹ · r' ⁻¹) ≡ 1r
  path = r · r' · (r ⁻¹ · r' ⁻¹) ≡⟨ cong (_· (r ⁻¹ · r' ⁻¹)) (·-comm _ _) ⟩
         r' · r · (r ⁻¹ · r' ⁻¹) ≡⟨ ·Assoc _ _ _ ⟩
         r' · r · r ⁻¹ · r' ⁻¹   ≡⟨ cong (_· r' ⁻¹) (sym (·Assoc _ _ _)) ⟩
         r' · (r · r ⁻¹) · r' ⁻¹ ≡⟨ cong (λ x → r' · x · r' ⁻¹) (·-rinv _) ⟩
         r' · 1r · r' ⁻¹         ≡⟨ cong (_· r' ⁻¹) (·Rid _) ⟩
         r' · r' ⁻¹              ≡⟨ ·-rinv _ ⟩
         1r ∎

 RˣContainsOne : 1r ∈ Rˣ
 RˣContainsOne = 1r , ·Lid _

 RˣInvClosed : (r : R) ⦃ _ : r ∈ Rˣ ⦄ → r ⁻¹ ∈ Rˣ
 RˣInvClosed r = r , ·-linv _

 UnitsAreNotZeroDivisors : (r : R) ⦃ _ : r ∈ Rˣ ⦄
                         → ∀ r' → r' · r ≡ 0r → r' ≡ 0r
 UnitsAreNotZeroDivisors r r' p = r'              ≡⟨ sym (·Rid _) ⟩
                                  r' · 1r         ≡⟨ cong (r' ·_) (sym (·-rinv _)) ⟩
                                  r' · (r · r ⁻¹) ≡⟨ ·Assoc _ _ _ ⟩
                                  r' · r · r ⁻¹   ≡⟨ cong (_· r ⁻¹) p ⟩
                                  0r · r ⁻¹       ≡⟨ 0LeftAnnihilates _ ⟩
                                  0r ∎


 -- laws keeping the instance arguments
 1⁻¹≡1 : ⦃ 1∈Rˣ' : 1r ∈ Rˣ ⦄ → 1r ⁻¹ ≡ 1r
 1⁻¹≡1 ⦃ 1∈Rˣ' ⦄ = (sym (·Lid _)) ∙ 1∈Rˣ' .snd

 ⁻¹-dist-· : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄ ⦃ rr'∈Rˣ : (r · r') ∈ Rˣ ⦄
           → (r · r') ⁻¹ ≡ r ⁻¹ · r' ⁻¹
 ⁻¹-dist-· r r' ⦃ r∈Rˣ ⦄ ⦃ r'∈Rˣ ⦄ ⦃ rr'∈Rˣ ⦄ =
                 sym path ∙∙ cong (r ⁻¹ · r' ⁻¹ ·_) (rr'∈Rˣ .snd) ∙∙ (·Rid _)
  where
  path : r ⁻¹ · r' ⁻¹ · (r · r' · (r · r') ⁻¹) ≡ (r · r') ⁻¹
  path = r ⁻¹ · r' ⁻¹ · (r · r' · (r · r') ⁻¹)
       ≡⟨ ·Assoc _ _ _ ⟩
         r ⁻¹ · r' ⁻¹ · (r · r') · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · r' ⁻¹ · x · (r · r') ⁻¹) (·-comm _ _) ⟩
         r ⁻¹ · r' ⁻¹ · (r' · r) · (r · r') ⁻¹
       ≡⟨ cong (_· (r · r') ⁻¹) (sym (·Assoc _ _ _)) ⟩
         r ⁻¹ · (r' ⁻¹ · (r' · r)) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · x · (r · r') ⁻¹) (·Assoc _ _ _) ⟩
         r ⁻¹ · (r' ⁻¹ · r' · r) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · (x · r) · (r · r') ⁻¹) (·-linv _) ⟩
         r ⁻¹ · (1r · r) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · x · (r · r') ⁻¹) (·Lid _) ⟩
         r ⁻¹ · r · (r · r') ⁻¹
       ≡⟨ cong (_· (r · r') ⁻¹) (·-linv _) ⟩
         1r · (r · r') ⁻¹
       ≡⟨ ·Lid _ ⟩
         (r · r') ⁻¹ ∎

 unitCong : {r r' : R} → r ≡ r' → ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄ → r ⁻¹ ≡ r' ⁻¹
 unitCong {r = r} {r' = r'} p ⦃ r∈Rˣ ⦄ ⦃ r'∈Rˣ ⦄ =
          PathPΣ (inverseUniqueness r' (r ⁻¹ , subst (λ x → x · r ⁻¹ ≡ 1r) p (r∈Rˣ .snd)) r'∈Rˣ) .fst

 ⁻¹-eq-elim : {r r' r'' : R} ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r' ≡ r'' · r → r' · r ⁻¹ ≡ r''
 ⁻¹-eq-elim {r = r} {r'' = r''} p = cong (_· r ⁻¹) p
                                  ∙ sym (·Assoc _ _ _)
                                  ∙ cong (r'' ·_) (·-rinv _)
                                  ∙ ·Rid _


-- some convenient notation
_ˣ : (R' : CommRing ℓ) → ℙ (R' .fst)
R' ˣ = Units.Rˣ R'

module CommRingHoms where
  open RingHoms

  idCommRingHom : (R : CommRing ℓ) → CommRingHom R R
  idCommRingHom R = idRingHom (CommRing→Ring R)

  compCommRingHom : (R S T : CommRing ℓ)
                  → CommRingHom R S → CommRingHom S T → CommRingHom R T
  compCommRingHom R S T = compRingHom {R = CommRing→Ring R} {CommRing→Ring S} {CommRing→Ring T}

  compIdCommRingHom : {R S : CommRing ℓ} (f : CommRingHom R S) → compCommRingHom R R S (idCommRingHom R) f ≡ f
  compIdCommRingHom = compIdRingHom

  idCompCommRingHom : {R S : CommRing ℓ} (f : CommRingHom R S) → compCommRingHom R S S f (idCommRingHom S) ≡ f
  idCompCommRingHom = idCompRingHom

  compAssocCommRingHom : {R S T U : CommRing ℓ} (f : CommRingHom R S) (g : CommRingHom S T) (h : CommRingHom T U) →
                         compCommRingHom R T U (compCommRingHom R S T f g) h ≡
                         compCommRingHom R S U f (compCommRingHom S T U g h)
  compAssocCommRingHom = compAssocRingHom


module CommRingHomTheory {A' B' : CommRing ℓ} (φ : CommRingHom A' B') where
 open Units A' renaming (Rˣ to Aˣ ; _⁻¹ to _⁻¹ᵃ ; ·-rinv to ·A-rinv ; ·-linv to ·A-linv)
 private A = fst A'
 open CommRingStr (snd A') renaming (_·_ to _·A_ ; 1r to 1a)
 open Units B' renaming (Rˣ to Bˣ ; _⁻¹ to _⁻¹ᵇ ; ·-rinv to ·B-rinv)
 open CommRingStr (snd B') renaming  ( _·_ to _·B_ ; 1r to 1b
                                     ; ·Lid to ·B-lid ; ·Rid to ·B-rid
                                     ; ·Assoc to ·B-assoc)

 private
   f = fst φ
 open IsRingHom (φ .snd)

 RingHomRespInv : (r : A) ⦃ r∈Aˣ : r ∈ Aˣ ⦄ → f r ∈ Bˣ
 RingHomRespInv r = f (r ⁻¹ᵃ) , (sym (pres· r (r ⁻¹ᵃ)) ∙∙ cong (f) (·A-rinv r) ∙∙ pres1)

 φ[x⁻¹]≡φ[x]⁻¹ : (r : A) ⦃ r∈Aˣ : r ∈ Aˣ ⦄ ⦃ φr∈Bˣ : f r ∈ Bˣ ⦄
               → f (r ⁻¹ᵃ) ≡ (f r) ⁻¹ᵇ
 φ[x⁻¹]≡φ[x]⁻¹ r ⦃ r∈Aˣ ⦄ ⦃ φr∈Bˣ ⦄ =
  f (r ⁻¹ᵃ)                         ≡⟨ sym (·B-rid _) ⟩
  f (r ⁻¹ᵃ) ·B 1b                   ≡⟨ cong (f (r ⁻¹ᵃ) ·B_) (sym (·B-rinv _)) ⟩
  f (r ⁻¹ᵃ) ·B ((f r) ·B (f r) ⁻¹ᵇ) ≡⟨ ·B-assoc _ _ _ ⟩
  f (r ⁻¹ᵃ) ·B (f r) ·B (f r) ⁻¹ᵇ   ≡⟨ cong (_·B (f r) ⁻¹ᵇ) (sym (pres· _ _)) ⟩
  f (r ⁻¹ᵃ ·A r) ·B (f r) ⁻¹ᵇ       ≡⟨ cong (λ x → f x ·B (f r) ⁻¹ᵇ) (·A-linv _) ⟩
  f 1a ·B (f r) ⁻¹ᵇ                 ≡⟨ cong (_·B (f r) ⁻¹ᵇ) (pres1) ⟩
  1b ·B (f r) ⁻¹ᵇ                   ≡⟨ ·B-lid _ ⟩
  (f r) ⁻¹ᵇ                         ∎


module Exponentiation (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 private R = fst R'

 -- introduce exponentiation
 _^_ : R → ℕ → R
 f ^ zero = 1r
 f ^ suc n = f · (f ^ n)

 infix 9 _^_

 -- and prove some laws
 1ⁿ≡1 : (n : ℕ) → 1r ^ n ≡ 1r
 1ⁿ≡1 zero = refl
 1ⁿ≡1 (suc n) = ·Lid _ ∙ 1ⁿ≡1 n

 ·-of-^-is-^-of-+ : (f : R) (m n : ℕ) → (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
 ·-of-^-is-^-of-+ f zero n = ·Lid _
 ·-of-^-is-^-of-+ f (suc m) n = sym (·Assoc _ _ _) ∙ cong (f ·_) (·-of-^-is-^-of-+ f m n)

 ^-ldist-· : (f g : R) (n : ℕ) → (f · g) ^ n ≡ (f ^ n) · (g ^ n)
 ^-ldist-· f g zero = sym (·Lid 1r)
 ^-ldist-· f g (suc n) = path
  where
  path : f · g · ((f · g) ^ n) ≡ f · (f ^ n) · (g · (g ^ n))
  path = f · g · ((f · g) ^ n)       ≡⟨ cong (f · g ·_) (^-ldist-· f g n) ⟩
         f · g · ((f ^ n) · (g ^ n)) ≡⟨ ·Assoc _ _ _ ⟩
         f · g · (f ^ n) · (g ^ n)   ≡⟨ cong (_· (g ^ n)) (sym (·Assoc _ _ _)) ⟩
         f · (g · (f ^ n)) · (g ^ n) ≡⟨ cong (λ r → (f · r) · (g ^ n)) (·-comm _ _) ⟩
         f · ((f ^ n) · g) · (g ^ n) ≡⟨ cong (_· (g ^ n)) (·Assoc _ _ _) ⟩
         f · (f ^ n) · g · (g ^ n)   ≡⟨ sym (·Assoc _ _ _) ⟩
         f · (f ^ n) · (g · (g ^ n)) ∎

 ^-rdist-·ℕ : (f : R) (n m : ℕ) → f ^ (n ·ℕ m) ≡ (f ^ n) ^ m
 ^-rdist-·ℕ f zero m = sym (1ⁿ≡1 m)
 ^-rdist-·ℕ f (suc n) m =  sym (·-of-^-is-^-of-+ f m (n ·ℕ m))
                        ∙∙ cong (f ^ m ·_) (^-rdist-·ℕ f n m)
                        ∙∙ sym  (^-ldist-· f (f ^ n) m)


-- like in Ring.Properties we provide helpful lemmas here
module CommRingTheory (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 private R = fst R'

 ·-commAssocl : (x y z : R) → x · (y · z) ≡ y · (x · z)
 ·-commAssocl x y z = ·Assoc x y z ∙∙ cong (_· z) (·-comm x y) ∙∙ sym (·Assoc y x z)

 ·-commAssocr : (x y z : R) → x · y · z ≡ x · z · y
 ·-commAssocr x y z = sym (·Assoc x y z) ∙∙ cong (x ·_) (·-comm y z) ∙∙ ·Assoc x z y


 ·-commAssocr2 : (x y z : R) → x · y · z ≡ z · y · x
 ·-commAssocr2 x y z = ·-commAssocr _ _ _ ∙∙ cong (_· y) (·-comm _ _) ∙∙ ·-commAssocr _ _ _

 ·-commAssocSwap : (x y z w : R) → (x · y) · (z · w) ≡ (x · z) · (y · w)
 ·-commAssocSwap x y z w = ·Assoc (x · y) z w ∙∙ cong (_· w) (·-commAssocr x y z)
                                               ∙∙ sym (·Assoc (x · z) y w)

