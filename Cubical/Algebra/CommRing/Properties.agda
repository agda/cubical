{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing.Base

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' : Level

module Units (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 private R = fst R'

 inverseUniqueness : (r : R) → isProp (Σ[ r' ∈ R ] r · r' ≡ 1r)
 inverseUniqueness r (r' , rr'≡1) (r'' , rr''≡1) = Σ≡Prop (λ _ → is-set _ _) path
  where
  path : r' ≡ r''
  path = r'             ≡⟨ sym (·IdR _) ⟩
         r' · 1r        ≡⟨ congR _·_ (sym rr''≡1) ⟩
         r' · (r · r'') ≡⟨ ·Assoc _ _ _ ⟩
         (r' · r) · r'' ≡⟨ congL _·_ (·Comm _ _) ⟩
         (r · r') · r'' ≡⟨ congL _·_ rr'≡1 ⟩
         1r · r''       ≡⟨ ·IdL _ ⟩
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
 ·-linv r ⦃ r∈Rˣ ⦄ = ·Comm _ _ ∙ r∈Rˣ .snd


 RˣMultClosed : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄
              → (r · r') ∈ Rˣ
 RˣMultClosed r r' = (r ⁻¹ · r' ⁻¹) , path
  where
  path : r · r' · (r ⁻¹ · r' ⁻¹) ≡ 1r
  path = r · r' · (r ⁻¹ · r' ⁻¹) ≡⟨ congL _·_ (·Comm _ _) ⟩
         r' · r · (r ⁻¹ · r' ⁻¹) ≡⟨ ·Assoc _ _ _ ⟩
         r' · r · r ⁻¹ · r' ⁻¹   ≡⟨ congL _·_ (sym (·Assoc _ _ _)) ⟩
         r' · (r · r ⁻¹) · r' ⁻¹ ≡⟨ cong (λ x → r' · x · r' ⁻¹) (·-rinv _) ⟩
         r' · 1r · r' ⁻¹         ≡⟨ congL _·_ (·IdR _) ⟩
         r' · r' ⁻¹              ≡⟨ ·-rinv _ ⟩
         1r ∎

 RˣMultDistributing : (r r' : R)
                    → r · r' ∈ Rˣ → (r ∈ Rˣ) × (r' ∈ Rˣ)
 RˣMultDistributing r r' rr'∈Rˣ =
     firstHalf r r' rr'∈Rˣ
   , firstHalf r' r (subst (_∈ Rˣ) (·Comm _ _) rr'∈Rˣ)
   where
   firstHalf : (r r' : R) → r · r' ∈ Rˣ → (r ∈ Rˣ)
   firstHalf r r' (s , rr's≡1) = r' · s , ·Assoc r r' s ∙ rr's≡1

 RˣContainsOne : 1r ∈ Rˣ
 RˣContainsOne = 1r , ·IdL _

 RˣInvClosed : (r : R) ⦃ _ : r ∈ Rˣ ⦄ → r ⁻¹ ∈ Rˣ
 RˣInvClosed r = r , ·-linv _

 UnitsAreNotZeroDivisors : (r : R) ⦃ _ : r ∈ Rˣ ⦄
                         → ∀ r' → r' · r ≡ 0r → r' ≡ 0r
 UnitsAreNotZeroDivisors r r' p = r'              ≡⟨ sym (·IdR _) ⟩
                                  r' · 1r         ≡⟨ congR _·_ (sym (·-rinv _)) ⟩
                                  r' · (r · r ⁻¹) ≡⟨ ·Assoc _ _ _ ⟩
                                  r' · r · r ⁻¹   ≡⟨ congL _·_ p ⟩
                                  0r · r ⁻¹       ≡⟨ 0LeftAnnihilates _ ⟩
                                  0r ∎


 -- laws keeping the instance arguments
 1⁻¹≡1 : ⦃ 1∈Rˣ' : 1r ∈ Rˣ ⦄ → 1r ⁻¹ ≡ 1r
 1⁻¹≡1 ⦃ 1∈Rˣ' ⦄ = (sym (·IdL _)) ∙ 1∈Rˣ' .snd

 ⁻¹-dist-· : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄ ⦃ rr'∈Rˣ : (r · r') ∈ Rˣ ⦄
           → (r · r') ⁻¹ ≡ r ⁻¹ · r' ⁻¹
 ⁻¹-dist-· r r' ⦃ r∈Rˣ ⦄ ⦃ r'∈Rˣ ⦄ ⦃ rr'∈Rˣ ⦄ =
                 sym path ∙∙ cong (r ⁻¹ · r' ⁻¹ ·_) (rr'∈Rˣ .snd) ∙∙ (·IdR _)
  where
  path : r ⁻¹ · r' ⁻¹ · (r · r' · (r · r') ⁻¹) ≡ (r · r') ⁻¹
  path = r ⁻¹ · r' ⁻¹ · (r · r' · (r · r') ⁻¹)
       ≡⟨ ·Assoc _ _ _ ⟩
         r ⁻¹ · r' ⁻¹ · (r · r') · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · r' ⁻¹ · x · (r · r') ⁻¹) (·Comm _ _) ⟩
         r ⁻¹ · r' ⁻¹ · (r' · r) · (r · r') ⁻¹
       ≡⟨ cong (_· (r · r') ⁻¹) (sym (·Assoc _ _ _)) ⟩
         r ⁻¹ · (r' ⁻¹ · (r' · r)) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · x · (r · r') ⁻¹) (·Assoc _ _ _) ⟩
         r ⁻¹ · (r' ⁻¹ · r' · r) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · (x · r) · (r · r') ⁻¹) (·-linv _) ⟩
         r ⁻¹ · (1r · r) · (r · r') ⁻¹
       ≡⟨ cong (λ x → r ⁻¹ · x · (r · r') ⁻¹) (·IdL _) ⟩
         r ⁻¹ · r · (r · r') ⁻¹
       ≡⟨ cong (_· (r · r') ⁻¹) (·-linv _) ⟩
         1r · (r · r') ⁻¹
       ≡⟨ ·IdL _ ⟩
         (r · r') ⁻¹ ∎

 unitCong : {r r' : R} → r ≡ r' → ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄ → r ⁻¹ ≡ r' ⁻¹
 unitCong {r = r} {r' = r'} p ⦃ r∈Rˣ ⦄ ⦃ r'∈Rˣ ⦄ =
          PathPΣ (inverseUniqueness r' (r ⁻¹ , subst (λ x → x · r ⁻¹ ≡ 1r) p (r∈Rˣ .snd)) r'∈Rˣ) .fst

 ⁻¹-eq-elim : {r r' r'' : R} ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r' ≡ r'' · r → r' · r ⁻¹ ≡ r''
 ⁻¹-eq-elim {r = r} {r'' = r''} p = congL _·_ p
                                  ∙ sym (·Assoc _ _ _)
                                  ∙ congR _·_ (·-rinv _)
                                  ∙ ·IdR _


-- some convenient notation
_ˣ : (R' : CommRing ℓ) → ℙ (R' .fst)
R' ˣ = Units.Rˣ R'

module _ where
  open RingHoms

  idCommRingHom : (R : CommRing ℓ) → CommRingHom R R
  idCommRingHom R = idRingHom (CommRing→Ring R)

  compCommRingHom : (R : CommRing ℓ) (S : CommRing ℓ') (T : CommRing ℓ'')
                  → CommRingHom R S → CommRingHom S T → CommRingHom R T
  compCommRingHom R S T = compRingHom {R = CommRing→Ring R} {CommRing→Ring S} {CommRing→Ring T}

  _∘cr_ : {R : CommRing ℓ} {S : CommRing ℓ'} {T : CommRing ℓ''}
        → CommRingHom S T → CommRingHom R S → CommRingHom R T
  g ∘cr f = compCommRingHom _ _ _ f g

  compIdCommRingHom : {R S : CommRing ℓ} (f : CommRingHom R S)
                    → compCommRingHom _ _ _ (idCommRingHom R) f ≡ f
  compIdCommRingHom = compIdRingHom

  idCompCommRingHom : {R S : CommRing ℓ} (f : CommRingHom R S)
                    → compCommRingHom _ _ _ f (idCommRingHom S) ≡ f
  idCompCommRingHom = idCompRingHom

  compAssocCommRingHom : {R S T U : CommRing ℓ}
                         (f : CommRingHom R S) (g : CommRingHom S T) (h : CommRingHom T U)
                       → compCommRingHom _ _ _ (compCommRingHom _ _ _ f g) h
                       ≡ compCommRingHom _ _ _ f (compCommRingHom _ _ _ g h)
  compAssocCommRingHom = compAssocRingHom

  open Iso

  injCommRingIso : {R : CommRing ℓ} {S : CommRing ℓ'} (f : CommRingIso R S)
                 → (x y : R .fst) → f .fst .fun x ≡ f .fst .fun y → x ≡ y
  injCommRingIso f x y h = sym (f .fst .leftInv x) ∙∙ cong (f .fst .inv) h ∙∙ f .fst .leftInv y

module CommRingEquivs where
 open RingEquivs

 compCommRingEquiv : {A : CommRing ℓ} {B : CommRing ℓ'} {C : CommRing ℓ''}
                   → CommRingEquiv A B → CommRingEquiv B C → CommRingEquiv A C
 compCommRingEquiv {A = A} {B = B} {C = C} = compRingEquiv {A = CommRing→Ring A}
                                                           {B = CommRing→Ring B}
                                                           {C = CommRing→Ring C}

 invCommRingEquiv : (A : CommRing ℓ) → (B : CommRing ℓ') → CommRingEquiv A B → CommRingEquiv B A
 fst (invCommRingEquiv A B e) = invEquiv (fst e)
 snd (invCommRingEquiv A B e) = isRingHomInv e

 idCommRingEquiv : (A : CommRing ℓ) → CommRingEquiv A A
 fst (idCommRingEquiv A) = idEquiv (fst A)
 snd (idCommRingEquiv A) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

module CommRingHomTheory {A' B' : CommRing ℓ} (φ : CommRingHom A' B') where
 open Units A' renaming (Rˣ to Aˣ ; _⁻¹ to _⁻¹ᵃ ; ·-rinv to ·A-rinv ; ·-linv to ·A-linv)
 private A = fst A'
 open CommRingStr (snd A') renaming (_·_ to _·A_ ; 1r to 1a)
 open Units B' renaming (Rˣ to Bˣ ; _⁻¹ to _⁻¹ᵇ ; ·-rinv to ·B-rinv)
 open CommRingStr (snd B') renaming  ( _·_ to _·B_ ; 1r to 1b
                                     ; ·IdL to ·B-lid ; ·IdR to ·B-rid
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
  f (r ⁻¹ᵃ) ·B 1b                   ≡⟨ congR _·B_ (sym (·B-rinv _)) ⟩
  f (r ⁻¹ᵃ) ·B ((f r) ·B (f r) ⁻¹ᵇ) ≡⟨ ·B-assoc _ _ _ ⟩
  f (r ⁻¹ᵃ) ·B (f r) ·B (f r) ⁻¹ᵇ   ≡⟨ congL _·B_ (sym (pres· _ _)) ⟩
  f (r ⁻¹ᵃ ·A r) ·B (f r) ⁻¹ᵇ       ≡⟨ cong (λ x → f x ·B (f r) ⁻¹ᵇ) (·A-linv _) ⟩
  f 1a ·B (f r) ⁻¹ᵇ                 ≡⟨ congL _·B_ pres1 ⟩
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
 1ⁿ≡1 (suc n) = ·IdL _ ∙ 1ⁿ≡1 n

 ·-of-^-is-^-of-+ : (f : R) (m n : ℕ) → (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
 ·-of-^-is-^-of-+ f zero n = ·IdL _
 ·-of-^-is-^-of-+ f (suc m) n = sym (·Assoc _ _ _) ∙ congR _·_ (·-of-^-is-^-of-+ f m n)

 ^-ldist-· : (f g : R) (n : ℕ) → (f · g) ^ n ≡ (f ^ n) · (g ^ n)
 ^-ldist-· f g zero = sym (·IdL 1r)
 ^-ldist-· f g (suc n) = path
  where
  path : f · g · ((f · g) ^ n) ≡ f · (f ^ n) · (g · (g ^ n))
  path = f · g · ((f · g) ^ n)       ≡⟨ cong (f · g ·_) (^-ldist-· f g n) ⟩
         f · g · ((f ^ n) · (g ^ n)) ≡⟨ ·Assoc _ _ _ ⟩
         f · g · (f ^ n) · (g ^ n)   ≡⟨ congL _·_ (sym (·Assoc _ _ _)) ⟩
         f · (g · (f ^ n)) · (g ^ n) ≡⟨ cong (λ r → (f · r) · (g ^ n)) (·Comm _ _) ⟩
         f · ((f ^ n) · g) · (g ^ n) ≡⟨ congL _·_ (·Assoc _ _ _) ⟩
         f · (f ^ n) · g · (g ^ n)   ≡⟨ sym (·Assoc _ _ _) ⟩
         f · (f ^ n) · (g · (g ^ n)) ∎

 ^-rdist-·ℕ : (f : R) (n m : ℕ) → f ^ (n ·ℕ m) ≡ (f ^ n) ^ m
 ^-rdist-·ℕ f zero m = sym (1ⁿ≡1 m)
 ^-rdist-·ℕ f (suc n) m =  sym (·-of-^-is-^-of-+ f m (n ·ℕ m))
                        ∙∙ cong (f ^ m ·_) (^-rdist-·ℕ f n m)
                        ∙∙ sym  (^-ldist-· f (f ^ n) m)

 -- interaction of exponentiation and units
 open Units R'

 ^-presUnit : ∀ (f : R) (n : ℕ) → f ∈ Rˣ → f ^ n ∈ Rˣ
 ^-presUnit f zero f∈Rˣ = RˣContainsOne
 ^-presUnit f (suc n) f∈Rˣ = RˣMultClosed f (f ^ n) ⦃ f∈Rˣ ⦄ ⦃ ^-presUnit f n f∈Rˣ ⦄


-- like in Ring.Properties we provide helpful lemmas here
module CommRingTheory (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 private R = fst R'

 ·CommAssocl : (x y z : R) → x · (y · z) ≡ y · (x · z)
 ·CommAssocl x y z = ·Assoc x y z ∙∙ congL _·_ (·Comm x y) ∙∙ sym (·Assoc y x z)

 ·CommAssocr : (x y z : R) → x · y · z ≡ x · z · y
 ·CommAssocr x y z = sym (·Assoc x y z) ∙∙ congR _·_ (·Comm y z) ∙∙ ·Assoc x z y

 ·CommAssocr2 : (x y z : R) → x · y · z ≡ z · y · x
 ·CommAssocr2 x y z = ·CommAssocr _ _ _ ∙∙ congL _·_ (·Comm _ _) ∙∙ ·CommAssocr _ _ _

 ·CommAssocSwap : (x y z w : R) → (x · y) · (z · w) ≡ (x · z) · (y · w)
 ·CommAssocSwap x y z w =
   ·Assoc (x · y) z w ∙∙ congL _·_ (·CommAssocr x y z) ∙∙ sym (·Assoc (x · z) y w)



-- the CommRing version of uaCompEquiv
module CommRingUAFunctoriality where
 open CommRingStr
 open CommRingEquivs

 CommRing≡ : (A B : CommRing ℓ) → (
   Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ]
   Σ[ q0 ∈ PathP (λ i → p i) (0r (snd A)) (0r (snd B)) ]
   Σ[ q1 ∈ PathP (λ i → p i) (1r (snd A)) (1r (snd B)) ]
   Σ[ r+ ∈ PathP (λ i → p i → p i → p i) (_+_ (snd A)) (_+_ (snd B)) ]
   Σ[ r· ∈ PathP (λ i → p i → p i → p i) (_·_ (snd A)) (_·_ (snd B)) ]
   Σ[ s ∈ PathP (λ i → p i → p i) (-_ (snd A)) (-_ (snd B)) ]
   PathP (λ i → IsCommRing (q0 i) (q1 i) (r+ i) (r· i) (s i)) (isCommRing (snd A)) (isCommRing (snd B)))
   ≃ (A ≡ B)
 CommRing≡ A B = isoToEquiv theIso
   where
   open Iso
   theIso : Iso _ _
   fun theIso (p , q0 , q1 , r+ , r· , s , t) i = p i
                                                , commringstr (q0 i) (q1 i) (r+ i) (r· i) (s i) (t i)
   inv theIso x = cong ⟨_⟩ x , cong (0r ∘ snd) x , cong (1r ∘ snd) x
                , cong (_+_ ∘ snd) x , cong (_·_ ∘ snd) x , cong (-_ ∘ snd) x , cong (isCommRing ∘ snd) x
   rightInv theIso _ = refl
   leftInv theIso _ = refl

 caracCommRing≡ : {A B : CommRing ℓ} (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracCommRing≡ {A = A} {B = B} p q P =
   sym (transportTransport⁻ (ua (CommRing≡ A B)) p)
                                    ∙∙ cong (transport (ua (CommRing≡ A B))) helper
                                    ∙∙ transportTransport⁻ (ua (CommRing≡ A B)) q
     where
     helper : transport (sym (ua (CommRing≡ A B))) p ≡ transport (sym (ua (CommRing≡ A B))) q
     helper = Σ≡Prop
                (λ _ → isPropΣ
                          (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd B)) _ _)
                          λ _ → isOfHLevelPathP 1 (isPropIsCommRing _ _ _ _ _) _ _)
               (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

 uaCompCommRingEquiv : {A B C : CommRing ℓ} (f : CommRingEquiv A B) (g : CommRingEquiv B C)
                  → uaCommRing (compCommRingEquiv f g) ≡ uaCommRing f ∙ uaCommRing g
 uaCompCommRingEquiv f g = caracCommRing≡ _ _ (
   cong ⟨_⟩ (uaCommRing (compCommRingEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaCommRing f) ∙ cong ⟨_⟩ (uaCommRing g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaCommRing f) (uaCommRing g)) ⟩
   cong ⟨_⟩ (uaCommRing f ∙ uaCommRing g) ∎)



open CommRingEquivs
open CommRingUAFunctoriality
recPT→CommRing : {A : Type ℓ'} (𝓕  : A → CommRing ℓ)
           → (σ : ∀ x y → CommRingEquiv (𝓕 x) (𝓕 y))
           → (∀ x y z → σ x z ≡ compCommRingEquiv (σ x y) (σ y z))
          ------------------------------------------------------
           → ∥ A ∥₁ → CommRing ℓ
recPT→CommRing 𝓕 σ compCoh = GpdElim.rec→Gpd isGroupoidCommRing 𝓕
  (3-ConstantCompChar 𝓕 (λ x y → uaCommRing (σ x y))
                          λ x y z → sym (  cong uaCommRing (compCoh x y z)
                                         ∙ uaCompCommRingEquiv (σ x y) (σ y z)))
