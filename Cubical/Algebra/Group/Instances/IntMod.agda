{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.IntMod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Int renaming (_+_ to _+ℤ_ ; ℤ to ℤType)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order
open import Cubical.Algebra.Group.Instances.Int
  renaming (ℤ to ℤGroup)
open import Cubical.Algebra.Group.Instances.Unit
  renaming (Unit to UnitGroup)
open import Cubical.Algebra.Group.Instances.Bool
  renaming (Bool to BoolGroup)
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open GroupStr
open IsGroup
open IsMonoid

ℤ/_ : ℕ → Group₀
ℤ/ zero = ℤGroup
fst (ℤ/ suc n) = Fin (suc n)
1g (snd (ℤ/ suc n)) = 0
GroupStr._·_ (snd (ℤ/ suc n)) = _+ₘ_
inv (snd (ℤ/ suc n)) = -ₘ_
IsSemigroup.is-set (isSemigroup (isMonoid (isGroup (snd (ℤ/ suc n))))) =
  isSetFin
IsSemigroup.assoc (isSemigroup (isMonoid (isGroup (snd (ℤ/ suc n))))) =
  λ x y z → sym (+ₘ-assoc x y z)
fst (identity (isMonoid (isGroup (snd (ℤ/ suc n)))) x) = +ₘ-rUnit x
snd (identity (isMonoid (isGroup (snd (ℤ/ suc n)))) x) = +ₘ-lUnit x
fst (inverse (isGroup (snd (ℤ/ suc n))) x) = +ₘ-rCancel x
snd (inverse (isGroup (snd (ℤ/ suc n))) x) = +ₘ-lCancel x

ℤ/1≅Unit : GroupIso (ℤ/ 1) UnitGroup
ℤ/1≅Unit = contrGroupIsoUnit isContrFin1

Bool≅ℤ/2 : GroupIso BoolGroup (ℤ/ 2)
Iso.fun (fst Bool≅ℤ/2) false = 1
Iso.fun (fst Bool≅ℤ/2) true = 0
Iso.inv (fst Bool≅ℤ/2) (zero , p) = true
Iso.inv (fst Bool≅ℤ/2) (suc zero , p) = false
Iso.inv (fst Bool≅ℤ/2) (suc (suc x) , p) =
  ⊥-rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.rightInv (fst Bool≅ℤ/2) (zero , p) =
  Σ≡Prop (λ _ → m≤n-isProp) refl
Iso.rightInv (fst Bool≅ℤ/2) (suc zero , p) =
  Σ≡Prop (λ _ → m≤n-isProp) refl
Iso.rightInv (fst Bool≅ℤ/2) (suc (suc x) , p) =
  ⊥-rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.leftInv (fst Bool≅ℤ/2) false = refl
Iso.leftInv (fst Bool≅ℤ/2) true = refl
snd Bool≅ℤ/2 =
  makeIsGroupHom λ { false false → refl
                   ; false true → refl
                   ; true false → refl
                   ; true true → refl}

ℤ/2≅Bool : GroupIso (ℤ/ 2) BoolGroup
ℤ/2≅Bool = invGroupIso Bool≅ℤ/2

-- Definition of the quotient map homomorphism ℤ → ℤ/ (suc n)
-- as a group homomorphism.
ℤ→Fin : (n : ℕ) → ℤType → Fin (suc n)
ℤ→Fin n (pos x) = x mod (suc n) , mod< n x
ℤ→Fin n (negsuc x) = -ₘ (suc x mod suc n , mod< n (suc x))

ℤ→Fin-presinv : (n : ℕ) (x : ℤType) → ℤ→Fin n (- x) ≡ -ₘ ℤ→Fin n x
ℤ→Fin-presinv n (pos zero) =
  Σ≡Prop (λ _ → m≤n-isProp) ((λ _ → zero) ∙ sym (cong fst help))
  where
  help : (-ₘ_ {n = n} 0) ≡ 0
  help = GroupTheory.inv1g (ℤ/ (suc n))
ℤ→Fin-presinv n (pos (suc x)) = Σ≡Prop (λ _ → m≤n-isProp) refl
ℤ→Fin-presinv n (negsuc x) =
  sym (GroupTheory.invInv (ℤ/ (suc n)) _)


-ₘ1-id : (n : ℕ)
      → Path (Fin (suc n)) (-ₘ (1 mod (suc n) , mod< n 1))
                            (n mod (suc n) , mod< n n)
-ₘ1-id zero = refl
-ₘ1-id (suc n) =
     cong -ₘ_ (FinPathℕ ((1 mod suc (suc n)) , mod< (suc n) 1) 1
                (modIndBase (suc n) 1 (n , +-comm n 2)) .snd)
   ∙ Σ≡Prop (λ _ → m≤n-isProp)
      ((+inductionBase (suc n) _
        (λ x _ → ((suc (suc n)) ∸ x) mod (suc (suc n))) λ _ x → x) 1
        (n , (+-comm n 2)))

suc-ₘ1 : (n y : ℕ)
  → ((suc y mod suc n) , mod< n (suc y)) -ₘ (1 mod (suc n) , mod< n 1)
   ≡ (y mod suc n , mod< n y)
suc-ₘ1 zero y =
  isContr→isProp
    (isOfHLevelRetractFromIso 0 (fst ℤ/1≅Unit) isContrUnit) _ _
suc-ₘ1 (suc n) y =
     (λ i → ((suc y mod suc (suc n)) , mod< (suc n) (suc y))
         +ₘ (-ₘ1-id (suc n) i))
   ∙ Σ≡Prop (λ _ → m≤n-isProp)
      (cong (_mod (2 +ℕ n))
         (cong (_+ℕ (suc n) mod (2 +ℕ n))
           (mod+mod≡mod (suc (suc n)) 1 y))
      ∙∙ sym (mod+mod≡mod (suc (suc n))
             ((1 mod suc (suc n))
              +ℕ (y mod suc (suc n))) (suc n))
      ∙∙ (mod-rCancel (suc (suc n)) ((1 mod suc (suc n))
                                     +ℕ (y mod suc (suc n))) (suc n)
          ∙ cong (_mod (suc (suc n)))
           (cong (_+ℕ (suc n mod suc (suc n)))
                 (+-comm (1 mod suc (suc n)) (y mod suc (suc n)))
           ∙ sym (+-assoc (y mod suc (suc n))
                  (1 mod suc (suc n)) (suc n mod suc (suc n))))
      ∙∙ mod-rCancel (suc (suc n)) (y mod suc (suc n))
            ((1 mod suc (suc n)) +ℕ (suc n mod suc (suc n)))
      ∙∙ (cong (_mod (2 +ℕ n))
            (cong ((y mod suc (suc n)) +ℕ_)
                    (sym (mod+mod≡mod (suc (suc n)) 1 (suc n))
                  ∙ zero-charac (suc (suc n)))
                  ∙ +-comm _ 0)
       ∙ mod-idempotent y)))

1-ₘsuc : (n y : ℕ)
  →     ((1 mod (suc n) , mod< n 1)
     +ₘ (-ₘ (((suc y mod suc n) , mod< n (suc y)))))
       ≡ -ₘ ((y mod suc n) , mod< n y)
1-ₘsuc n y =
     sym (GroupTheory.invInv (ℤ/ (suc n)) _)
   ∙ cong -ₘ_
      (GroupTheory.invDistr (ℤ/ (suc n))
        (modInd n 1 , mod< n 1) (-ₘ (modInd n (suc y) , mod< n (suc y)))
      ∙ cong (_-ₘ (modInd n 1 , mod< n 1))
       (GroupTheory.invInv (ℤ/ (suc n)) (modInd n (suc y) , mod< n (suc y)))
       ∙ suc-ₘ1 n y)

isHomℤ→Fin : (n : ℕ) → IsGroupHom (snd ℤGroup) (ℤ→Fin n) (snd (ℤ/ (suc n)))
isHomℤ→Fin n =
  makeIsGroupHom
    λ { (pos x) y → pos+case x y
      ; (negsuc x) (pos y) →
             cong (ℤ→Fin n) (+Comm (negsuc x) (pos y))
          ∙∙ pos+case y (negsuc x)
          ∙∙ +ₘ-comm (ℤ→Fin n (pos y)) (ℤ→Fin n (negsuc x))
      ; (negsuc x) (negsuc y) →
           sym (cong (ℤ→Fin n) (-Dist+ (pos (suc x)) (pos (suc y))))
        ∙∙ ℤ→Fin-presinv n (pos (suc x) +ℤ (pos (suc y)))
        ∙∙ cong -ₘ_ (pos+case (suc x) (pos (suc y)))
        ∙∙ GroupTheory.invDistr (ℤ/ (suc n))
             (modInd n (suc x)
            , mod< n (suc x)) (modInd n (suc y) , mod< n (suc y))
        ∙∙ +ₘ-comm (ℤ→Fin n (negsuc y)) (ℤ→Fin n (negsuc x))}
  where
  +1case :  (y : ℤType) → ℤ→Fin n (1 +ℤ y) ≡ ℤ→Fin n 1 +ₘ ℤ→Fin n y
  +1case (pos zero) = sym (GroupStr.rid (snd (ℤ/ (suc n))) _)
  +1case (pos (suc y)) =
       cong (ℤ→Fin n) (+Comm 1 (pos (suc y)))
     ∙ Σ≡Prop (λ _ → m≤n-isProp) (mod+mod≡mod (suc n) 1 (suc y))
  +1case (negsuc zero) =
      Σ≡Prop (λ _ → m≤n-isProp) refl
    ∙ sym (GroupStr.invr (snd (ℤ/ (suc n))) (modInd n 1 , mod< n 1))
  +1case (negsuc (suc y)) =
    Σ≡Prop (λ _ → m≤n-isProp)
      (cong fst (cong (ℤ→Fin n) (+Comm 1 (negsuc (suc y))))
      ∙∙ cong fst (cong -ₘ_ (refl {x = suc y mod suc n , mod< n (suc y)}))
      ∙∙ cong fst (sym (1-ₘsuc n (suc y)))
       ∙ λ i → fst ((1 mod (suc n) , mod< n 1)
         +ₘ (-ₘ (((suc (suc y) mod suc n) , mod< n (suc (suc y)))))))

  pos+case : (x : ℕ) (y : ℤType)
    → ℤ→Fin n (pos x +ℤ y) ≡ ℤ→Fin n (pos x) +ₘ ℤ→Fin n y
  pos+case zero y =
      cong (ℤ→Fin n) (+Comm 0 y)
    ∙ sym (GroupStr.lid (snd (ℤ/ (suc n))) (ℤ→Fin n y))
  pos+case (suc zero) y = +1case y
  pos+case (suc (suc x)) y =
       cong (ℤ→Fin n) (cong (_+ℤ y) (+Comm (pos (suc x)) 1)
                     ∙ sym (+Assoc 1 (pos (suc x)) y))
    ∙∙ +1case (pos (suc x) +ℤ y)
    ∙∙ (cong ((modInd n 1 , mod< n 1) +ₘ_) (pos+case (suc x) y)
     ∙∙ sym (+ₘ-assoc (modInd n 1 , mod< n 1)
              (modInd n (suc x) , mod< n (suc x)) (ℤ→Fin n y))
     ∙∙ cong (_+ₘ ℤ→Fin n y) (lem x))
    where
    lem : (x : ℕ)
      → (modInd n 1 , mod< n 1) +ₘ (modInd n (suc x) , mod< n (suc x))
        ≡ ℤ→Fin n (pos (suc (suc x)))
    lem x =
      Σ≡Prop (λ _ → m≤n-isProp) (sym (mod+mod≡mod (suc n) 1 (suc x)))
