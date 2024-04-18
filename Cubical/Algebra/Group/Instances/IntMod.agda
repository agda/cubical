{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Instances.IntMod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (isProp≤)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int

open GroupStr
open IsGroup
open IsMonoid


ℤGroup/_ : ℕ → Group₀
ℤGroup/ zero = ℤGroup
fst (ℤGroup/ suc n) = Fin (suc n)
1g (snd (ℤGroup/ suc n)) = 0
GroupStr._·_ (snd (ℤGroup/ suc n)) = _+ₘ_
inv (snd (ℤGroup/ suc n)) = -ₘ_
isGroup (snd (ℤGroup/ suc n)) = makeIsGroup
                                isSetFin
                                (λ x y z → sym (+ₘ-assoc x y z))
                                +ₘ-rUnit
                                +ₘ-lUnit
                                +ₘ-rCancel
                                +ₘ-lCancel

ℤGroup/1≅Unit : GroupIso (ℤGroup/ 1) UnitGroup₀
ℤGroup/1≅Unit = contrGroupIsoUnit isContrFin1

Bool≅ℤGroup/2 : GroupIso BoolGroup (ℤGroup/ 2)
Iso.fun (fst Bool≅ℤGroup/2) false = 1
Iso.fun (fst Bool≅ℤGroup/2) true = 0
Iso.inv (fst Bool≅ℤGroup/2) (zero , p) = true
Iso.inv (fst Bool≅ℤGroup/2) (suc zero , p) = false
Iso.inv (fst Bool≅ℤGroup/2) (suc (suc x) , p) =
  ⊥.rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.rightInv (fst Bool≅ℤGroup/2) (zero , p) =
  Σ≡Prop (λ _ → isProp≤) refl
Iso.rightInv (fst Bool≅ℤGroup/2) (suc zero , p) =
  Σ≡Prop (λ _ → isProp≤) refl
Iso.rightInv (fst Bool≅ℤGroup/2) (suc (suc x) , p) =
  ⊥.rec (¬-<-zero (predℕ-≤-predℕ (predℕ-≤-predℕ p)))
Iso.leftInv (fst Bool≅ℤGroup/2) false = refl
Iso.leftInv (fst Bool≅ℤGroup/2) true = refl
snd Bool≅ℤGroup/2 =
  makeIsGroupHom λ { false false → refl
                   ; false true → refl
                   ; true false → refl
                   ; true true → refl}

ℤGroup/2≅Bool : GroupIso (ℤGroup/ 2) BoolGroup
ℤGroup/2≅Bool = invGroupIso Bool≅ℤGroup/2

-- Definition of the quotient map homomorphism ℤ → ℤGroup/ (suc n)
-- as a group homomorphism.
ℤ→Fin : (n : ℕ) → ℤ → Fin (suc n)
ℤ→Fin n (pos x) = x mod (suc n) , mod< n x
ℤ→Fin n (negsuc x) = -ₘ (suc x mod suc n , mod< n (suc x))

ℤ→Fin-presinv : (n : ℕ) (x : ℤ) → ℤ→Fin n (- x) ≡ -ₘ ℤ→Fin n x
ℤ→Fin-presinv n (pos zero) =
  Σ≡Prop (λ _ → isProp≤) ((λ _ → zero) ∙ sym (cong fst help))
  where
  help : (-ₘ_ {n = n} 0) ≡ 0
  help = GroupTheory.inv1g (ℤGroup/ (suc n))
ℤ→Fin-presinv n (pos (suc x)) = Σ≡Prop (λ _ → isProp≤) refl
ℤ→Fin-presinv n (negsuc x) =
  sym (GroupTheory.invInv (ℤGroup/ (suc n)) _)


-ₘ1-id : (n : ℕ)
      → Path (Fin (suc n)) (-ₘ (1 mod (suc n) , mod< n 1))
                            (n mod (suc n) , mod< n n)
-ₘ1-id zero = refl
-ₘ1-id (suc n) =
     cong -ₘ_ (FinPathℕ ((1 mod suc (suc n)) , mod< (suc n) 1) 1
                (modIndBase (suc n) 1 (n , +-comm n 2)) .snd)
   ∙ Σ≡Prop (λ _ → isProp≤)
      ((+inductionBase (suc n) _
        (λ x _ → ((suc (suc n)) ∸ x) mod (suc (suc n))) λ _ x → x) 1
        (n , (+-comm n 2)))

suc-ₘ1 : (n y : ℕ)
  → ((suc y mod suc n) , mod< n (suc y)) -ₘ (1 mod (suc n) , mod< n 1)
   ≡ (y mod suc n , mod< n y)
suc-ₘ1 zero y =
  isContr→isProp
    (isOfHLevelRetractFromIso 0 (fst ℤGroup/1≅Unit) isContrUnit) _ _
suc-ₘ1 (suc n) y =
     (λ i → ((suc y mod suc (suc n)) , mod< (suc n) (suc y))
         +ₘ (-ₘ1-id (suc n) i))
   ∙ Σ≡Prop (λ _ → isProp≤)
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
     sym (GroupTheory.invInv (ℤGroup/ (suc n)) _)
   ∙ cong -ₘ_
      (GroupTheory.invDistr (ℤGroup/ (suc n))
        (modInd n 1 , mod< n 1) (-ₘ (modInd n (suc y) , mod< n (suc y)))
      ∙ cong (_-ₘ (modInd n 1 , mod< n 1))
       (GroupTheory.invInv (ℤGroup/ (suc n)) (modInd n (suc y) , mod< n (suc y)))
       ∙ suc-ₘ1 n y)

isHomℤ→Fin : (n : ℕ) → IsGroupHom (snd ℤGroup) (ℤ→Fin n) (snd (ℤGroup/ (suc n)))
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
        ∙∙ GroupTheory.invDistr (ℤGroup/ (suc n))
             (modInd n (suc x)
            , mod< n (suc x)) (modInd n (suc y) , mod< n (suc y))
        ∙∙ +ₘ-comm (ℤ→Fin n (negsuc y)) (ℤ→Fin n (negsuc x))}
  where
  +1case :  (y : ℤ) → ℤ→Fin n (1 +ℤ y) ≡ ℤ→Fin n 1 +ₘ ℤ→Fin n y
  +1case (pos zero) = sym (GroupStr.·IdR (snd (ℤGroup/ (suc n))) _)
  +1case (pos (suc y)) =
       cong (ℤ→Fin n) (+Comm 1 (pos (suc y)))
     ∙ Σ≡Prop (λ _ → isProp≤) (mod+mod≡mod (suc n) 1 (suc y))
  +1case (negsuc zero) =
      Σ≡Prop (λ _ → isProp≤) refl
    ∙ sym (GroupStr.·InvR (snd (ℤGroup/ (suc n))) (modInd n 1 , mod< n 1))
  +1case (negsuc (suc y)) =
    Σ≡Prop (λ _ → isProp≤)
      (cong fst (cong (ℤ→Fin n) (+Comm 1 (negsuc (suc y))))
      ∙∙ cong fst (cong -ₘ_ (refl {x = suc y mod suc n , mod< n (suc y)}))
      ∙∙ cong fst (sym (1-ₘsuc n (suc y)))
       ∙ λ i → fst ((1 mod (suc n) , mod< n 1)
         +ₘ (-ₘ (((suc (suc y) mod suc n) , mod< n (suc (suc y)))))))

  pos+case : (x : ℕ) (y : ℤ)
    → ℤ→Fin n (pos x +ℤ y) ≡ ℤ→Fin n (pos x) +ₘ ℤ→Fin n y
  pos+case zero y =
      cong (ℤ→Fin n) (+Comm 0 y)
    ∙ sym (GroupStr.·IdL (snd (ℤGroup/ (suc n))) (ℤ→Fin n y))
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
      Σ≡Prop (λ _ → isProp≤) (sym (mod+mod≡mod (suc n) 1 (suc x)))

-- ℤ/2 lemmas
ℤ/2-elim : ∀ {ℓ} {A : Fin 2 → Type ℓ} → A 0 → A 1 → (x : _) → A x
ℤ/2-elim {A = A} a₀ a₁ (zero , p) = subst (λ p → A (zero , p)) (isProp≤ (0 .snd) p) a₀
ℤ/2-elim {A = A} a₀ a₁ (suc zero , p) = subst (λ p → A (1 , p)) (isProp≤ (1 .snd) p) a₁
ℤ/2-elim {A = A} a₀ a₁ (suc (suc x) , p) =
  ⊥.rec (snotz (cong (λ x → predℕ (predℕ x)) (+-comm (3 +ℕ x) (fst p) ∙ snd p)))

ℤ/2-rec : ∀ {ℓ} {A : Type ℓ} → A → A → Fin 2 → A
ℤ/2-rec {A = A} a₀ a₁ (zero , p) = a₀
ℤ/2-rec {A = A} a₀ a₁ (suc zero , p) = a₁
ℤ/2-rec {A = A} a₀ a₁ (suc (suc x) , p) =
  ⊥.rec (snotz (cong (λ x → predℕ (predℕ x)) (+-comm (3 +ℕ x) (fst p) ∙ snd p)))

-Const-ℤ/2 : (x : fst (ℤGroup/ 2)) → -ₘ x ≡ x
-Const-ℤ/2 = ℤ/2-elim refl refl

pres0→GroupIsoℤ/2 : ∀ {ℓ} {G : Group ℓ} (f : fst G ≃ (ℤGroup/ 2) .fst)
  → fst f (GroupStr.1g (snd G)) ≡ fzero
  → IsGroupHom (snd G) (fst f) ((ℤGroup/ 2) .snd)
pres0→GroupIsoℤ/2 {G = G} f fp = isGroupHomInv ((invEquiv f) , main)
  where
  one = invEq f fone

  f⁻∙ : invEq f fzero ≡ GroupStr.1g (snd G)
  f⁻∙ = sym (cong (invEq f) fp) ∙ retEq f _

  f⁻1 : GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)
      ≡ GroupStr.1g (snd G)
  f⁻1 = sym (retEq f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)))
    ∙∙ cong (invEq f) (mainlem _ refl ∙ sym fp)
    ∙∙ retEq f (GroupStr.1g (snd G))
    where
    l : ¬ (fst f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone))
                ≡ fone)
    l p = snotz (cong fst q)
      where
      q : fone ≡ fzero
      q = (sym (secEq f fone)
        ∙ cong (fst f)
            ((sym (GroupStr.·IdL (snd G) one)
            ∙ cong (λ x → GroupStr._·_ (snd G) x one) (sym (GroupStr.·InvL (snd G) one)))
            ∙ sym (GroupStr.·Assoc (snd G) (GroupStr.inv (snd G) one) one one)))
        ∙ cong (fst f) (cong (GroupStr._·_ (snd G) (GroupStr.inv (snd G) (invEq f fone)))
                ((sym (retEq f _) ∙ cong (invEq f) p)))
        ∙ cong (fst f) (GroupStr.·InvL (snd G) _)
        ∙ fp


    mainlem : (x : _)
      → fst f (GroupStr._·_ (snd G) (invEq f fone) (invEq f fone)) ≡ x
      → f .fst ((snd G GroupStr.· invEq f fone) (invEq f fone)) ≡ fzero
    mainlem = ℤ/2-elim
      (λ p → p)
      λ p → ⊥.rec (l p)


  main : IsGroupHom ((ℤGroup/ 2) .snd) (invEq f) (snd G)
  main =
    makeIsGroupHom
      (ℤ/2-elim
        (ℤ/2-elim (f⁻∙ ∙ sym (GroupStr.·IdR (snd G) (GroupStr.1g (snd G)))
                       ∙ cong (λ x → snd G .GroupStr._·_ x x) (sym f⁻∙))
                  (sym (GroupStr.·IdL (snd G) one)
                  ∙ cong (λ x → snd G .GroupStr._·_ x one) (sym f⁻∙)))
        (ℤ/2-elim (sym (GroupStr.·IdR (snd G) one)
                  ∙ cong (snd G .GroupStr._·_ (invEq f fone)) (sym f⁻∙))
                  (f⁻∙ ∙ sym f⁻1)))
