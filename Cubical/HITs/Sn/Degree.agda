module Cubical.HITs.Sn.Degree where
{-
Contains facts about the degree of maps Sⁿ → Sⁿ
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; _+_ to _+ℤ_)

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn

-- prelims for definition in 0 case
S⁰×S⁰→ℤ : S₊ 0 → S₊ 0 → ℤ
S⁰×S⁰→ℤ false false = 0
S⁰×S⁰→ℤ false true = -1
S⁰×S⁰→ℤ true false = 1
S⁰×S⁰→ℤ true true = 0

S⁰×S⁰→ℤ-diag : (x : Bool) → S⁰×S⁰→ℤ x x ≡ 0
S⁰×S⁰→ℤ-diag false = refl
S⁰×S⁰→ℤ-diag true = refl

-- degree map
-- We use Hⁿ(Sⁿ,ℤ) rather than πₙ(Sⁿ) for better computational behaviour
degree : (n : ℕ) → (S₊ n → S₊ n) → ℤ
degree zero f = S⁰×S⁰→ℤ (f true) (f false)
degree (suc n) f = Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst) ∣ (λ x → ∣ f x ∣) ∣₂

degree∙ : (n : ℕ) → (S₊∙ n →∙ S₊∙ n) → ℤ
degree∙ zero f = degree 0 (f .fst)
degree∙ (suc n) f = Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst) ∣ (λ x → ∣ fst f x ∣) ∣₂

-- Properties
degreeConst : (n : ℕ) → degree n (λ _ → ptSn n) ≡ 0
degreeConst zero = refl
degreeConst (suc n) = IsGroupHom.pres1 (Hⁿ-Sⁿ≅ℤ n .snd)

-- degree can be stated as an iso
module _ (n : ℕ) where
  degreeIso : Iso ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ ℤ
  degreeIso = compIso (invIso (πₙSⁿ-unpointIso n))
                (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n)))

  degree∥₂ : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ → ℤ
  degree∥₂ = ST.rec isSetℤ (degree (suc n))

  degree∥₂≡ : degree∥₂ ≡ Iso.fun degreeIso
  degree∥₂≡ = funExt (λ f
    → cong degree∥₂
        (sym (Iso.rightInv (πₙSⁿ-unpointIso n) f))
        ∙∙ help (Iso.inv (πₙSⁿ-unpointIso n) f)
        ∙∙ cong (Iso.fun degreeIso) (Iso.rightInv (πₙSⁿ-unpointIso n) f))
    where
    help : (g : _) → degree∥₂ (Iso.fun (πₙSⁿ-unpointIso n) g)
                    ≡ Iso.fun degreeIso (Iso.fun (πₙSⁿ-unpointIso n) g)
    help = ST.elim (λ _ → isOfHLevelPath 2 isSetℤ _ _)
           λ g → cong (Iso.fun (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst))
                                         (fst (Hⁿ-Sⁿ≅ℤ n))))
                   (sym (Iso.leftInv (πₙSⁿ-unpointIso n) ∣ g ∣₂))

  degree∥₂Iso : Iso ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ ℤ
  Iso.fun degree∥₂Iso = degree∥₂
  Iso.inv degree∥₂Iso = Iso.inv degreeIso
  Iso.rightInv degree∥₂Iso p =
    funExt⁻ degree∥₂≡ (Iso.inv degreeIso p) ∙ Iso.rightInv degreeIso p
  Iso.leftInv degree∥₂Iso p =
    cong (Iso.inv degreeIso) (funExt⁻ degree∥₂≡ p) ∙ Iso.leftInv degreeIso p

πₙSⁿ : (n : ℕ) → Group₀
πₙSⁿ n = π'Gr n (S₊∙ (suc n))

degreeComp : (n : ℕ) (f g : (S₊ n → S₊ n))
  → degree n (f ∘ g)
   ≡ degree n f ·ℤ degree n g
degreeComp zero f g with (g true) | (g false)
... | false | false = S⁰×S⁰→ℤ-diag (f false)
    ∙ ·Comm (pos 0) (S⁰×S⁰→ℤ (f true) (f false))
... | false | true = lem (f false) (f true)
  where
  lem : (x y : Bool) → S⁰×S⁰→ℤ x y ≡ (S⁰×S⁰→ℤ y x) ·ℤ negsuc 0
  lem false false = refl
  lem false true = refl
  lem true false = refl
  lem true true = refl
... | true | false = ·Comm 1 (S⁰×S⁰→ℤ (f true) (f false))
... | true | true = S⁰×S⁰→ℤ-diag (f true)
  ∙ ·Comm (pos 0) (S⁰×S⁰→ℤ (f true) (f false))
degreeComp (suc n) f g =
     (λ i → degree∥₂≡ n i ∣ f ∘ g ∣₂)
  ∙∙ deg-comp-help n ∣ f ∣₂ ∣ g ∣₂
  ∙∙ cong₂ _·ℤ_ (sym (funExt⁻ (degree∥₂≡ n) ∣ f ∣₂))
                (sym (funExt⁻ (degree∥₂≡ n) ∣ g ∣₂))
  where
  deg-comp-help : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
     → Iso.fun (degreeIso n) (multSⁿ↬ n f g)
     ≡ (Iso.fun (degreeIso n) f) ·ℤ Iso.fun (degreeIso n) g
  deg-comp-help n f g =
    cong (Iso.fun (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n))))
          (multπₙ-pres' n f g)
     ∙ cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)))
        (multHⁿSⁿ-pres n (isIso-πₙSⁿ-unpointIso n .fst f)
                        (isIso-πₙSⁿ-unpointIso n .fst g))
     ∙ Hⁿ-Sⁿ≅ℤ-pres·
          n (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst f))
            (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst g))

degreeComp' : (n : ℕ) (f g : (S₊ n → S₊ n))
  → degree n (f ∘ g)
   ≡ degree n g ·ℤ degree n f
degreeComp' n f g = degreeComp n f g ∙ ·Comm (degree n f) (degree n g)

πₙSⁿCompComm : (n : ℕ) (f g : (S₊ (suc n) → S₊ (suc n))) → ∥ f ∘ g ≡ g ∘ f ∥₁
πₙSⁿCompComm n f g =
  PT.map (idfun _) (Iso.fun PathIdTrunc₀Iso
  (sym (Iso.leftInv (degree∥₂Iso n) (∣ f ∘ g ∣₂))
  ∙ cong (Iso.inv (degreeIso n))
     (degreeComp (suc n) f g ∙ sym (degreeComp' (suc n) g f))
  ∙ Iso.leftInv (degree∥₂Iso n) (∣ g ∘ f ∣₂)))

degreeSusp : (n : ℕ) (f : S₊ n → S₊ n)
            → degree n f ≡ degree (suc n) (suspFunS∙ f .fst)
degreeSusp zero f with (f true) | (f false)
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl
degreeSusp (suc n) f = cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst))
    (sym (Iso.rightInv (fst (suspensionAx-Sn n n)) _)
    ∙ cong (Iso.fun (suspensionAx-Sn n n .fst)) lem)
  where
  lem : Iso.inv (suspensionAx-Sn n n .fst) ∣ ∣_∣ₕ ∘ f ∣₂
       ≡ ∣ ∣_∣ₕ ∘ suspFun f ∣₂
  lem = cong ∣_∣₂ (funExt
    λ { north → refl
      ; south → cong ∣_∣ₕ (merid (ptSn (suc n)))
      ; (merid a i) j →
       ∣ compPath-filler (merid (f a)) (sym (merid (ptSn (suc n)))) (~ j) i ∣ₕ})

degreeIdfun : (n : ℕ) → degree n (λ x → x) ≡ 1
degreeIdfun zero = refl
degreeIdfun (suc n) =
   cong (degree (suc n)) (sym (cong fst suspFunS∙Id))
  ∙∙ (sym (degreeSusp n (idfun _)))
  ∙∙ degreeIdfun n

degreeHom : {n : ℕ} (f g : S₊∙ (suc n) →∙ S₊∙ (suc n))
  → degree (suc n) (∙Π f g .fst)
   ≡ degree (suc n) (fst f) +ℤ degree (suc n) (fst g)
degreeHom {n = n} f g =
   cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst)) (cong ∣_∣₂ (funExt
     λ x → cong ∣_∣ₕ (cong₂ (λ f g → ∙Π f g .fst x)
                     (sym (Iso.rightInv (sphereFunIso n) f))
                     (sym (Iso.rightInv (sphereFunIso n) g)))
         ∙∙ help n _ _ x
         ∙∙ cong₂ (λ x y → ∣ x ∣ₕ +[ suc n ]ₖ ∣ y ∣ₕ)
                  (funExt⁻ (cong fst (Iso.rightInv (sphereFunIso n) f)) x)
                  (funExt⁻ (cong fst (Iso.rightInv (sphereFunIso n) g)) x)))
  ∙ IsGroupHom.pres· (Hⁿ-Sⁿ≅ℤ n .snd) _ _
  where
  help : (n : ℕ) (f g : S₊∙ n →∙ Ω (S₊∙ (suc n))) (x : S₊ (suc n))
                      → Path (coHomK (suc n))
                  ∣ ∙Π (Iso.fun (sphereFunIso n) f)
                       (Iso.fun (sphereFunIso n) g) .fst x ∣ₕ
                  (∣ fst (Iso.fun (sphereFunIso n) f) x ∣
       +[ suc n ]ₖ ∣ fst (Iso.fun (sphereFunIso n) g) x ∣)
  help zero f g base = refl
  help zero f g (loop i) j = lem j i
    where
    lem : cong ∣_∣ₕ ((fst f false ∙ refl) ∙ fst g false ∙ refl)
        ≡ cong₂ (λ x y → ∣ x ∣ₕ +[ suc zero ]ₖ ∣ y ∣ₕ)
                (fst f false) (fst g false)
    lem = cong-∙ ∣_∣ₕ _ _
      ∙ cong₂ _∙_ ((λ i j → ∣ rUnit (fst f false) (~ i) j  ∣ₕ)
                ∙ (λ j → cong (λ x → rUnitₖ 1 ∣ x ∣ₕ (~ j)) (fst f false)))
                ((λ i j → ∣ rUnit (fst g false) (~ i) j  ∣ₕ)
                ∙ (λ j → cong (λ x → lUnitₖ 1 ∣ x ∣ₕ (~ j)) (fst g false)))
      ∙ sym (cong₂Funct (λ x y → ∣ x ∣ₕ +[ suc zero ]ₖ ∣ y ∣ₕ)
             (fst f false) (fst g false))
  help (suc n) f g north = refl
  help (suc n) f g south = refl
  help (suc n) f g (merid a i) j = lem j i
    where
    lem : cong ∣_∣ₕ ((cong (fst (toΩ→fromSusp f)) (σS a) ∙ refl)
                 ∙ (cong (fst (toΩ→fromSusp g)) (σS a) ∙ refl))
        ≡ cong₂ (λ x y → ∣ x ∣ₕ +[ suc (suc n) ]ₖ ∣ y ∣ₕ)
                (fst f a) (fst g a)
    lem = cong-∙ ∣_∣ₕ _ _
      ∙ cong₂ _∙_ (cong (cong ∣_∣ₕ)
                    (funExt⁻ (cong fst (Iso.leftInv ΩSuspAdjointIso f)) a)
                  ∙ λ j i → rUnitₖ (suc (suc n)) ∣ fst f a i ∣ₕ (~ j))
                  (cong (cong ∣_∣ₕ)
                    (funExt⁻ (cong fst (Iso.leftInv ΩSuspAdjointIso g)) a)
                  ∙ (λ j i → lUnitₖ (suc (suc n)) ∣ fst g a i ∣ₕ (~ j)))
      ∙ sym (cong₂Funct (λ x y → ∣ x ∣ₕ +[ suc (suc n) ]ₖ ∣ y ∣ₕ)
              (fst f a) (fst g a))
