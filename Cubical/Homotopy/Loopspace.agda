{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.Loopspace where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation hiding (elim2) renaming (rec to trRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open Iso

{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

{- homotopy Group -}
π : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → Type ℓ
π n A = ∥ typ ((Ω^ n) A) ∥ 2

{- loop space map -}
Ω→ : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → (Ω A →∙ Ω B)
Ω→ (f , f∙) = (λ p → (sym f∙ ∙ cong f p) ∙ f∙) , cong (λ q → q ∙ f∙) (sym (rUnit (sym f∙))) ∙ lCancel f∙

{- Commutativity of loop spaces -}
isComm∙ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
isComm∙ A = (p q : typ (Ω A)) → p ∙ q ≡ q ∙ p

Eckmann-Hilton : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ ((Ω^ (suc n)) A)
Eckmann-Hilton n α β =
  transport (λ i → cong (λ x → rUnit x (~ i)) α ∙ cong (λ x → lUnit x (~ i)) β
                 ≡ cong (λ x → lUnit x (~ i)) β ∙ cong (λ x → rUnit x (~ i)) α)
             λ i → (λ j → α (j ∧ ~ i) ∙ β (j ∧ i)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

isCommA→isCommTrunc : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → isComm∙ A
                    → isOfHLevel (suc n) (typ A)
                    → isComm∙ (∥ typ A ∥ (suc n) , ∣ pt A ∣)
isCommA→isCommTrunc {A = (A , a)} n comm hlev p q =
    ((λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((p ∙ q) j) (~ i)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (cong (trRec hlev (λ x → x)) (p ∙ q)))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) p q i)))
 ∙ ((λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (comm (cong (trRec hlev (λ x → x)) p) (cong (trRec hlev (λ x → x)) q) i))
 ∙∙ (λ i → cong {B = λ _ → ∥ A ∥ (suc n) } (λ x → ∣ x ∣) (congFunct {A = ∥ A ∥ (suc n)} {B = A} (trRec hlev (λ x → x)) q p (~ i)))
 ∙∙ (λ i j → (leftInv (truncIdempotentIso (suc n) hlev) ((q ∙ p) j) i)))

ptdIso→comm : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} (e : Iso (typ A) B) → isComm∙ A → isComm∙ (B , fun e (pt A))
ptdIso→comm {A = (A , a)} {B = B} e comm p q =
       sym (rightInv (congIso e) (p ∙ q))
    ∙∙ (cong (fun (congIso e)) ((invCongFunct e p q)
                            ∙∙ (comm (inv (congIso e) p) (inv (congIso e) q))
                            ∙∙ (sym (invCongFunct e q p))))
    ∙∙ rightInv (congIso e) (q ∙ p)

{- Homotopy group version -}
π-comp : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → ∥ typ ((Ω^ (suc n)) A) ∥₂
      → ∥ typ ((Ω^ (suc n)) A) ∥₂ → ∥ typ ((Ω^ (suc n)) A) ∥₂
π-comp n = elim2 (λ _ _ → setTruncIsSet) λ p q → ∣ p ∙ q ∣₂

Eckmann-Hilton-π : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (p q : ∥ typ ((Ω^ (2 + n)) A) ∥₂)
               → π-comp (1 + n) p q ≡ π-comp (1 + n) q p
Eckmann-Hilton-π  n = elim2 (λ x y → isOfHLevelPath 2 setTruncIsSet _ _)
                             λ p q → cong ∣_∣₂ (Eckmann-Hilton n p q)

{-

{-
open import Cubical.HITs.Rationals.QuoQ renaming (_·_ to _·ℚ_ ; _+_ to _+ℚ_ ; -_ to -ℚ_)
open import Cubical.Data.Nat renaming (_·_ to _ℕ·_)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.SetQuotients as SetQuotient
  using ([_]; eq/; discreteSetQuotients) renaming (_/_ to _//_) public
open import Cubical.HITs.Ints.QuoInt
_∼'_ : ℕ × ℕ₊₁ → ℕ × ℕ₊₁ → Type₀
(a , b) ∼' (c , d) = pos a · ℕ₊₁→ℤ d ≡ pos c · ℕ₊₁→ℤ b

ℚ₊ : Type₀
ℚ₊ = (ℕ × ℕ₊₁) // _∼'_

isSetℚ₊ : isSet ℚ₊
isSetℚ₊ = SetQuotient.squash/

ℚ₊→ℚ : ℚ₊ → ℚ
ℚ₊→ℚ [ a ] = [ (pos (fst a)) , (snd a) ]
ℚ₊→ℚ (eq/ (a , a₀) (b , b₀) r i) = eq/ (pos a , a₀) (pos b , b₀) r i
ℚ₊→ℚ (_//_.squash/ x y p q i j) =
  isSetℚ _ _ (cong ℚ₊→ℚ p) (cong ℚ₊→ℚ q) i j

_-ℚ_ : ℚ → ℚ → ℚ
x -ℚ y = x +ℚ (-ℚ y)

ℚ-rec : ∀ {ℓ} {A : Type ℓ} → (f : (x : ℤ × ℕ₊₁) → A) → ((a b : _) → a ∼ b → f a ≡ f b) → ℚ → A
ℚ-rec f eq [ a ] = f a
ℚ-rec f eq (eq/ a b r i) = eq a b r i
ℚ-rec f eq (_//_.squash/ x x₁ p q i i₁) = {!!}

_<ℚ_ : ℚ → ℚ → Type₀
_<ℚ_ = {!ℚ → ℚ → Type₀!}
_<ℚ₊_ : ℚ₊ → ℚ₊ → Type₀
_<ℚ₊_ = {!!}

_+ℚ₊_ : ℚ₊ → ℚ₊ → ℚ₊
_+ℚ₊_ = {!!}

_-ℚ₊_ : ℚ₊ → ℚ₊ → ℚ₊
_-ℚ₊_ = {!!}

R' : Type₀
~* : ℚ₊ → R' → R' → Type₀
R' = RRR
  module _ where
    data RRR : Type₀ where
      rat : ℚ → RRR
      lim : (x : ℚ₊ → R') → ((δ ε : ℚ₊) → ~* (δ +ℚ₊ ε) (x δ) (x ε)) → RRR

~* = Rel3
  module _ where
    data Rel3 : ℚ₊ → RRR → RRR → Type₀ where
      cond₁ : (q r : ℚ) (ε : ℚ₊)
        → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
        → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
        → Rel3 ε (rat q) (rat r)
      cond₂ : (q : _) (y : _) (ε : _) (δ : _) (pf : _)
            → Rel3 (ε -ℚ₊ δ) (rat q) (y δ) → Rel3 ε (rat q) (lim y pf)
      cond₃ : (x : _) (r : _) (ε : _) (δ : _) (pf : _) → Rel3 (ε -ℚ₊ δ) (x δ) (rat r)
            → Rel3 ε (lim x pf) (rat r)
      cond₄ : (x y : _) (pf1 : _) (pf2 : _) (ε : _) (δ : _) (η : _)
           → Rel3 (ε -ℚ₊ (δ -ℚ₊ η)) (x δ) (y η) → Rel3 ε (lim x pf1) (lim y pf2)

      proppie : (q r : RRR) (ε : ℚ₊) → isProp (Rel3 ε q r)

data ℝ : Type₀ where
  inc : R' → ℝ
  rel : (x y : R') → ((ε : _) → ~* ε x y) → inc x ≡ inc y

-- data Rel : ℚ₊ → ℚ → ℚ → Type₀ where
--   cond₁ : (q r : ℚ) (ε : ℚ₊)
--         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
--         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
--         → Rel ε q r
--   cond₂ : (q y ε δ : ℚ) (ε : ℚ₊)
--         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
--         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
--         → Rel ε q r


-- data ℝ : Type₀ where
--   rat : ℚ → ℝ
--   eqrel₁ : (q r : ℚ) (ε : ℚ₊)
--         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
--         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
--         → rat q ≡ rat r
--   lim : (x : ℚ₊) →  {!!}

-- {-
-- _∼_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → Type₀
-- (a , b) ∼ (c , d) = a · ℕ₊₁→ℤ d ≡ c · ℕ₊₁→ℤ b

-- ℚ : Type₀
-- ℚ = (ℤ × ℕ₊₁) // _∼_


-- isSetℚ : isSet ℚ
-- isSetℚ = SetQuotient.squash/
-- -}
-}

open import Cubical.Data.Sigma
open import Cubical.Algebra.Group

homC : (n : ℕ) (A : Pointed₀) (G : Group₀) → Type₀
homC zero A G = Unit
homC (suc zero) A G = fst G
homC (suc (suc zero)) A G = ∥ fst A ∥₂
homC (suc (suc (suc zero))) A G = ∥ (Σ[ x ∈ typ A ] x ≡ x) ∥₂
homC (suc (suc (suc (suc n)))) A G =
  ∥ Σ[ (x , y , z , w) ∈ typ ((Ω^ n) A) × typ ((Ω^ n) A) × typ ((Ω^ n) A) × typ ((Ω^ n) A) ]
   (Σ[ p ∈ x ≡ y ]
     Σ[ q ∈ z ≡ w ]
       Σ[ r ∈ x ≡ z ]
         (Σ[ s ∈ y ≡ w ] PathP (λ i → r i ≡ s i) p q))  ∥₂

open import Cubical.HITs.SetTruncation renaming (elim to sElim ; rec to sRec ; map to sMap)
zeroz : (n : ℕ) (A : Pointed₀) (G : Group₀) → homC n A G
zeroz zero A G = tt
zeroz (suc zero) A G = GroupStr.0g (snd G)
zeroz (suc (suc zero)) A G = ∣ pt A ∣₂
zeroz (suc (suc (suc zero))) A G = ∣ pt A , refl ∣₂
zeroz (suc (suc (suc (suc n)))) A G =
  ∣ (pt ((Ω^ n) A) , (pt ((Ω^ n) A) , (pt ((Ω^ n) A) , pt ((Ω^ n) A))))
  , refl , refl , refl , refl , refl ∣₂
open import Cubical.Foundations.Function

s : ∀ {A : Type₀} {a : A} (x : a ≡ a) (p : x ≡ x) → transport (λ i → x i ≡ x i) x ≡ x
s {a = a} x p =
     (λ j → transport (λ i → x (i ∨ j) ≡ x i) λ i → x (j ∨ i))
  ∙∙ (λ j → transport (λ i → a ≡ x (i ∨ j)) λ i → x (i ∧ j))
  ∙∙ transportRefl x
   ∙ p

help : ∀ {A : Type₀} {a : A} (x y z w : a ≡ a) (p : x ≡ y) (q : z ≡ w) (r : x ≡ z) → (s : y ≡ w) → PathP (λ i → z i ≡ w i) x y
help x y z w =
  J (λ y p → z ≡ w → x ≡ z → y ≡ w → PathP (λ i → z i ≡ w i) x y)
    (J (λ w q → x ≡ z → x ≡ w → PathP (λ i → z i ≡ w i) x x)
      (J (λ z r → x ≡ z → PathP (λ i → z i ≡ z i) x x)
        λ p → toPathP (s x p)))

d : (n : ℕ) (A : Pointed₀) (G : Group₀) → homC (suc n) A G → homC n A G
d zero A G _ = tt
d (suc zero) A G = {!!}
d (suc (suc zero)) A G = sMap (uncurry λ x p → x)
d (suc (suc (suc zero))) A G =
  sMap (uncurry λ (x , y , z , w) (p , q , r , s , P) → x , p ∙ s ∙ sym q ∙ sym r)
d (suc (suc (suc (suc n)))) A G =
  sRec setTruncIsSet
    (uncurry λ (x , y , z , w) → λ (p , q , r , s , P) → ∣ ((pt (((Ω^ n) A))) , pt ((Ω^ n) A) , pt ((Ω^ n) A) , pt ((Ω^ n) A)) , x , y , z , w , help x y z w p q r s ∣₂)
  {-
  Goal: PathP (λ i → x i ≡ x i) x x
  i = i0 ⊢ x j
i = i1 ⊢ y j
j = i0 ⊢ z i
j = i1 ⊢ w i
  -}

d^2 : (n : ℕ) (A : Pointed₀) (G : Group₀) → (x : homC (suc (suc (suc n))) A G) → d (suc n) A G (d (suc (suc n)) A G x) ≡ zeroz (suc n) A G
d^2 zero A G x = {!!}
d^2 (suc zero) A G = {!!}
d^2 (suc (suc zero)) A G = {!!}
d^2 (suc (suc (suc n))) A G =
  sElim {!!}
    (uncurry λ {(x , y , z , w) →
      uncurry {!J !}})
  where
  helpie : ∀ {A  : Type} {a : A} (x : a ≡ a) → help x x x x refl refl refl refl ≡ {!!}  
  helpie = {!!}
-}
