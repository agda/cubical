{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.RPn.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

open import Cubical.Data.Prod hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.HITs.PropositionalTruncation as PropTrunc

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Bundle : (F : Type ℓ) (E : Type ℓ') (B : Type ℓ'') → Type _
-- Bundle F E B = Σ[ p ∈ (E → B) ] ∀ x → ∥ F ≃ fiber p x ∥

TypeEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeEqvTo ℓ X = TypeWithStr ℓ (λ Y → ∥ Y ≃ X ∥)

PointedEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
PointedEqvTo ℓ X = TypeWithStr ℓ (λ Y → Y × ∥ Y ≃ X ∥)

-- Bundle' : Type ℓ' → Type ℓ'' → (ℓ : Level) → Type (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-suc ℓ))
-- Bundle' F X ℓ = X → TypeEqvTo ℓ F

Total : ∀ {B : Type ℓ} {F : Type ℓ'} {ℓ''} → (B → TypeEqvTo ℓ'' F) → Type _
Total {B = B} {F} p⁻¹ = Σ[ x ∈ B ] typ (p⁻¹ x)

pr : ∀ {B : Type ℓ} {F : Type ℓ'} {ℓ''} (p⁻¹ : B → TypeEqvTo ℓ'' F) → Total p⁻¹ → B
pr p⁻¹ = fst

open import Cubical.Data.Bool
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

2-EltType : (ℓ : Level) → Type (ℓ-suc ℓ)
2-EltType ℓ = TypeEqvTo ℓ Bool

2-EltType₀ = 2-EltType ℓ-zero

2-EltPointed : (ℓ : Level) → Type (ℓ-suc ℓ)
2-EltPointed ℓ = PointedEqvTo ℓ Bool

2-EltPointed₀ = 2-EltPointed ℓ-zero

open import Cubical.Foundations.SIP renaming (SNS₂ to SNS)
open import Cubical.Foundations.Pointed
open import Cubical.Structures.Pointed

2-EltPointed-structure : Type ℓ → Type ℓ
2-EltPointed-structure = add-to-structure pointed-structure (λ Y _ → ∥ Y ≃ Bool ∥)

2-EltPointed-iso : StrIso 2-EltPointed-structure ℓ''
2-EltPointed-iso = add-to-iso pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ Bool ∥)

2-EltPointed-SNS : SNS {ℓ} 2-EltPointed-structure 2-EltPointed-iso
2-EltPointed-SNS = add-axioms-SNS pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ Bool ∥)
                                  (λ _ _ → squash)
                                  pointed-is-SNS

2-EltPointed-SIP : (A B : 2-EltPointed ℓ) → A ≃[ 2-EltPointed-iso ] B ≃ (A ≡ B)
2-EltPointed-SIP = SIP 2-EltPointed-structure 2-EltPointed-iso (SNS₂→SNS₄ 2-EltPointed-SNS)

2-EltPointed-sip : (A B : 2-EltPointed ℓ) → A ≃[ 2-EltPointed-iso ] B → (A ≡ B)
2-EltPointed-sip A B = equivFun (2-EltPointed-SIP A B)

pointed-SIP : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B ≃ (A ≡ B)
pointed-SIP = SIP pointed-structure pointed-iso (SNS₂→SNS₄ pointed-is-SNS)

pointed-sip : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B → (A ≡ B)
pointed-sip A B = equivFun (pointed-SIP A B)

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

dichotomyBool : (x : Bool) → (x ≡ true) ⊎ (x ≡ false)
dichotomyBool true  = inl refl
dichotomyBool false = inr refl

isContr-BoolPointedIso : ∀ x → isContr ((Bool , true) ≃[ pointed-iso ] (Bool , x))
fst (isContr-BoolPointedIso true) = idEquiv _ , refl
snd (isContr-BoolPointedIso true) (e , p)
  = ΣProp≡ (λ e → isSetBool (equivFun e true) true)
           {u = idEquiv _ , refl} {v = e , p}
           (ΣProp≡ isPropIsEquiv λ { i true → p (~ i) ; i false → q (~ i) })
  where q : equivFun e false ≡ false
        q with dichotomyBool (invEq e false)
        ... | (inr q) = cong (equivFun e) (sym q) ∙ retEq e false
        ... | (inl q) = ⊥.rec (true≢false (sym p ∙ cong (equivFun e) (sym q) ∙ retEq e false))
fst (isContr-BoolPointedIso false) = notEquiv , refl
snd (isContr-BoolPointedIso false) (e , p)
  = ΣProp≡ (λ e → isSetBool (equivFun e true) false)
           {u = notEquiv , refl} {v = e , p}
           (ΣProp≡ isPropIsEquiv λ { i true → p (~ i) ; i false → q (~ i) })
  where q : equivFun e false ≡ true
        q with dichotomyBool (invEq e true)
        ... | (inr q) = cong (equivFun e) (sym q) ∙ retEq e true
        ... | (inl q) = ⊥.rec (false≢true (sym p ∙ cong (equivFun e) (sym q) ∙ retEq e true))

isContr-2-EltPointed-iso : (A∙ : 2-EltPointed₀)
                         → isContr ((Bool , true , ∣ idEquiv Bool ∣) ≃[ 2-EltPointed-iso ] A∙)
isContr-2-EltPointed-iso (A , x , ∣e∣)
  = PropTrunc.rec isPropIsContr
                  (λ e → J (λ A∙ _ → isContr ((Bool , true) ≃[ pointed-iso ] A∙))
                           (isContr-BoolPointedIso (equivFun e x))
                           (sym (pointed-sip _ _ (e , refl))))
                  ∣e∣

open import Cubical.Data.NatMinusOne
open import Cubical.HITs.MappingCones

RP  : ℕ₋₁ → Type₀
cov⁻¹ : (n : ℕ₋₁) → RP n → 2-EltType₀

RP neg1 = ⊥
RP (ℕ→ℕ₋₁ n) = Cone (pr (cov⁻¹ (-1+ n)) {- : Total (cov⁻¹ (-1+ n)) → RP (-1+ n) -})

cov⁻¹ neg1 x = Bool , ∣ idEquiv _ ∣
cov⁻¹ (ℕ→ℕ₋₁ n) hub     = Bool , ∣ idEquiv _ ∣
cov⁻¹ (ℕ→ℕ₋₁ n) (inj x) = cov⁻¹ (-1+ n) x
cov⁻¹ (ℕ→ℕ₋₁ n) (spoke (x , y) i) = typ (eq i) , str (eq i) .snd
  where eq : (Bool , true , ∣ idEquiv Bool ∣) ≡ (typ (cov⁻¹ (-1+ n) x) , y , str (cov⁻¹ (-1+ n) x))
        eq = 2-EltPointed-sip _ _ (fst (isContr-2-EltPointed-iso (typ (cov⁻¹ (-1+ n) x) , y , str (cov⁻¹ (-1+ n) x))))

open import Cubical.HITs.Susp
open import Cubical.HITs.Sn
open import Cubical.Foundations.Isomorphism

thm : ∀ n → Total (cov⁻¹ n) ≡ S n
thm neg1 = isoToPath (iso (λ { () }) (λ { () }) (λ { () }) (λ { () }))
thm (ℕ→ℕ₋₁ n) = {!!} ∙ cong Susp (thm (-1+ n))
