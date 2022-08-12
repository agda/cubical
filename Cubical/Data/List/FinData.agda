{-# OPTIONS --safe #-}
module Cubical.Data.List.FinData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism


open import Cubical.Relation.Binary

open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.SetQuotients as SQ

open import Cubical.HITs.FiniteMultiset as FM renaming (_∷_ to _∷fm_ ; [] to []fm)
open import Cubical.HITs.FreeComMonoids using (FreeComMonoid;AssocList≃FreeComMonoid)
open import Cubical.HITs.AssocList using (FMSet≃AssocList)

variable
  ℓ : Level
  A : Type ℓ

-- copy-paste from agda-stdlib
lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero ^a = []
tabulate (suc n) ^a = ^a zero ∷ tabulate n (^a ∘ suc)

length-tabulate : ∀ n → (^a : Fin n → A) → length (tabulate n ^a) ≡ n
length-tabulate zero ^a = refl
length-tabulate (suc n) ^a = cong suc (length-tabulate n (^a ∘ suc))

tabulate-lookup : ∀ (xs : List A) → tabulate (length xs) (lookup xs) ≡ xs
tabulate-lookup [] = refl
tabulate-lookup (x ∷ xs) = cong (x ∷_) (tabulate-lookup xs)

lookup-tabulate : ∀ n → (^a : Fin n → A)
  → PathP (λ i → (Fin (length-tabulate n ^a i) → A)) (lookup (tabulate n ^a)) ^a
lookup-tabulate (suc n) ^a i zero = ^a zero
lookup-tabulate (suc n) ^a i (suc p) = lookup-tabulate n (^a ∘ suc) i p

lookup-tabulateT : ∀ n → (^a : Fin n → A)
  →  lookup (tabulate n ^a) ∘ subst⁻ Fin (length-tabulate n ^a) ≡ ^a
lookup-tabulateT n ^a = funExt (λ _ → sym (transportRefl _)) ∙ fromPathP (lookup-tabulate n ^a)


permute : ∀ {n} (l : List A) → Fin n ≃ Fin (length l) → List A
permute l e = tabulate _ (lookup l ∘ (equivFun e))


length-permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l)) →
                  length (permute l e) ≡ n 
length-permute l e = length-tabulate _ _

_↔_ : List A → List A → Type _
x ↔ y =
  Σ (Fin (length x) ≃ Fin (length y))
     λ e → ∀ k → lookup x k ≡ lookup y (equivFun e k)

↔permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l))
                → l ↔ (permute l e) 
↔permute {n = n} l e = invEquiv e ∙ₑ pathToEquiv (cong Fin (sym (length-permute l e))) ,
    λ k → cong (lookup l) (sym (secEq e k))
      ∙ λ i → lookup-tabulateT n (λ x₁ → lookup l (fst e x₁)) (~ i) (invEq e k)
     
isSym↔ : BinaryRelation.isSym (_↔_ {A = A})
fst (isSym↔ _ _ (e , _)) = invEquiv e
snd (isSym↔ _ b (e , p)) k =
  cong (lookup b) (sym (secEq e _)) ∙ sym (p _)

isTrans↔ : BinaryRelation.isTrans (_↔_ {A = A})
fst (isTrans↔ _ _ _ (e , _) (f , _)) = e ∙ₑ f
snd (isTrans↔ _ _ _ (_ , p) (_ , q)) k = p _ ∙ q _

isEquivRel↔ : BinaryRelation.isEquivRel {ℓ = ℓ} {A = List A} _↔_
isEquivRel↔ =
 BinaryRelation.equivRel
   (λ _ → idEquiv _ , (λ _ → refl))
   isSym↔ isTrans↔

↔→length≡ : ∀ {x y : List A} →  x ↔ y → length x ≡ length y
↔→length≡ = isInjectiveFin≃ ∘ fst


List/↔ : (A : Type ℓ) → Type ℓ
List/↔ A =  List A / _↔_

_∷/_ : A → List/↔ A → List/↔ A
_∷/_ {A = A} a = SQ.rec squash/ (_/_.[_] ∘ (a ∷_))
            λ x y r → eq/ _ _ ((sucPerm (fst r))
             , λ { zero → refl ; (suc k) → snd r k} )
 
List→FM : List A → FMSet A
List→FM {A = A} = foldr {B = FMSet A} _∷fm_ []fm

h-swap : (l : List A) → ∀ k → List→FM l ≡ List→FM (permute l (PunchInOut≃ k))
h-swap (x ∷ l) zero = cong List→FM (sym (tabulate-lookup (x ∷ l)))
h-swap (x ∷ x₁ ∷ l) one i = comm x x₁ (List→FM (tabulate-lookup l (~ i))) i
h-swap (x ∷ x₁ ∷ l) (suc (suc k)) = cong (x ∷fm_) (h-swap (x₁ ∷ l) (suc k)) ∙ comm _ _ _


h : ∀ n → (a b : List A) → length a ≡ n → length b ≡ n →
       a ↔ b → List→FM a ≡ List→FM b
h zero [] [] x x₁ x₂ = refl
h zero [] (x₃ ∷ b) x x₁ x₂ = ⊥.rec (Cubical.Data.Nat.snotz x₁)
h zero (x₃ ∷ a) _ x x₁ x₂ = ⊥.rec (Cubical.Data.Nat.snotz x)
h (suc n) [] b x x₁ x₂ = ⊥.rec (Cubical.Data.Nat.znots x)
h (suc n) (x₃ ∷ a) [] x x₁ x₂ = ⊥.rec (Cubical.Data.Nat.znots x₁)
h (suc n) (x ∷ xs) (y ∷ ys) pX pY ro@(e , p) =
  let (e' , p') = Fin≃SucEquiv'' e
      y' = lookup (y ∷ ys)
           (equivFun
            (sucPerm (fst (Fin≃SucEquiv'' e)) ∙ₑ PunchInOut≃ (equivFun e zero))
            zero)
      ys' = tabulate (length xs)
               (λ x₁ →
                  lookup (y ∷ ys)
                  (equivFun
                   (sucPerm (fst (Fin≃SucEquiv'' e)) ∙ₑ PunchInOut≃ (equivFun e zero))
                   (suc x₁)))
      lenX=lenY = isInjectiveFin≃ e'

  in cong (List→FM) (sym (tabulate-lookup (x ∷ xs)) ∙
          cong (tabulate _) (funExt p ∙ cong (lookup (y ∷ ys) ∘_) (cong equivFun p')))
       ∙∙
       cong (y' ∷fm_)
       (h n ys' (permute ys' (invEquiv e' ∙ₑ pathToEquiv (cong Fin (sym (length-tabulate _ _)))))
         (length-tabulate _ _ ∙ injSuc pX) (length-tabulate (length ys) _ ∙ sym lenX=lenY ∙ injSuc pX)
         (↔permute ys' ((invEquiv e' ∙ₑ pathToEquiv (cong Fin (sym (length-tabulate _ _))))))
         ∙ cong (List→FM ∘ tabulate (length ys))
           (cong (_∘ invEq e') (lookup-tabulateT _ _) ∙
            cong (((
               lookup (y ∷ ys) ∘ 
                (equivFun (PunchInOut≃ (equivFun e zero))) ∘  suc) ∘_) ∘ fst) ((invEquiv-is-linv e'))))
        ∙∙
         sym (h-swap (y ∷ ys) (equivFun e zero))


IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
IsoList/↔FMSet {A = A} = w
  where

    toFM : _
    toFM = SQ.rec trunc List→FM
      λ a b r → h (length a) a b refl (sym (↔→length≡ {x = a} {y = b} r)) r

    fromFM : _
    fromFM = FM.Rec.f squash/
        _/_.[ [] ] _∷/_
        λ _ _ → elimProp (λ _ → squash/ _ _)
          λ _ → eq/ _ _ (swapHead ,
             λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

    w : Iso (List/↔ A) (FMSet A)
    Iso.fun w = toFM
    Iso.inv w = fromFM
    Iso.rightInv w = 
      FM.ElimProp.f (trunc _ _) refl
        λ a {xs} →
          ((elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
               (λ _ → trunc _ _) (λ _ → refl) ∘ fromFM) xs ∙_) ∘ cong (_ ∷fm_)

    Iso.leftInv w = SQ.elimProp (λ x → squash/ _ _) (ind refl (cong (_ ∷/_)))


List/↔≃FreeComMonoid : List/↔ A ≃ FreeComMonoid A
List/↔≃FreeComMonoid = isoToEquiv IsoList/↔FMSet ∙ₑ FMSet≃AssocList ∙ₑ AssocList≃FreeComMonoid
