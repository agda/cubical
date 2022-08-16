{-# OPTIONS --safe #-}
module Cubical.Data.List.FinData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.Nat renaming (snotz to ℕsnotz ; znots to ℕznots)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎


open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)

open import Cubical.HITs.FiniteMultiset as FM
  renaming (_∷_ to _∷fm_ ; [] to []fm ; _++_ to _++fm_) hiding ([_])
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

lookup-tabulateT : ∀ n → (^a : Fin n → A) → ∀ k
    → lookup (tabulate n ^a) (subst⁻ Fin (length-tabulate n ^a) k) ≡ ^a k
lookup-tabulateT n ^a k = (sym (transportRefl _)) ∙ funExt⁻ (fromPathP (lookup-tabulate n ^a)) k

permute : ∀ {n} (l : List A) → Fin n ≃ Fin (length l) → List A
permute l e = tabulate _ (lookup l ∘ (equivFun e))

length-permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l)) →
                  length (permute l e) ≡ n 
length-permute _ _ = length-tabulate _ _

length-permute' : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l)) →
                  length (permute l e) ≡ length l 
length-permute' l e = length-permute l e ∙ isInjectiveFin≃ e


tabulate∘ : ∀ {n m} → (e : Fin n → A)
               (g : Fin m → Fin n)  →
                tabulate m (lookup (tabulate n e)
                  ∘ subst⁻ Fin (length-tabulate _ _) ∘ g)  ≡
                  tabulate m (e ∘ g)
tabulate∘ {m = zero} _ _ = refl
tabulate∘ {m = suc _} e _ = 
  cong₂ _∷_
    ( congP (λ i → lookup-tabulate _ e i)
     (toPathP (transportTransport⁻ (cong Fin _) _)))
    (tabulate∘ e _)




infix 4  _↔_

_↔_ : List A → List A → Type _
x ↔ y =
  Σ (Fin (length x) ≃ Fin (length y))
     λ e → ∀ k → lookup x k ≡ lookup y (equivFun e k)

↔permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l))
                → l ↔ (permute l e) 
↔permute l e = invEquiv e ∙ₑ ≡→Fin≃ (sym (length-permute l e)) ,
    λ k → cong (lookup l) (sym (secEq e k))
      ∙ sym (lookup-tabulateT _ (lookup l ∘ (fst e)) (invEq e k))

isRefl↔ : BinaryRelation.isRefl (_↔_ {A = A})
isRefl↔ = (λ _ → idEquiv _ , (λ _ → refl))

isSym↔ : BinaryRelation.isSym (_↔_ {A = A})
isSym↔ _ b (e , p) = invEquiv e , λ k → cong (lookup b) (sym (secEq e _)) ∙ sym (p _)

isTrans↔ : BinaryRelation.isTrans (_↔_ {A = A})
isTrans↔ _ _ _ (e , p) (f , q) = e ∙ₑ f , λ _ → p _ ∙ q _

infixr 30 _∙↔_

_∙↔_ : {a b c : List A} → a ↔ b → b ↔ c → a ↔ c
_∙↔_ {a = a} {b} {c} p q = isTrans↔ a b c p q

isEquivRel↔ : BinaryRelation.isEquivRel {ℓ = ℓ} {A = List A} _↔_
isEquivRel↔ = BinaryRelation.equivRel isRefl↔ isSym↔ isTrans↔

↔→length≡ : ∀ {x y : List A} →  x ↔ y → length x ≡ length y
↔→length≡ = isInjectiveFin≃ ∘ fst

¬nil↔cons : ∀ {x : A} {xs} → ¬ ([] ↔ x ∷ xs)
¬nil↔cons = ℕznots ∘ ↔→length≡ {x = []}  

¬cons↔nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ↔ [])
¬cons↔nil = ℕsnotz ∘ ↔→length≡ {y = []}  

_∷↔_ : ∀ (a : A) {xs ys} → xs ↔ ys → a ∷ xs ↔ a ∷ ys
a ∷↔ (e , p) = sucPerm e , λ { zero → refl ; (suc _) → p _}

≡→↔ : ∀ {xs ys : List A} → xs ≡ ys → xs ↔ ys
≡→↔ {xs = xs} = J (λ ys p → xs ↔ ys) (isRefl↔ xs)

headSwap↔ : {x y : A} → ∀ {l} → x ∷ y ∷ l ↔ y ∷ x ∷ l
headSwap↔ =
  swap0and1 , λ { zero → refl ; one → refl ; (suc (suc k)) → refl }


_∷↔∷ʳ_ : ∀ xs → (x : A) → xs ∷ʳ x ↔ x ∷ xs
_∷↔∷ʳ_ = ind (isRefl↔ ∘ [_])
  λ x _ →    ≡→↔ (++-assoc [ _ ] _ [ _ ])
          ∙↔ (_ ∷↔ x _)
          ∙↔ headSwap↔
 
_↔∷ʳ_ : ∀ {xs ys} → xs ↔ ys → ∀ (a : A) → xs ∷ʳ a ↔ ys ∷ʳ a
_↔∷ʳ_ {xs = xs} {ys} r _ =
  isTrans↔ (xs ∷ʳ _) _ (ys ∷ʳ _) (xs ∷↔∷ʳ _)
   (isTrans↔ _ _ (ys ∷ʳ _) (_ ∷↔ r) (isSym↔ (ys ∷ʳ _) (_ ∷ ys)  (ys ∷↔∷ʳ _)))


lookup-FinSumChar : ∀ {xs ys : List A} →
        ∀ k → lookup (xs ++ ys) k ≡
         ⊎.rec (lookup xs) (lookup ys)
           (FinSumChar.inv (length xs) (length ys)
             (subst Fin (length++ xs ys) k))
lookup-FinSumChar {xs = []} {ys} _ = cong (lookup ys) (sym (transportRefl _))
lookup-FinSumChar {xs = x ∷ xs} {ys} zero = 
   cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ (FinSumChar.inv _ _))
     (transportFin-zero _)
lookup-FinSumChar {xs = x ∷ xs} {ys} (suc _) = 
   _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
   _ ≡⟨ h (FinSumChar.inv _ _ _) ⟩
   _ ≡⟨ cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ FinSumChar.inv _ _)
           (sym (transportFin-suc (length++ xs ys) _ _)) ⟩ _ ∎
            
  where
    h : ∀ z → ⊎.rec _ _ z ≡ ⊎.rec (lookup (x ∷ xs)) _ (FinSumChar.invSucAux _ _ z)
    h (inl _) = refl
    h (inr _) = refl

cong↔++R : ∀ {xs ys : List A} → xs ↔ ys → ∀ l → xs ++ l ↔ ys ++ l
cong↔++R {xs = xs} {ys} (e , p) _ =
 let hh = ⊎-equiv e (idEquiv _)
 in ≡→Fin≃ _ ∙ₑ invEquiv (FinSumChar.Equiv _ _) ∙ₑ hh
      ∙ₑ FinSumChar.Equiv _ _  ∙ₑ ≡→Fin≃ _
 , λ _ → 
   let k' = FinSumChar.inv _ _ _
   in _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
      _ ≡⟨ cong (λ g → ⊎.rec g _ k') (funExt p) ⟩
      _ ≡⟨ recMap k' ⟩
      _ ≡⟨ cong (⊎.rec _ _)
           ( _ ≡⟨ ⊎.elim {C = (λ y → ⊎.mapl _ y ≡ equivFun hh y)} (λ _ → refl) (λ _ → refl) k' ⟩
             _ ≡⟨ sym (FinSumChar.ret _ _ _) ⟩
             _ ≡⟨ cong (FinSumChar.inv _ _)
                  (sym (transportTransport⁻ (cong Fin _) _)) ⟩ _ ∎ ) ⟩  
      _ ≡⟨ sym (lookup-FinSumChar {xs = ys} _) ⟩ _ ∎


_++↔_ : (x y : List A) → x ++ y ↔ y ++ x
x ++↔ [] = ≡→↔ (++-unit-r x)
[] ++↔ y@(_ ∷ _) = ≡→↔ (sym (++-unit-r y) )
(x ∷ xs) ++↔ (y ∷ ys) = 
  isTrans↔ (x ∷ (xs ++ y ∷ ys)) (x ∷ y ∷ ys ++ xs) (y ∷ (ys ++ x ∷ xs))
    (x ∷↔ ((xs ++↔ (y ∷ ys))))
      (isTrans↔ _ _ _ headSwap↔
        (y ∷↔ isTrans↔ _ ((ys ++ [ x ]) ++ xs) (ys ++ x ∷ xs)
         (cong↔++R {ys = ( ys ∷ʳ x)} (isSym↔ ( ys ∷ʳ x) _ (ys ∷↔∷ʳ x)) xs)
         (≡→↔ (++-assoc ys [ x ] xs))))


rev↔ : (xs : List A) → xs ↔ rev xs
rev↔ [] = isRefl↔ []
rev↔ (x ∷ xs) =
  isTrans↔ _ _ (rev xs ++ [ x ])
    (x ∷↔ rev↔ xs) (isSym↔ ((rev xs) ∷ʳ x) _ ((rev xs) ∷↔∷ʳ x))

List/↔ : (A : Type ℓ) → Type ℓ
List/↔ A =  List A / _↔_

pattern []/ = [ [] ]/

_∷/_ : A → List/↔ A → List/↔ A
_∷/_ {A = A} a = SQ.rec squash/ ([_]/ ∘ (a ∷_))
            λ _ _ r → eq/ _ _ (sucPerm (fst r)
             , λ { zero → refl ; (suc _) → snd r _})


List→FMSet : List A → FMSet A
List→FMSet {A = A} = foldr {B = FMSet A} _∷fm_ []fm

h-swap' : (l : List A) → ∀ k
   → List→FMSet l ≡ List→FMSet (permute l (invEquiv (PunchInOut≃ k)))
h-swap' (x ∷ l) zero = cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
h-swap' (x ∷ x₁ ∷ l) one i =
  comm x x₁ (List→FMSet ( (tabulate-lookup l) (~ i))) i 
h-swap' (x ∷ x₁ ∷ l) (suc (suc k)) =
  _ ≡⟨ comm x x₁ _ ⟩
  _ ≡⟨ cong (x₁ ∷fm_) {!!} ⟩
  (x₁ ∷fm List→FMSet (tabulate (suc (length l))
     (lookup (x ∷ x₁ ∷ l) ∘  invEq (swap0and1 ∙ₑ
         (sucPerm (PunchInOut≃ (suc k)))) ∘ suc))) ∎

h-swap : (l : List A) → ∀ k
  → List→FMSet l ≡ List→FMSet (permute l (PunchInOut≃ k))
h-swap (x ∷ l) zero =
  cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
h-swap (x ∷ x₁ ∷ l) one i =
  comm x x₁ (List→FMSet (tabulate-lookup l (~ i))) i
h-swap (x ∷ x₁ ∷ l) (suc (suc k)) =
  cong (x ∷fm_) (h-swap (x₁ ∷ l) (suc k)) ∙ comm _ _ _


lookup-tabulate-lookup : (xs : List A) → ∀ m → ∀ e → ∀ k →   
      lookup xs k ≡ lookup (tabulate m (lookup xs ∘ invEq e))
         (subst Fin (sym (length-tabulate m (lookup xs ∘ invEq e)))
           (equivFun e k))
lookup-tabulate-lookup xs m e k =
     cong (lookup xs) (sym (retEq e k))
   ∙ sym (lookup-tabulateT _ _ (equivFun e k))


↔→FMSet≡ : (a b : List A) → a ↔ b → List→FMSet a ≡ List→FMSet b
↔→FMSet≡ [] [] _ = refl
↔→FMSet≡ [] (_ ∷ _) = ⊥.rec ∘ ¬nil↔cons
↔→FMSet≡ (_ ∷ _) [] = ⊥.rec ∘ ¬cons↔nil
↔→FMSet≡ {A = A} (x ∷ xs) (y ∷ ys) r@(e , _) =  
   let (e' , p') = unwindPermHead e
       k' = equivFun e zero
       xs' = permute xs (invEquiv e')
       (_ , p⁻) = isSym↔ _ _ r
       pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))
   in
      _ ≡⟨ cong (x ∷fm_) (↔→FMSet≡ xs xs' (↔permute xs (invEquiv e'))) ⟩
      _ ≡⟨ h-swap' (x ∷ xs') (subst Fin pL k') ⟩
      _ ≡⟨ cong List→FMSet
          (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
                    (PunchInOut≃∙ₑ≡→Fin≃ pL k')) ⟩
           _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
                           (invEq (PunchInOut≃ k'))  ⟩
           _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
           _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
           _ ≡⟨ tabulate-lookup _ ⟩ (y ∷ ys) ∎
          ) ⟩ _ ∎


IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
IsoList/↔FMSet {A = A} = w
  where

    toFM = SQ.rec trunc List→FMSet ↔→FMSet≡
    
    fromFM = FM.Rec.f squash/
        []/ _∷/_
        λ _ _ → elimProp (λ _ → squash/ _ _)
          λ _ → eq/ _ _ (swap0and1 ,
             λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

    w : Iso _ _
    Iso.fun w = toFM
    Iso.inv w = fromFM
    Iso.rightInv w = 
      FM.ElimProp.f (trunc _ _) refl
        λ a {xs} →
          ((elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
              (λ _ → trunc _ _)
              (λ _ → refl) ∘ fromFM) xs ∙_)
           ∘ cong (_ ∷fm_)

    Iso.leftInv w =
      SQ.elimProp
        (λ x → squash/ _ _)
        (ind refl (cong (_ ∷/_)))


List/↔≃FreeComMonoid : List/↔ A ≃ FreeComMonoid A
List/↔≃FreeComMonoid =
      isoToEquiv IsoList/↔FMSet
   ∙ₑ FMSet≃AssocList
   ∙ₑ AssocList≃FreeComMonoid
