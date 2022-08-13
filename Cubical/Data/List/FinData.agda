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
length-permute l e = length-tabulate _ _


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

headSwap↔ : (x y : A) → ∀ l → x ∷ y ∷ l ↔ y ∷ x ∷ l
headSwap↔ x y l =
  swapHead , λ { zero → refl ; one → refl ; (suc (suc k)) → refl }


_∷↔∷ʳ_ : ∀ xs → (x : A) → xs ∷ʳ x ↔ x ∷ xs
_∷↔∷ʳ_ = ind (isRefl↔ ∘ [_])
  λ x _ → ≡→↔ (++-assoc [ _ ] _ [ _ ]) ∙↔ (_ ∷↔ x _) ∙↔ headSwap↔ _ _ _
 
_↔∷ʳ_ : ∀ {xs ys} → xs ↔ ys → ∀ (a : A) → xs ∷ʳ a ↔ ys ∷ʳ a
_↔∷ʳ_ {xs = xs} {ys} r _ =
  isTrans↔ (xs ∷ʳ _) _ (ys ∷ʳ _) (xs ∷↔∷ʳ _)
   (isTrans↔ _ _ (ys ∷ʳ _) (_ ∷↔ r) (isSym↔ (ys ∷ʳ _) (_ ∷ ys)  (ys ∷↔∷ʳ _)))


lookup-FinSumChar : ∀ {xs ys : List A} →
        ∀ k → lookup (xs ++ ys) k ≡
         ⊎.rec (lookup xs) (lookup ys) (invEq (FinSumChar.Equiv (length xs) (length ys)
            ∙ₑ ≡→Fin≃ (sym (length++ xs ys))) k)
lookup-FinSumChar {xs = []} {ys} k = cong (lookup ys) (sym (transport⁻Transport refl k))
lookup-FinSumChar {xs = x ∷ xs} {ys} zero = 
  cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ (FinSumChar.inv (suc (length xs)) (length ys)))
  (transportFinFix-zero _ ∙ substComposite Fin _ refl zero)

lookup-FinSumChar {xs = x ∷ xs} {ys} (suc k) =  
  lookup-FinSumChar {xs = xs} {ys} k
   ∙ funExt⁻ q (FinSumChar.inv (length xs) (length ys)
        (transp (λ i → Fin (length xs + length ys)) i0
         (transp (λ i → Fin (length++ xs ys i)) i0 k)))
    ∙ cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ FinSumChar.inv (suc (length xs)) (length ys))
        (  sym (cong {B = λ _ → Fin _} suc (substComposite Fin (λ j →  ( (length++ xs ys j))) refl k))  
          ∙ sym (transportFinFix (length++ xs ys ∙ refl) _ k) ∙ substComposite Fin (λ j →  (suc (length++ xs ys j)))
         refl (suc k)) 
  where

      q : ⊎.rec (lookup xs) (lookup ys)
            ≡
            ⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘
            (FinSumChar.invSucAux (length xs) (length ys))
      q i (inl x) = lookup xs x
      q i (inr x) = lookup ys x


cong↔++R : ∀ {xs ys : List A} → xs ↔ ys → ∀ l → xs ++ l ↔ ys ++ l
fst (cong↔++R {xs = xs} {ys} x l) =
  ≡→Fin≃ (length++ xs l) ∙ₑ
    (invEquiv (FinSumChar.Equiv (length xs) (length l))
     ∙ₑ ⊎-equiv (fst x) (idEquiv _)
     ∙ₑ FinSumChar.Equiv (length ys) (length l) )
   ∙ₑ ≡→Fin≃ (sym (length++ ys l))
snd (cong↔++R {A = A} {xs = xs} {ys} x l) k =
  lookup-FinSumChar {xs = xs} {l} k ∙
   (λ i → ⊎.rec (λ k' → snd x k' i) (lookup l) (invEq
       (FinSumChar.Equiv (length xs) (length l) ∙ₑ
        ≡→Fin≃ (sym (length++ xs l)))
       k))
   ∙ sym (recMap (equivFun (fst x)) (lookup ys) (idfun _) (lookup l)
      (invEq
       (FinSumChar.Equiv (length xs) (length l) ∙ₑ ≡→Fin≃ (sym (length++ xs l))) k))
   ∙ cong (⊎.rec (lookup ys) (lookup l))
      (h (transp (λ j → Fin (length++ xs l j)) i0 k))
   ∙ sym (lookup-FinSumChar {xs = ys} {l} _)
  where
    h : (k : Fin (length xs + length l)) →           
         ⊎.map (fst (fst x)) (λ x₁ → x₁)
         (FinSumChar.inv (length xs) (length l)
          (transp (λ i → Fin (length xs + length l)) i0
           (k)))
         ≡
         FinSumChar.inv (length ys) (length l)
         (transp (λ i → Fin (length ys + length l)) i0
          (transp (λ j → Fin (length++ ys l j)) i0
           (transp (λ i → Fin (length++ ys l (~ i))) i0
            (FinSumChar.fun (length ys) (length l)
             (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
              .Iso.fun
              (FinSumChar.inv (length xs) (length l)
               k))))))
    h k =
         cong (⊎.map (fst (fst x)) (λ x₁ → x₁) ∘ (FinSumChar.inv (length xs) (length l)))
           (transportRefl k)
      ∙  (⊎.elim
           {C = (λ y → ⊎.map (fst (fst x)) (λ x₁ → x₁) y ≡
                  ⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
                      .Iso.fun y)}
           (λ _ → refl) (λ _ → refl)
          (FinSumChar.inv (length xs) (length l) k)) 
      ∙ sym (FinSumChar.ret (length ys) (length l) _)
      ∙ cong (FinSumChar.inv (length ys) (length l))
            (sym (transportRefl (FinSumChar.fun (length ys) (length l)
        (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
         .Iso.fun (FinSumChar.inv (length xs) (length l) k)))))
      ∙ cong (FinSumChar.inv (length ys) (length l)
           ∘ transp (λ i → Fin (length ys + length l)) i0)
            (sym (transportTransport⁻ (cong Fin (length++ ys l))
              (FinSumChar.fun (length ys) (length l)
             (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
              .Iso.fun
              (FinSumChar.inv (length xs) (length l)
               k)))))
 
_++↔_ : (x y : List A) → x ++ y ↔ y ++ x
x ++↔ [] = ≡→↔ (++-unit-r x)
[] ++↔ y@(_ ∷ _) = ≡→↔ (sym (++-unit-r y) )
(x ∷ xs) ++↔ (y ∷ ys) = 
  isTrans↔ (x ∷ (xs ++ y ∷ ys)) (x ∷ y ∷ ys ++ xs) (y ∷ (ys ++ x ∷ xs))
    (x ∷↔ ((xs ++↔ (y ∷ ys))))
      (isTrans↔ _ _ _ (headSwap↔ x y (ys ++ xs))
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

h-swap : (l : List A) → ∀ k → List→FMSet l ≡ List→FMSet (permute l (PunchInOut≃ k))
h-swap (x ∷ l) zero = cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
h-swap (x ∷ x₁ ∷ l) one i = comm x x₁ (List→FMSet (tabulate-lookup l (~ i))) i
h-swap (x ∷ x₁ ∷ l) (suc (suc k)) = cong (x ∷fm_) (h-swap (x₁ ∷ l) (suc k)) ∙ comm _ _ _

↔→FMSet≡ : (a b : List A) → a ↔ b → List→FMSet a ≡ List→FMSet b
↔→FMSet≡ a b r =  h (length a) a b refl (sym (↔→length≡ {x = a} {y = b} r)) r
 where
  h : ∀ n → (a b : List A) → length a ≡ n → length b ≡ n →
         a ↔ b → List→FMSet a ≡ List→FMSet b
  h zero [] [] x x₁ x₂ = refl
  h zero [] (x₃ ∷ b) x x₁ x₂ = ⊥.rec (ℕsnotz x₁)
  h zero (x₃ ∷ a) _ x x₁ x₂ = ⊥.rec (ℕsnotz x)
  h (suc n) [] b x x₁ x₂ = ⊥.rec (ℕznots x)
  h (suc n) (x₃ ∷ a) [] x x₁ x₂ = ⊥.rec (ℕznots x₁)
  h (suc n) (x ∷ xs) (y ∷ ys) pX pY ro@(e , p) =
    let (e' , p') = Fin≃SucEquiv'' e
        y' = lookup (y ∷ ys) (equivFun (PunchInOut≃ (equivFun e zero)) zero)
        ys' = tabulate (length xs)
                 (lookup (y ∷ ys) ∘ 
                    (equivFun (sucPerm e' ∙ₑ PunchInOut≃ (equivFun e zero))) ∘ suc)

    in cong List→FMSet (sym (tabulate-lookup (x ∷ xs)) ∙
            cong (tabulate _) (funExt p ∙ cong (lookup (y ∷ ys) ∘_) (cong equivFun p')))
         ∙∙
         cong (y' ∷fm_)
         (h n ys' (permute ys' (invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _))))
           (length-tabulate _ _ ∙ injSuc pX) (length-tabulate (length ys) _ ∙ sym (isInjectiveFin≃ e')
              ∙ injSuc pX)
           (↔permute ys' ((invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _)))))
           ∙ cong (List→FMSet ∘ tabulate (length ys))
             (cong (_∘ invEq e') (funExt (lookup-tabulateT _ _)) ∙
              cong (((
                 lookup (y ∷ ys) ∘ 
                  (equivFun (PunchInOut≃ (equivFun e zero))) ∘  suc) ∘_) ∘ fst) ((invEquiv-is-linv e'))))
          ∙∙
           sym (h-swap (y ∷ ys) (equivFun e zero))


IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
IsoList/↔FMSet {A = A} = w
  where

    toFM : _
    toFM = SQ.rec trunc List→FMSet ↔→FMSet≡      

    fromFM : _
    fromFM = FM.Rec.f squash/
        []/ _∷/_
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
