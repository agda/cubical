
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.List as L
open import Cubical.Data.FinData
open import Cubical.Data.List.FinData
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ hiding (map)
open import Cubical.Data.Maybe
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Nat
import Cubical.Data.Sigma as Σ

module Cubical.Data.List.Dependent where

open _≅_

module ListDep {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) where
 data ListP  : (as : List A) → Type (ℓ-max ℓA ℓB) where
   [] : ListP []
   _∷_ : {x : A} (y : B x) {xs : List A} (ys : ListP xs) → ListP (x ∷ xs)

 infixr 5 _∷_

 pattern P[_] x = x ∷ []

 -- Represent ListP via known operations in order to derive properties more easily.
 RepListP : (as : List A) → Type ℓB
 RepListP [] = Lift _ Unit
 RepListP (a ∷ as) = B a × RepListP as

 isoRepListP : (as : List A) → ListP as ≅ RepListP as
 fun (isoRepListP []) bs = lift tt
 inv (isoRepListP []) u = []
 sec (isoRepListP []) u = refl
 ret (isoRepListP []) [] = refl
 fun (isoRepListP (a ∷ as)) (b ∷ bs) = b , fun (isoRepListP as) bs
 inv (isoRepListP (a ∷ as)) (b , br) = b ∷ inv (isoRepListP as) br
 sec (isoRepListP (a ∷ as)) (b , br) i = b , sec (isoRepListP as) br i
 ret (isoRepListP (a ∷ as)) (b ∷ bs) i = b ∷ ret (isoRepListP as) bs i

 equivRepListP : (as : List A) → ListP as ≃ RepListP as
 equivRepListP as = isoToEquiv (isoRepListP as)

 pathRepListP : (as : List A) → ListP as ≡ Lift ℓA (RepListP as)
 pathRepListP as = ua (equivRepListP as ∙ₑ LiftEquiv {A = RepListP as})

 ΣList→ListΣ : Σ _ ListP → List (Σ A B)
 ΣList→ListΣ (_ , []) = []
 ΣList→ListΣ (_ , y ∷ ys) = (_ , y) ∷ ΣList→ListΣ (_ , ys)

 ListΣ→ΣList : List (Σ A B) → Σ _ ListP
 ListΣ→ΣList [] = _ , []
 ListΣ→ΣList ((_ , x) ∷ xs) = _ , (x ∷ snd (ListΣ→ΣList xs) )

 IsoListΣListDep : (Σ _ ListP) ≅ List (Σ A B)
 IsoListΣListDep .fun = ΣList→ListΣ
 IsoListΣListDep .inv = ListΣ→ΣList
 IsoListΣListDep .sec = L.elim refl (cong (_ ∷_))
 IsoListΣListDep .ret =
   uncurry (L.elim (λ { [] → refl})
     λ a → λ { (y ∷ ys) i → _ , y ∷ a ys i .snd })

module ListDepSum {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) where
 data ⊎ᵢ  : (as : List A) → Type (ℓ-max ℓA ℓB) where

   inj₀ : {x : A} (y : B x) {xs : List A} → ⊎ᵢ (x ∷ xs)
   inj₊ : {x : A} {xs : List A} (ys : ⊎ᵢ xs) → ⊎ᵢ (x ∷ xs)

 --------------------------

 -- Represent ListP via known operations in order to derive properties more easily.
 Rep⊎ᵢ : (as : List A) → Type ℓB
 Rep⊎ᵢ [] = ⊥*
 Rep⊎ᵢ (a ∷ as) = B a ⊎ Rep⊎ᵢ as

 isoRep⊎ᵢ : (as : List A) → ⊎ᵢ as ≅ Rep⊎ᵢ as
 isoRep⊎ᵢ _ .fun (inj₀ y) = inl y
 isoRep⊎ᵢ _ .fun (inj₊ x) = inr (isoRep⊎ᵢ _ .fun x)
 isoRep⊎ᵢ (_ ∷ _) .inv (inl x) = inj₀ x
 isoRep⊎ᵢ (_ ∷ _) .inv (inr x) = inj₊ (isoRep⊎ᵢ _ .inv x)
 isoRep⊎ᵢ (_ ∷ _) .sec (inl x) = refl
 isoRep⊎ᵢ (_ ∷ _) .sec (inr x) = cong inr (isoRep⊎ᵢ _ .sec x)
 isoRep⊎ᵢ _ .ret (inj₀ y) = refl
 isoRep⊎ᵢ _ .ret (inj₊ a) = cong inj₊ (isoRep⊎ᵢ _ .ret a)

 equivRep⊎ᵢ : (as : List A) → ⊎ᵢ as ≃ Rep⊎ᵢ as
 equivRep⊎ᵢ as = isoToEquiv (isoRep⊎ᵢ as)

 pathRep⊎ᵢ : (as : List A) → ⊎ᵢ as ≡ Lift ℓA (Rep⊎ᵢ as)
 pathRep⊎ᵢ as = ua (equivRep⊎ᵢ as ∙ₑ LiftEquiv {A = Rep⊎ᵢ as})


module _ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} where
 open ListDep B
 open ListDepSum B

 _++P_ : ∀ {xs ys} → ListP xs → ListP ys → ListP (xs ++ ys)
 ListDep.[] ++P ys = ys
 (y ListDep.∷ x) ++P ys = y ListDep.∷ (x ++P ys)

 splitP : ∀ {xs ys} → ListP (xs ++ ys) → (ListP xs Σ.× ListP ys)
 splitP {[]} = [] ,_
 splitP {x ∷ xs} (y ∷ ys) = Σ.map-fst (y ∷_) (splitP {xs} ys)

 split++-sec :  ∀ {xs ys} → section (splitP {xs} {ys}) (uncurry _++P_)
 split++-sec (ListDep.[] , _) = refl
 split++-sec (x ListDep.∷ xs , ys) = cong (Σ.map-fst (x ∷_)) (split++-sec (xs , ys))

 split++-ret :  ∀ {xs ys} → retract (splitP {xs} {ys}) (uncurry _++P_)
 split++-ret {[]} _ = refl
 split++-ret {x ∷ xs} (y ListDep.∷ ys) = cong (y ∷_) (split++-ret {xs} ys)

 split++Iso : ∀ {xs ys} → (ListP (xs ++ ys)) ≅ (ListP xs Σ.× ListP ys)
 split++Iso .fun = splitP
 split++Iso .inv = uncurry _++P_
 split++Iso .sec = split++-sec
 split++Iso {xs} .ret = split++-ret {xs}

 split++Equiv : ∀ {xs ys} → (ListP (xs ++ ys)) ≃ (ListP xs Σ.× ListP ys)
 split++Equiv = isoToEquiv split++Iso


 iX : ∀ {xs} → ⊎ᵢ xs → A
 iX {x ∷ _} (ListDepSum.inj₀ _) = x
 iX {_ ∷ xs} (ListDepSum.inj₊ x) = iX {xs} x

open ListDep public
open ListDepSum public


private
  isOfHLevelSucSuc-RepListP : ∀ {ℓA ℓB} (n : HLevel)
    → {A : Type ℓA}
    → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
    → (as : List A)
    → isOfHLevel (suc (suc n)) (RepListP B as)
  isOfHLevelSucSuc-RepListP n isHB [] = isOfHLevelLift (suc (suc n)) (isOfHLevelUnit (suc (suc n)))
  isOfHLevelSucSuc-RepListP n isHB (a ∷ as) = isOfHLevelProd (suc (suc n)) (isHB a) (isOfHLevelSucSuc-RepListP n isHB as)

isOfHLevelSucSuc-ListP : ∀ {ℓA ℓB} (n : HLevel)
  → {A : Type ℓA}
  → {B : A → Type ℓB} → ((a : A) → isOfHLevel (suc (suc n)) (B a))
  → {as : List A}
  → isOfHLevel (suc (suc n)) (ListP B as)
isOfHLevelSucSuc-ListP n {A} {B} isHB {as} =
  isOfHLevelRespectEquiv (suc (suc n)) (invEquiv (equivRepListP _ _)) (isOfHLevelSucSuc-RepListP n isHB as)
--------------------------

lookupP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as} (bs : ListP B as) → (p : Fin (length as)) → B (lookup as p)
lookupP (b ∷ bs) zero = b
lookupP (b ∷ bs) (suc p) = lookupP bs p

{- It seems sensible to reserve the name tabulateP for a function that mentions tabulate (rather than lookup) in its type.
-}
tabulateOverLookup : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} as (^b : (p : Fin (length as)) → B (lookup as p))
  → ListP B as
tabulateOverLookup [] ^b = []
tabulateOverLookup (a ∷ as) ^b = ^b zero ∷ tabulateOverLookup as (^b ∘ suc)

tabulateOverLookup-lookupP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as} (bs : ListP B as) →
  tabulateOverLookup as (lookupP bs) ≡ bs
tabulateOverLookup-lookupP [] = refl
tabulateOverLookup-lookupP (b ∷ bs) = cong (b ∷_) (tabulateOverLookup-lookupP bs)

lookupP-tabulateOverLookup : ∀ {ℓA ℓB} {A : Type ℓA} (B : A → Type ℓB) as (^b : (p : Fin (length as)) → B (lookup as p))
  → lookupP (tabulateOverLookup {B = B} as ^b) ≡ ^b
lookupP-tabulateOverLookup B (a ∷ as) ^b i zero = ^b zero
lookupP-tabulateOverLookup B (a ∷ as) ^b i (suc p) = lookupP-tabulateOverLookup B as (^b ∘ suc) i p

--------------------------

mapP : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (f : A → A') (g : (a : A) → B a → B' (f a)) → ∀ as → ListP B as → ListP B' (map f as)
mapP f g [] [] = []
mapP f g (a ∷ as) (b ∷ bs) = g _ b ∷ mapP f g as bs

mapOverIdfun : ∀ {ℓA ℓB ℓB'} {A : Type ℓA} {B : A → Type ℓB} {B' : A → Type ℓB'}
  (g : (a : A) → B a → B' a) → ∀ as → ListP B as → ListP B' as
mapOverIdfun g [] [] = []
mapOverIdfun g (a ∷ as) (b ∷ bs) = g a b ∷ mapOverIdfun g as bs

mapOverIdfun-idfun : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} as → mapOverIdfun (λ a → idfun _) as ≡ (idfun (ListP B as))
mapOverIdfun-idfun [] i [] = []
mapOverIdfun-idfun (a ∷ as) i (b ∷ bs) = b ∷ mapOverIdfun-idfun as i bs

mapOverIdfun-∘ : ∀ {ℓA ℓB ℓB' ℓB''} {A : Type ℓA} {B : A → Type ℓB} {B' : A → Type ℓB'} {B'' : A → Type ℓB''}
  (h : (a : A) → B' a → B'' a) (g : (a : A) → B a → B' a) → ∀ as
  → mapOverIdfun (λ a → h a ∘ g a) as ≡ mapOverIdfun h as ∘ mapOverIdfun g as
mapOverIdfun-∘ h g [] i [] = []
mapOverIdfun-∘ h g (a ∷ as) i (b ∷ bs) = h a (g a b) ∷ mapOverIdfun-∘ h g as i bs

mapOverSpan : ∀ {ℓI ℓA ℓA' ℓB ℓB'} {I : Type ℓI} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'}
  (f : I → A) (f' : I → A') (g : ∀ i → B (f i) → B' (f' i)) → ∀ is → ListP B (map f is) → ListP B' (map f' is)
mapOverSpan f f' g [] [] = []
mapOverSpan f f' g (i ∷ is) (b ∷ bs) = g i b ∷ mapOverSpan f f' g is bs

mapOverSpan-idfun : ∀ {ℓI ℓA ℓB} {I : Type ℓI} {A : Type ℓA} {B : A → Type ℓB}
  (f : I → A) → ∀ is → mapOverSpan {B = B} f f (λ i a → a) is ≡ idfun _
mapOverSpan-idfun f [] j [] = []
mapOverSpan-idfun f (i ∷ is) j (b ∷ bs) = b ∷ mapOverSpan-idfun f is j bs

mapOverSpan-∘ : ∀ {ℓI ℓA ℓA' ℓA'' ℓB ℓB' ℓB''}
  {I : Type ℓI}
  {A : Type ℓA} {A' : Type ℓA'} {A'' : Type ℓA''}
  {B : A → Type ℓB} {B' : A' → Type ℓB'} {B'' : A'' → Type ℓB''}
  (f : I → A) (f' : I → A') (f'' : I → A'')
  (g1 : ∀ i → B (f i) → B' (f' i)) →
  (g2 : ∀ i → B' (f' i) → B'' (f'' i)) →
  ∀ is → mapOverSpan f f'' (λ i → g2 i ∘ g1 i) is ≡
          mapOverSpan {B = B'} {B' = B''} f' f'' g2 is ∘ mapOverSpan {B = B} f f' g1 is
mapOverSpan-∘ f f' f'' g1 g2 [] j [] = []
mapOverSpan-∘ {B' = B'} f f' f'' g1 g2 (i ∷ is) j (b ∷ bs) =
  g2 i (g1 i b) ∷ mapOverSpan-∘ {B' = B'} f f' f'' g1 g2 is j bs

mapOverSpan∘Idfun : ∀ {ℓI ℓA ℓA'' ℓB ℓB' ℓB''}
  {I : Type ℓI}
  {A : Type ℓA} {A'' : Type ℓA''}
  {B : A → Type ℓB} {B' : A → Type ℓB'} {B'' : A'' → Type ℓB''}
  (f' : I → A) (f'' : I → A'')
  (g1 : ∀ a → B a → B' a )
  (g2 : ∀ i → B' (f' i) → B'' (f'' i)) →
  ∀ is → mapOverSpan {B = B} {B' = B''} f' f'' (λ i → g2 i ∘ g1 (f' i)) is ≡
          mapOverSpan {B = B'} f' f'' g2 is ∘ mapOverIdfun g1 (map f' is)
mapOverSpan∘Idfun f' f'' g1 g2 [] j [] = []
mapOverSpan∘Idfun f' f'' g1 g2 (i ∷ is) j (b ∷ bs) =
  g2 i (g1 (f' i) b) ∷ mapOverSpan∘Idfun f' f'' g1 g2 is j bs

fromConst : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} {xs} → ListP {A = A} (λ _ → B) xs → List B
fromConst [] = []
fromConst (x ∷ xs) = x ∷ fromConst xs

lengthP : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} {xs} → ListP {A = A} (λ _ → B) xs → ℕ
lengthP {xs = xs} _ = length xs



private
 variable
  ℓA ℓB ℓC : Level
  A A' : Type ℓA
  B C : A → Type ℓB


IsoListDepFunFun⊎ᵢ : (as : List A) → ((x : ⊎ᵢ B as) → C (iX x)) ≅ ListP (λ a → (B a → C a)) as
IsoListDepFunFun⊎ᵢ [] .fun _ = []
IsoListDepFunFun⊎ᵢ (x ∷ xs) .fun y =
 (λ b → y (inj₀ b)) ∷ IsoListDepFunFun⊎ᵢ xs .fun (y ∘ inj₊)
IsoListDepFunFun⊎ᵢ [] .inv _ ()
IsoListDepFunFun⊎ᵢ (x ∷ xs) .inv (y ∷ ys) (inj₀ b) = y b
IsoListDepFunFun⊎ᵢ (x ∷ xs) .inv (y ∷ ys) (inj₊ b) =
  IsoListDepFunFun⊎ᵢ xs .inv ys b
IsoListDepFunFun⊎ᵢ [] .sec [] = refl
IsoListDepFunFun⊎ᵢ (x ∷ as) .sec (y ∷ b) i = y ∷ IsoListDepFunFun⊎ᵢ as .sec b i
IsoListDepFunFun⊎ᵢ [] .ret a i ()
IsoListDepFunFun⊎ᵢ (x ∷ as) .ret a i (inj₀ y) = a (inj₀ y)
IsoListDepFunFun⊎ᵢ {C = C} (x ∷ as) .ret a i (inj₊ x₁) =
  IsoListDepFunFun⊎ᵢ {C = C} as .ret (a ∘ inj₊) i x₁

elimTail : ∀ {a} {as : List A} → (⊎ᵢ B (a ∷ as)) → ListP (λ a → B a → ⊥) as  → B a
elimTail {as = []} (inj₀ y) _ = y
elimTail {as = _ ∷ _} (inj₀ y) x₁ = y
elimTail {as = _ ∷ _} (inj₊ (inj₀ y)) (¬Ba' ∷ _) = ⊥.rec (¬Ba' y)
elimTail {as = _ ∷ _} (inj₊ (inj₊ x)) (¬Ba' ∷ x₁) = elimTail (inj₊ x) x₁
