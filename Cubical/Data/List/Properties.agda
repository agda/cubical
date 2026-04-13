module Cubical.Data.List.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sum as ⊎ hiding (map)
open import Cubical.Data.Unit
open import Cubical.Data.List.Base as List

open import Cubical.Relation.Nullary

module _ {ℓ} {A : Type ℓ} where

  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-r [] = refl
  ++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  rev-snoc : (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ y ∷ rev xs
  rev-snoc [] y = refl
  rev-snoc (x ∷ xs) y = cong (_++ [ x ]) (rev-snoc xs y)

  rev-++ : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
  rev-++ [] ys = sym (++-unit-r (rev ys))
  rev-++ (x ∷ xs) ys =
    cong (λ zs → zs ++ [ x ]) (rev-++ xs ys)
    ∙ ++-assoc (rev ys) (rev xs) [ x ]

  rev-rev : (xs : List A) → rev (rev xs) ≡ xs
  rev-rev [] = refl
  rev-rev (x ∷ xs) = rev-snoc (rev xs) x ∙ cong (_∷_ x) (rev-rev xs)

  rev-rev-snoc : (xs : List A) (y : A) →
    Square (rev-rev (xs ++ [ y ])) (cong (_++ [ y ]) (rev-rev xs)) (cong rev (rev-snoc xs y)) refl
  rev-rev-snoc [] y = sym (lUnit refl)
  rev-rev-snoc (x ∷ xs) y i j =
    hcomp
      (λ k → λ
        { (i = i1) → compPath-filler (rev-snoc (rev xs) x) (cong (x ∷_) (rev-rev xs)) k j ++ [ y ]
        ; (j = i0) → rev (rev-snoc xs y i ++ [ x ])
        ; (j = i1) → x ∷ rev-rev-snoc xs y i k
        })
      (rev-snoc (rev-snoc xs y i) x j)

  data SnocView : List A → Type ℓ where
    nil : SnocView []
    snoc : (x : A) → (xs : List A) → (sx : SnocView xs) → SnocView (xs ∷ʳ x)

  snocView : (xs : List A) → SnocView xs
  snocView xs = helper nil xs
    where
    helper : {l : List A} -> SnocView l -> (r : List A) -> SnocView (l ++ r)
    helper {l} sl [] = subst SnocView (sym (++-unit-r l)) sl
    helper {l} sl (x ∷ r) = subst SnocView (++-assoc l (x ∷ []) r) (helper (snoc x l sl) r)

-- Path space of list type
module ListPath {ℓ} {A : Type ℓ} where

  Cover : List A → List A → Type ℓ
  Cover [] [] = Unit*
  Cover [] (_ ∷ _) = ⊥*
  Cover (_ ∷ _) [] = ⊥*
  Cover (x ∷ xs) (y ∷ ys) = (x ≡ y) × Cover xs ys

  reflCode : ∀ xs → Cover xs xs
  reflCode [] = lift tt
  reflCode (_ ∷ xs) = refl , reflCode xs

  encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
  encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

  encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
  encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode [] [] _ = refl
  decode [] (_ ∷ _) (lift ())
  decode (x ∷ xs) [] (lift ())
  decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
  decodeRefl [] = refl
  decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

  decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs _ =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)
    (xs ys : List A) → isOfHLevel (suc n) (Cover xs ys)
  isOfHLevelCover n p [] [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isPropUnit)
  isOfHLevelCover n p [] (y ∷ ys) =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) (y ∷ ys) =
    isOfHLevelΣ (suc n) (p x y) (\ _ → isOfHLevelCover n p xs ys)

isOfHLevelList : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (List A)
isOfHLevelList n ofLevel xs ys =
  isOfHLevelRetract (suc n)
    (ListPath.encode xs ys)
    (ListPath.decode xs ys)
    (ListPath.decodeEncode xs ys)
    (ListPath.isOfHLevelCover n ofLevel xs ys)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'
    x y : A
    xs ys : List A

caseList : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (n c : B) → List A → B
caseList n _ []      = n
caseList _ c (_ ∷ _) = c

safe-head : A → List A → A
safe-head x []      = x
safe-head _ (x ∷ _) = x

safe-tail : List A → List A
safe-tail []       = []
safe-tail (_ ∷ xs) = xs

cons-inj₁ : x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ {x = x} p = cong (safe-head x) p

cons-inj₂ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ = cong safe-tail

snoc-inj₂ : xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
snoc-inj₂ {xs = xs} {ys = ys} p =
 cons-inj₁ ((sym (rev-++ xs _)) ∙∙ cong rev p ∙∙ (rev-++ ys _))

snoc-inj₁ : xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
snoc-inj₁ {xs = xs} {ys = ys} p =
   sym (rev-rev _) ∙∙ cong rev (cons-inj₂ ((sym (rev-++ xs _)) ∙∙ cong rev p ∙∙ (rev-++ ys _)))
        ∙∙ rev-rev _

¬cons≡nil : ¬ (x ∷ xs ≡ [])
¬cons≡nil p = lower (ListPath.encode _ _ p)

¬nil≡cons : ¬ ([] ≡ x ∷ xs)
¬nil≡cons p = lower (ListPath.encode _ _ p)

¬snoc≡nil : ¬ (xs ∷ʳ x ≡ [])
¬snoc≡nil {xs = []} contra = ¬cons≡nil contra
¬snoc≡nil {xs = x ∷ xs} contra = ¬cons≡nil contra

¬nil≡snoc : ¬ ([] ≡ xs ∷ʳ x)
¬nil≡snoc contra = ¬snoc≡nil (sym contra)

cons≡rev-snoc : (x : A) → (xs : List A) → x ∷ rev xs ≡ rev (xs ∷ʳ x)
cons≡rev-snoc _ [] = refl
cons≡rev-snoc x (y ∷ ys) = λ i → cons≡rev-snoc x ys i ++ y ∷ []

isContr[]≡[] : isContr (Path (List A) [] [])
isContr[]≡[] = refl , ListPath.decodeEncode [] []

isPropXs≡[] : isProp (xs ≡ [])
isPropXs≡[] {xs = []} = isOfHLevelSuc 0 isContr[]≡[]
isPropXs≡[] {xs = x ∷ xs} = λ p _ → ⊥.rec (¬cons≡nil p)

discreteList : Discrete A → Discrete (List A)
discreteList eqA []       []       = yes refl
discreteList eqA []       (y ∷ ys) = no ¬nil≡cons
discreteList eqA (x ∷ xs) []       = no ¬cons≡nil
discreteList eqA (x ∷ xs) (y ∷ ys) with eqA x y | discreteList eqA xs ys
... | yes p | yes q = yes (λ i → p i ∷ q i)
... | yes _ | no ¬q = no (λ p → ¬q (cons-inj₂ p))
... | no ¬p | _     = no (λ q → ¬p (cons-inj₁ q))

foldrCons : (xs : List A) → foldr _∷_ [] xs ≡ xs
foldrCons [] = refl
foldrCons (x ∷ xs) = cong (x ∷_) (foldrCons xs)

length-map : (f : A → B) → (as : List A)
  → length (map f as) ≡ length as
length-map f [] = refl
length-map f (a ∷ as) = cong suc (length-map f as)

map++ : (f : A → B) → (as bs : List A)
   → map f as ++ map f bs ≡ map f (as ++ bs)
map++ f [] bs = refl
map++ f (x ∷ as) bs = cong (f x ∷_) (map++ f as bs)

rev-map-comm : (f : A → B) → (as : List A)
  → map f (rev as) ≡ rev (map f as)
rev-map-comm f [] = refl
rev-map-comm f (x ∷ as) =
 sym (map++ f (rev as) _) ∙ cong (_++ [ f x ]) (rev-map-comm f as)

length++ : (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length++ [] ys = refl
length++ (x ∷ xs) ys = cong suc (length++ xs ys)

drop++ : ∀ (xs ys : List A) k →
   drop (length xs + k) (xs ++ ys) ≡ drop k ys
drop++ [] ys k = refl
drop++ (x ∷ xs) ys k = drop++ xs ys k

dropLength++ : (xs : List A) → drop (length xs) (xs ++ ys) ≡ ys
dropLength++ {ys = ys} xs =
  cong (flip drop (xs ++ ys)) (sym (+-zero (length xs))) ∙ drop++ xs ys 0


dropLength : (xs : List A) → drop (length xs) xs ≡ []
dropLength xs =
    cong (drop (length xs)) (sym (++-unit-r xs))
  ∙ dropLength++ xs


take++ : ∀ (xs ys : List A) k → take (length xs + k) (xs ++ ys) ≡ xs ++ take k ys
take++ [] ys k = refl
take++ (x ∷ xs) ys k = cong (_ ∷_) (take++ _ _ k)


takeLength++ : ∀ ys → take (length xs) (xs ++ ys) ≡ xs
takeLength++ {xs = xs} ys =
      cong (flip take (xs ++ ys)) (sym (+-zero (length xs)))
   ∙∙ take++ xs ys 0
   ∙∙ ++-unit-r xs

takeLength : take (length xs) xs ≡ xs
takeLength = cong (take _) (sym (++-unit-r _)) ∙ takeLength++ []

map-∘ : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
        (g : B → C) (f : A → B) (as : List A)
        → map g (map f as) ≡ map (λ x → g (f x)) as
map-∘ g f [] = refl
map-∘ g f (x ∷ as) = cong (_ ∷_) (map-∘ g f as)

map-id : (as : List A) → map (λ x → x) as ≡ as
map-id [] = refl
map-id (x ∷ as) = cong (_ ∷_) (map-id as)

length≡0→≡[] : ∀ (xs : List A) → length xs ≡ 0 → xs ≡ []
length≡0→≡[] [] x = refl
length≡0→≡[] (x₁ ∷ xs) x = ⊥.rec (snotz x)

init : List A → List A
init [] = []
init (x ∷ []) = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs

tail : List A → List A
tail [] = []
tail (x ∷ xs) = xs

init-red-lem : ∀ (x : A) xs → ¬ (xs ≡ []) → (x ∷ init xs) ≡ (init (x ∷ xs))
init-red-lem x [] x₁ = ⊥.rec (x₁ refl)
init-red-lem x (x₂ ∷ xs) x₁ = refl

init∷ʳ : init (xs ∷ʳ x) ≡ xs
init∷ʳ {xs = []} = refl
init∷ʳ {xs = _ ∷ []} = refl
init∷ʳ {xs = _ ∷ _ ∷ _} = cong (_ ∷_) init∷ʳ

tail∷ʳ : tail (xs ∷ʳ y) ∷ʳ x ≡ tail (xs ∷ʳ y ∷ʳ x)
tail∷ʳ {xs = []} = refl
tail∷ʳ {xs = x ∷ xs} = refl

init-rev-tail : rev (init xs) ≡ tail (rev xs)
init-rev-tail {xs = []} = refl
init-rev-tail {xs = x ∷ []} = refl
init-rev-tail {xs = x ∷ y ∷ xs} =
   cong (_∷ʳ x) (init-rev-tail {xs = y ∷ xs})
 ∙ tail∷ʳ {xs = rev xs}

init++ : ∀ xs → xs ++ init (x ∷ ys) ≡ init (xs ++ x ∷ ys)
init++ [] = refl
init++ (_ ∷ []) = refl
init++ (_ ∷ _ ∷ _) = cong (_ ∷_) (init++ (_ ∷ _))

Split++ : (xs ys xs' ys' zs : List A) → Type _
Split++ xs ys xs' ys' zs = ((xs ++ zs ≡ xs') × (ys ≡ zs ++ ys'))

split++ : ∀ (xs' ys' xs ys : List A) → xs' ++ ys' ≡ xs ++ ys →
              Σ _ λ zs →
                ((Split++ xs' ys' xs ys zs)
                ⊎ (Split++ xs ys xs' ys' zs))
split++ [] ys' xs ys x = xs , inl (refl , x)
split++ xs'@(_ ∷ _) ys' [] ys x = xs' , inr (refl , sym x)
split++ (x₁ ∷ xs') ys' (x₂ ∷ xs) ys x =
 let (zs , q) = split++ xs' ys' xs ys (cons-inj₂ x)
     p = cons-inj₁ x
 in zs , ⊎.map (map-fst (λ q i → p    i  ∷ q i))
               (map-fst (λ q i → p (~ i) ∷ q i)) q

repeat : ℕ → A → List A
repeat zero _ = []
repeat (suc k) x = x ∷ repeat k x

rot : List A → List A
rot [] = []
rot (x ∷ xs) = xs ∷ʳ x

take[] : ∀ n → take {A = A} n [] ≡ []
take[] zero = refl
take[] (suc n) = refl

drop[] : ∀ n → drop {A = A} n [] ≡ []
drop[] zero = refl
drop[] (suc n) = refl

lookupAlways : A → List A → ℕ → A
lookupAlways a [] _ = a
lookupAlways _ (x ∷ _) zero = x
lookupAlways a (x ∷ xs) (suc k) = lookupAlways a xs k

lookupMb : List A → ℕ → Maybe A
lookupMb = lookupAlways nothing ∘S map just

offset : A → ℕ →  List A → List A
offset a n xs = repeat (substLen n xs) a ++ xs
 where
 substLen : ℕ → List A → ℕ
 substLen zero _ = zero
 substLen k@(suc _) [] = k
 substLen (suc k) (_ ∷ xs) = substLen k xs

offsetR : A → ℕ →  List A → List A
offsetR a zero xs = xs
offsetR a (suc n) [] = repeat (suc n) a
offsetR a (suc n) (x ∷ xs) = x ∷ offsetR a n xs

module List₂ where
 open import Cubical.HITs.SetTruncation renaming
   (rec to rec₂ ; map to map₂ ; elim to elim₂ )

 ∥List∥₂→List∥∥₂ : ∥ List A ∥₂ → List ∥ A ∥₂
 ∥List∥₂→List∥∥₂ = rec₂ (isOfHLevelList 0 squash₂) (map ∣_∣₂)

 List∥∥₂→∥List∥₂ : List ∥ A ∥₂ → ∥ List A ∥₂
 List∥∥₂→∥List∥₂ [] = ∣ [] ∣₂
 List∥∥₂→∥List∥₂ (x ∷ xs) =
   rec2 squash₂ (λ x xs → ∣ x ∷ xs ∣₂) x (List∥∥₂→∥List∥₂ xs)

 Iso∥List∥₂List∥∥₂ : Iso (List ∥ A ∥₂) ∥ List A ∥₂
 Iso.fun Iso∥List∥₂List∥∥₂ = List∥∥₂→∥List∥₂
 Iso.inv Iso∥List∥₂List∥∥₂ = ∥List∥₂→List∥∥₂
 Iso.sec Iso∥List∥₂List∥∥₂ =
   elim₂ (isProp→isSet ∘ λ _ → squash₂ _ _)
     (List.elim refl (cong (rec2 squash₂ (λ x₁ xs → ∣ x₁ ∷ xs ∣₂) ∣ _ ∣₂)))
 Iso.ret Iso∥List∥₂List∥∥₂ = List.elim refl ((lem _ _ ∙_) ∘S cong (_ ∷_))
  where
  lem = elim2 {C = λ a l' → ∥List∥₂→List∥∥₂
      (rec2 squash₂ (λ x₁ xs → ∣ x₁ ∷ xs ∣₂) a l')
      ≡ a ∷ ∥List∥₂→List∥∥₂ l'}
       (λ _ _ → isProp→isSet (isOfHLevelList 0 squash₂ _ _))
        λ _ _ → refl

 List-comm-∥∥₂ : ∀ {ℓ} → List {ℓ} ∘ ∥_∥₂ ≡ ∥_∥₂ ∘ List
 List-comm-∥∥₂ = funExt λ A → isoToPath (Iso∥List∥₂List∥∥₂ {A = A})

join : List (List A) → List A
join [] = []
join (x ∷ xs) = x ++ join xs

cart : List  A → List B → List (A × B)
cart la lb = join (map (λ b → map (_, b) la) lb)

takeWhile : (A → Maybe B) → List A → List B
takeWhile f [] = []
takeWhile f (x ∷ xs) with f x
... | nothing = []
... | just y = y ∷ takeWhile f xs

dropBy : (A → Bool) → List A → List A
dropBy _ [] = []
dropBy f (x ∷ xs) =
  if f x then (dropBy f xs) else (x ∷ xs)

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (x ∷ xs) = Mb.rec [] [_] x ++ catMaybes xs

zipWithIndex : List A → List (ℕ × A)
zipWithIndex [] = []
zipWithIndex (x ∷ xs) = (zero , x) ∷ map (map-fst suc) (zipWithIndex xs)
