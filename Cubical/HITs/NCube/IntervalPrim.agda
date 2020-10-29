{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.IntervalPrim where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum 

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Sigma.Nested.Currying

Fin1-elim : ∀ {ℓ} → {p : Fin 1 → Type ℓ}
            → p fzero → ∀ x → p x  
Fin1-elim {p = p} x x₁ = subst p (snd isContrFin1 x₁) x

dichotomy≤ : ∀ b n → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)
dichotomy≤ b n
  = case n Cubical.Data.Nat.Order.≟ b return (λ _ → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)) of λ
  { (lt o) → inl o
  ; (eq p) → inr (0 , p ∙ sym (+-zero b))
  ; (gt (m , p)) → inr (suc m , sym p ∙ +-suc m b ∙ +-comm (suc m) b)
  }


replaceAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → A → Vec A n → Vec A n  
replaceAt {n = zero} _ _ _ = []
replaceAt {n = suc n} zero a v = a ∷ (tail v)
replaceAt {n = suc n} (suc k) a v = head v ∷ replaceAt k a (tail v)

removeAt : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ℕ → Vec A (suc n) → Vec A n  
removeAt zero v = (tail v)
removeAt {n = zero} (suc k) v = []
removeAt {n = suc n} (suc k) v = head v ∷ removeAt k (tail v)

-- repeat : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → A →  Vec A n
-- repeat {n = zero} a = []
-- repeat {n = suc n} a  = a ∷ (repeat a) 

last : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A (suc n) → A
last {n = zero} a = head a
last {n = suc n} a = last (tail a) 

removeLast : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A (suc n) → Vec A n
removeLast {n = zero} x = []
removeLast {n = suc n} x = head x ∷ (removeLast (tail x))

_∷ₗ_ : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Vec A n → A → Vec A (suc n)
_∷ₗ_ {n = zero} x x₁ = x₁ ∷ []
_∷ₗ_ {n = suc n} x x₁ = head x ∷ ((tail x) ∷ₗ x₁)


removeLast-last : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                 → (x : Vec A n)
                 → (a : A)
                 →  (x ≡ (removeLast (x ∷ₗ a))) × (a ≡ (last (x ∷ₗ a))) 
removeLast-last {n = zero} [] a = refl , refl
removeLast-last {n = suc n} (x ∷ xs) a =
  let h = removeLast-last xs a
  in cong (x ∷_) (fst h) , snd h

last-removeLast : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                 → (x : Vec A (suc n)) → (removeLast x ∷ₗ last x ≡ x)
last-removeLast (x ∷ []) = refl
last-removeLast (x ∷ x₁ ∷ x₂) = cong (x ∷_) (last-removeLast (x₁ ∷ x₂))

head-tail : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                 → (x : Vec A (suc n)) → ((head x ∷ tail x) ≡ x)
head-tail {n = n} (x ∷ x₁) = refl

padWithFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k → Vec A (suc n) → Vec A (k + suc n)  
padWithFirst k x = repeat {n = k} (head x) ++ x

padWithFirst< : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n}
                → ∀ m → (suc n ≤ m)
                → Vec A (suc n) → Vec A (m)  
padWithFirst< m sn<m v = subst (Vec _) (snd sn<m) (padWithFirst (fst sn<m) v)

dropFirst : ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ {n} → ∀ k →  Vec A (k + suc n) → Vec A (suc n)
dropFirst zero x = x
dropFirst (suc k) x = dropFirst k (tail x) 

trimFin : ∀ {n} → ℕ → Fin (suc n) 
trimFin {zero} _ = fzero
trimFin {suc n} zero = fzero
trimFin {suc n} (suc x) = fsuc (trimFin x)



_─_ :  ℕ → ℕ → ℕ
x ─ zero = x
zero ─ suc x₁ = zero
suc x ─ suc x₁ = x ─ x₁

n─n≡0 : ∀ n → n ─ n ≡ zero
n─n≡0 zero = refl
n─n≡0 (suc n) = n─n≡0 n

─+ : ∀ m n → ∀ k → m ≡ n ─ (toℕ {suc n} k) → m + (toℕ k) ≡ n
─+ m n (zero , snd₁) x = +-comm m zero ∙ x
─+ zero zero (suc fst₁ , snd₁) x = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
─+ (suc m) zero (suc fst₁ , snd₁) x = ⊥-rec (snotz x)
─+ zero (suc n) (suc fst₁ , snd₁) x = cong suc (─+ zero n (fst₁ , (pred-≤-pred snd₁)) x)
─+ (suc m) (suc n) (suc fst₁ , snd₁) x =
 cong suc (+-suc m fst₁) ∙ cong suc (─+ (suc m) n (fst₁ , (pred-≤-pred snd₁)) x)










ifω : Typeω → Typeω → Bool → Typeω 
ifω x y false = x
ifω x y true = y

⊥-recω : {A : Typeω} → ⊥ → A
⊥-recω ()


record _×ω_ (A : Typeω) (B : Typeω) : Typeω where
  constructor pairω
  field
     proj₁ω : A
     proj₂ω : B

open _×ω_ public

record Σω (A : Typeω) (B : A → Typeω) : Typeω where
  constructor _,ω_
  field
     fstω : A
     sndω : B fstω 

open Σω public

indω : (x : ℕ → Typeω) → (x 0) → (∀ n → x n → x (suc n)) → ∀ n → x n 
indω x x₁ x₂ zero = x₁
indω x x₁ x₂ (suc n) = x₂ n (indω x x₁ x₂ n)

_↔ω_ : ∀ {ℓ} → Type ℓ → Typeω → Typeω
T ↔ω Tω = (T → Tω) ×ω (Tω → T)

↔ω-section : {ℓ : Level} {T : Type ℓ} {Tω : Typeω} →
                T ↔ω Tω → Type ℓ 
↔ω-section {ℓ} {T} {Tω} x = (b : T) → proj₂ω x (proj₁ω x b) ≡ b


Liftω : ∀ {ℓ} (A : Type ℓ) → Typeω
Liftω A = .(IsOne i1) → A

liftω : ∀ {ℓ} {A : Type ℓ} → A → Liftω A
liftω a = λ _ → a

lowerω : ∀ {ℓ} {A : Type ℓ} → Liftω A → A
lowerω x = x 1=1

record ωType : Typeω₁ where 
  constructor ωty
  field
    Tω : Typeω
    _≡ω_ : (Tω → (Tω → Typeω))
    symω : {a b : Tω} → a ≡ω b → b ≡ω a
    _transω_ : {a b c : Tω} → a ≡ω b → b ≡ω c → a ≡ω c

open ωType using () renaming (Tω to T[_]) public 

record Morω (A B : ωType) : Typeω where
  constructor morω

  field
    f : T[ A ] → T[ B ]
    f= : (x y : T[ A ]) → (A ωType.≡ω x) y → (B ωType.≡ω (f x)) (f y)

ω[_] : ∀ {ℓ} → Type ℓ → ωType
ω[ A ] = ωty (Liftω A) (λ x x₁ → Liftω (lowerω x ≡ lowerω x₁))
             (λ x x₁ → sym (lowerω x))
              λ x x₁ → liftω ( (lowerω x) ∙ (lowerω x₁) )

I→ : ωType → ωType
I→ x = ωty (I → Tω) (λ x₁ x₂ → (∀ i → (x₁ i ≡ω x₂ i)))
           (λ x₁ i → symω (x₁ i))
           λ x₁ x₂ i → (x₁ i) transω (x₂ i)
  where open ωType x

∀I : (A : I → ωType) → ωType
∀I A = ωty (∀ i → Tω (A i))
           (λ x x₁ → ∀ (i : I) → _≡ω_ (A i) (x i) (x₁ i))
           (λ x i → symω (A i) (x i))
           λ x x₁ i → _transω_ (A i) (x i) (x₁ i) 
  where open ωType

  

record Isoω {ℓ : Level} (T : Type ℓ)
                (t : ωType) : Typeω where
  open ωType t

  field
    to : T → Tω
    from : Tω → T
    sec : (b : T) → from (to b) ≡ b    
    ret : (a : Tω) → to (from a) ≡ω a




Typeωⁿ : Typeω → ℕ → Typeω
Typeωⁿ x zero = x
Typeωⁿ x (suc x₁) = I → Typeωⁿ x x₁


iterω : (ωType → ωType) → ωType → ℕ → ωType  
iterω f x0 zero = x0
iterω f x0 (suc n) = f (iterω f x0 n)

Cu :  ∀ {ℓ} → ∀ (A  : Type ℓ) → (n : ℕ) → ωType
Cu A = iterω I→ ω[ A ]

Cuω :  ∀ (A  : ωType) → (n : ℕ) → ωType
Cuω A = iterω I→ A




mor-Cuω : {A B : ωType} → (Morω A B) → ∀ n → (Morω (Cuω A n) (Cuω B n))
mor-Cuω x zero = x
mor-Cuω x (suc n) =
  let z = mor-Cuω (x) n
  in morω (λ x₁ i → Morω.f z (x₁ i)) λ x₁ y x₂ i → Morω.f= (mor-Cuω (x) n) (x₁ i) (y i) (x₂ i)


map-Cuω : {A B : ωType} → (T[ A ] → T[ B ]) → ∀ n → T[ Cuω A n ] → T[ Cuω B n ]
map-Cuω x zero = x
map-Cuω x (suc n) x₁ i = map-Cuω x n (x₁ i)

CType : (ℓ : Level) → ℕ → ωType 
CType ℓ n = Cu (Type ℓ) n


Cu[_,_] : ∀ {ℓ} → {A : Type ℓ} → ∀ n → A → T[ (Cu A n) ] 
Cu[_,_] zero a _ = a
Cu[_,_] (suc n) a _ = Cu[_,_] n a


cu : ∀ {ℓ} → ∀ n → T[ CType ℓ n ] → ωType
cu zero A = ω[ lowerω A ]
cu (suc n) A = ∀I λ i → cu n (A i)

cuC[_,_] : ∀ {ℓ} → ∀ n → {A : Type ℓ } → A →  T[ cu n Cu[ n , A ] ] 
cuC[_,_] zero a _ = a
cuC[_,_] (suc n) a _ = cuC[_,_] n a


Ieω : ωType
T[_] Ieω = I
ωType._≡ω_ Ieω = λ x x₁ → (.(IsOne x) → IsOne x₁) ×ω (.(IsOne x₁) → IsOne x)
proj₁ω (ωType.symω Ieω x) = proj₂ω x
proj₂ω (ωType.symω Ieω x) = proj₁ω x
(Ieω ωType.transω x) x₁ = pairω (λ x₂ → proj₁ω x₁ (proj₁ω x x₂)) (λ x₂ → proj₂ω x (proj₂ω x₁ x₂))

-- Ieω' : ωType
-- T[_] Ieω' = I
-- ωType._≡ω_ Ieω' = λ x x₁ → ∀ ℓ → (A : Type ℓ) → (
--         ((.(IsOne x) → A) → ((.(IsOne x₁)) → A))
--          ×ω
--         ((.(IsOne x₁) → A) → ((.(IsOne x)) → A)))
-- proj₁ω (ωType.symω Ieω' x ℓ A) = (proj₂ω (x ℓ A))
-- proj₂ω (ωType.symω Ieω' x ℓ A) = (proj₁ω (x ℓ A))
-- proj₁ω ((Ieω' ωType.transω x) x₁ ℓ A) x₂ x₃ = {!!}
-- proj₂ω ((Ieω' ωType.transω x) x₁ ℓ A) = {!!}

Ie' : ℕ → Typeω
Ie' n = T[ iterω I→ Ieω n ]

Ie : ℕ → Typeω
Ie zero = I
Ie (suc n) = I → Ie n

Cu-dim-subst : ∀ (n₁ n₂ : ℕ) → n₁ ≡ n₂ → Ie n₁ → Ie n₂ 
Cu-dim-subst zero zero p x₁ = x₁
Cu-dim-subst zero (suc n₂) p x₁ = ⊥-recω (znots p)
Cu-dim-subst (suc n₁) zero p x₁ =  ⊥-recω (snotz p)
Cu-dim-subst (suc n₁) (suc n₂) p x₁ i = Cu-dim-subst n₁ n₂ (cong predℕ p) (x₁ i)

Cuz : ∀ {ℓ} → ∀ {A  : Type ℓ} → T[ Cu A 0 ] → A
Cuz x = x 1=1

-- this version of Interval will let us handle both ends in single case
-- the convention of i0 ↔ false , i1 ↔ true is used everywhere in this module

data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

isOne-∨B : ∀ b → IsOne (Bool→I b ∨ ~ Bool→I b)
isOne-∨B false = 1=1
isOne-∨B true = 1=1

bool-elimω : ∀ {A : Typeω} → Bool → A → A → A
bool-elimω false f _ = f
bool-elimω true _ t = t

negIf : Bool → I → I
negIf b i = bool-elimω b (~ i) i 

self∨ : I → I
self∨ x = x ∨ (~ x)

Iapp : ∀ {ℓ} → {A : Type ℓ}
         → (I → A) → Interval' → A
Iapp x (end x₁) = x (Bool→I x₁) 
Iapp x (inside i) = x i

caseBool : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → Bool → A
caseBool att aff true  = att
caseBool att aff false = aff

Iapp= : ∀ {ℓ} → {A : Type ℓ} → {a₀ a₁ : A}
         → a₀ ≡ a₁ → Interval' → A
Iapp= {a₀ = a₀} {a₁} x (end x₁) = caseBool a₁ a₀ x₁ 
Iapp= x (inside i) = x i

IappP : ∀ {ℓ} → {A : I → Type ℓ} → {a₀ : A i0} → {a₁ : A i1}
      → PathP (λ i → A i) a₀ a₁ 
      → ∀ i' →  Iapp (λ i → A i) i'
IappP {a₀ = a₀} x (end false) = a₀
IappP {a₁ = a₁} x (end true) = a₁
IappP x (inside i) = x i


iterω-I→-face :  ∀ (A  : ωType) → (n : ℕ) → ℕ → Bool
                  → T[ iterω I→ A (suc n) ]
                  → T[ iterω I→ A n ]
iterω-I→-face A n zero x₁ x₂ = x₂ (Bool→I x₁)
iterω-I→-face A zero (suc x) x₁ x₂ = x₂ (Bool→I x₁)
iterω-I→-face A (suc n) (suc x) x₁ x₂ i = iterω-I→-face A n x x₁ (x₂ i) 

CType-face : ∀ {ℓ} → ∀ n → ℕ → Bool
             → T[ CType ℓ (suc n) ]
             → T[ CType ℓ n ]    
CType-face = iterω-I→-face _


Ie-face : ∀ n → ℕ → Bool → Ie (suc n) → Ie n 
Ie-face n zero b x = x (Bool→I b)
Ie-face zero (suc k) b x = x (Bool→I b)
Ie-face (suc n) (suc k) b x i = Ie-face n k b (x i)


NCube : ℕ -> Type₀
NCube = Vec Interval' 

_i∷_ : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
          (∀ x → A x) → ∀ i → ∀ x → (A ∘ (inside i ∷_)) x 
_i∷_ {ℓ} {n} {A} x i = x ∘ (inside i ∷_)

_b∷_ : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ} →
          (∀ x → A x) → ∀ b → ∀ x → (A ∘ (end b ∷_)) x 
_b∷_ {ℓ} {n} {A} x b = x ∘ (end b ∷_)

Ct[_,_] : ∀ {ℓ}  → ∀ n → (A : NCube n → Type ℓ) → T[ CType ℓ n ] 
Ct[ zero , A ] = liftω (A [])
Ct[ suc n , A ] i = Ct[ n , (A ∘ (inside i ∷_)) ]

ct[_,_] : ∀ {ℓ}  → ∀ n → {A : NCube n → Type ℓ} → (a : ∀ c → A c) → T[ cu n (Ct[ n , A ]) ] 
ct[ zero , a ] = liftω (a [])
ct[ suc n , a ] i = ct[ n , a i∷ i ]




isContr-Inrerval' : isContr Interval'
fst isContr-Inrerval' = end false
snd isContr-Inrerval' (end false) = refl
snd isContr-Inrerval' (end true) = inside
snd isContr-Inrerval' (inside i) j = inside (i ∧ j) 

isProp-Inrerval' = (isContr→isProp isContr-Inrerval')

endT= : ∀ i' → end true ≡ i'
endT= (end false) = sym inside
endT= (end true) = refl
endT= (inside i) i₁ = inside (i ∨ ~ i₁)

endF= : ∀ i' → i' ≡ end false 
endF= (end false) = refl
endF= (end true) = sym inside
endF= (inside i) i₁ = inside (i ∧ ~ i₁)

----------
----------

corner0 : ∀ {n} → NCube n
corner0 {zero} = []
corner0 {suc n} =  end false ∷ corner0

corner1 : ∀ {n} → NCube n
corner1 {zero} = []
corner1 {suc n} =  end true ∷ corner1

corner0-≡ : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n} (corner0) a  
corner0-≡ {zero} [] = refl
corner0-≡ {suc n} (end false ∷ x₁) i = end false ∷ corner0-≡ x₁ i
corner0-≡ {suc n} (end true ∷ x₁) i = inside i ∷ corner0-≡ x₁ i
corner0-≡ {suc n} (inside i ∷ x₁) j = inside (i ∧ j) ∷ corner0-≡ x₁ j

≡-corner1 : ∀ {n} → ∀ (a : NCube n) → _≡_ {A = NCube n}  a (corner1)  
≡-corner1 {zero} [] = refl
≡-corner1 {suc n} (end true ∷ x₁) i = end true ∷ ≡-corner1 x₁ i
≡-corner1 {suc n} (end false ∷ x₁) i = inside i ∷ ≡-corner1 x₁ i
≡-corner1 {suc n} (inside i ∷ x₁) j = inside (i ∨ j) ∷ ≡-corner1 x₁ j

corner0-≡-corner1 : ∀ {n} → _≡_ {A = NCube n}  corner0 corner1  
corner0-≡-corner1 {zero} = refl
corner0-≡-corner1 {suc n} i = (inside i) ∷ corner0-≡-corner1 i


isPropCube : ∀ {n} → isProp (NCube n)
isPropCube {zero} [] [] i = []
isPropCube {suc n} (x ∷ x₁) (x₂ ∷ x₃) i =
    (isContr→isProp isContr-Inrerval') x x₂ i ∷ (isPropCube x₁ x₃ i)

inside≡ : ∀ i j → inside i ≡ inside j
inside≡ i j i' = inside ( (i ∧ (~ i'))  ∨ (j ∧ i') ) 


--------------
--------------

Interval'-≡-∥Bool∥  : Interval' → Interval' ≡ ∥ Bool ∥
Interval'-≡-∥Bool∥ i' i = fst (Lo.⇔toPath {P = Interval' , isProp-Inrerval'}
                                          {Q = Lo.∥ Bool ∥ₚ } f g i)
  where
    f : _
    f (end x) = ∣ x ∣ 
    f (inside i) = squash  ∣ false ∣  ∣ true ∣  i

    g : _
    g x = i'



lenNC : ∀ n → NCube n → Vec S¹ n 
lenNC zero [] = []
lenNC (suc n) (end x ∷ x₁) = base ∷ (lenNC _ x₁)
lenNC (suc n) (inside i ∷ x₁) = loop i ∷ (lenNC _ x₁) 

-- Cu→I :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → (NCube (suc n) → A) → Iⁿ→ A n
-- Cu→I zero x x₁ = x (inside x₁ ∷ [])
-- Cu→I (suc n) x i = Cu→I n (x ∘ (inside i ∷_))
 
-- Cu←I :  ∀ {ℓ} → ∀ {A  : Type ℓ} → ∀ n → Iⁿ→ A n → (NCube (suc n) → A)
-- Cu←I zero x (end x₁ ∷ x₂) = x (Bool→I x₁)
-- Cu←I zero x (inside i ∷ x₂) = x i
-- Cu←I (suc n) x (end x₁ ∷ x₂) = Cu←I n (x (Bool→I x₁)) x₂
-- Cu←I (suc n) x (inside i ∷ x₂) = Cu←I n (x i) x₂




-- Cu-app : ∀ {ℓ} → ∀ {n} → ∀ {A  : Type ℓ} → Cu A n → NCube n → A
-- Cu-app {n = zero} x _ = Cuz x
-- Cu-app {n = suc n} x v = Iapp (λ i → Cu-app (x i) (tail v)) (head v)

-- cu-app : ∀ {ℓ} → ∀ n → ∀ {A  : CType ℓ n} → cu n A → (cu : NCube n) → Cu-app A cu
-- cu-app {ℓ} zero {A} x cu = x  1=1
-- cu-app {ℓ} (suc n) {A} x cu = IappP (λ i → cu-app n (x i) (tail cu)) (head cu) 

-- Cu-elim : ∀ {ℓ} → ∀ n → ∀ {A  : Type ℓ} → (NCube n → A) → Cu A n 
-- Cu-elim (zero) x _ = x []
-- Cu-elim (suc n) x i = Cu-elim n (x ∘ (inside i ∷_))

-- c→elim : ∀ {ℓ} → ∀ n → ∀ {A  : CType ℓ n} → ((cu : NCube n) → Cu-app A cu) → cu n A 
-- c→elim zero x _ = x []
-- c→elim (suc n) x i = c→elim n ((x ∘ (inside i ∷_)))


-- Cumap : ∀ {ℓ ℓ'} → ∀ n → ∀ {A  : Type ℓ} → ∀ {B  : Type ℓ'} → (A → B) → Cu A n → Cu B n
-- Cumap zero f x _ = f (x 1=1)
-- Cumap (suc n) f x i = Cumap n f (x i)

Cu→ : ∀ {ℓ ℓ'} → ∀ n → (A  : T[ CType ℓ n ] ) → (B : T[ CType ℓ' n ])
        →  T[ CType (ℓ-max ℓ ℓ') n ]
Cu→ zero A B _ = A 1=1 → B 1=1
Cu→ (suc n) A B i = Cu→ n (A i) (B i)

cu→[_,_] : ∀ {ℓ ℓ'} → ∀ n → {A : NCube n → Type ℓ } → {B : NCube n → Type ℓ' }
              → (∀ c → A c → B c) →  T[ cu n (Cu→ n Ct[ n , A ] Ct[ n , B ]) ]
cu→[ zero , x ] = liftω (x [])
cu→[ suc n , x ] i = cu→[ n , x i∷ i ]

Cu→[_,_] : ∀ {ℓ ℓ'} → ∀ n → {A : NCube n → Type ℓ } → {B : Type ℓ' }
              → (∀ c → A c → B) →  T[ cu n (Cu→ n Ct[ n , A ] Cu[ n , B ]) ]
Cu→[ zero , x ] = liftω (x [])
Cu→[ suc n , x ] i = Cu→[ n , x i∷ i ]

cTy : ∀ {ℓ} → ∀ n → T[ cu n Cu[ n , Type ℓ ] ] → T[ CType ℓ n ]
cTy zero x = x
cTy (suc n) x i = cTy (n) (x i) 

c-map→ : ∀ {ℓ ℓ'} → ∀ n → ∀ {A  : T[ CType ℓ n ]} → ∀ {B  : T[ CType ℓ' n ]}
        → T[ cu n (Cu→ n A B) ] → T[ cu n A ] → T[ cu n B ]
c-map→ zero f a _ = (f 1=1) (a 1=1) 
c-map→ (suc n) f a i = c-map→ n (f i) (a i)

Cu-Π : ∀ {ℓ ℓ'} → ∀ n → (A  : T[ CType ℓ n ]) → (B : T[ cu n (Cu→ n A Cu[ n , Type ℓ' ]) ])
        →  T[ CType (ℓ-max ℓ ℓ') n ]
Cu-Π zero A B _ = (a : A 1=1) → B 1=1 a
Cu-Π (suc n) A B i = Cu-Π n (A i) (B i)

c-mapΠ : ∀ {ℓ ℓ'} → ∀ n
         → ∀ {A  : T[ CType ℓ n ]} → {B : T[ cu n (Cu→ n A Cu[ n , Type ℓ' ]) ]}
         → T[ cu n (Cu-Π n A B) ] → (a : T[ cu n A ]) → T[ cu n (cTy n (c-map→ n B a)) ]
c-mapΠ zero f a _ = (f 1=1) (a 1=1)
c-mapΠ (suc n) f a i = c-mapΠ n (f i) (a i)

---- conversions from and to functions of NCube


CType-to-NC : ∀ {ℓ} → ∀ n → Isoω (NCube n → Type ℓ) (CType ℓ n)
CType-to-NC zero =
  record { to = λ x x₁ → x []
         ; from = λ x x₁ → lowerω x
         ; sec = λ b i x → b (isPropCube [] x i)
         ; ret = λ a x i → a 1=1
         }
Isoω.to (CType-to-NC (suc n)) x i = Isoω.to (CType-to-NC n) (x ∘ (inside i ∷_))
Isoω.from (CType-to-NC (suc n)) x (end x₁ ∷ x₂) = Isoω.from (CType-to-NC n) (x (Bool→I x₁)) x₂
Isoω.from (CType-to-NC (suc n)) x (inside i ∷ x₂) = Isoω.from (CType-to-NC n) (x i) x₂
Isoω.sec (CType-to-NC (suc n)) b i (end false ∷ x₁) =
  Isoω.sec (CType-to-NC n) (λ x₂ → b (end false ∷ x₂)) i x₁
Isoω.sec (CType-to-NC (suc n)) b i (end true ∷ x₁) =
  Isoω.sec (CType-to-NC n) (λ x₂ → b (end true ∷ x₂)) i x₁
Isoω.sec (CType-to-NC (suc n)) b i (inside i₁ ∷ x₁) =
  Isoω.sec (CType-to-NC n) (b ∘ (inside i₁ ∷_)) i x₁
Isoω.ret (CType-to-NC (suc n)) a i = Isoω.ret (CType-to-NC (n)) (a i)

CType-ev : ∀ {ℓ} → ∀ n → T[ CType ℓ n ] → NCube n → Type ℓ
CType-ev zero x x₁ = x 1=1
CType-ev (suc n) x (end x₁ ∷ x₂) = CType-ev n (x (Bool→I x₁)) x₂
CType-ev (suc n) x (inside i ∷ x₂) = CType-ev n (x i) x₂ 

CType-ev-elim : ∀ {ℓ} → ∀ n → {A : NCube n → Type ℓ} → (c :  NCube n)
                  → CType-ev n Ct[ n , A ] c → A c 
CType-ev-elim zero [] x = x
CType-ev-elim (suc n) (end false ∷ c) x = CType-ev-elim n c x
CType-ev-elim (suc n) (end true ∷ c) x = CType-ev-elim n c x
CType-ev-elim (suc n) (inside i ∷ c) x = CType-ev-elim n c x


from-cu : ∀ {ℓ} → ∀ {n} → {A : T[ CType ℓ n ]}
           →  T[ cu n A ] → (c : NCube n) → CType-ev n A c
from-cu {n = zero} x _ = lowerω x 
from-cu {n = suc n} {A} x (end x₁ ∷ c) = from-cu {n = n} {A (Bool→I x₁)} (x (Bool→I x₁)) c
from-cu {n = suc n} {A} x (inside i ∷ c) = from-cu {n = n} {A i} (x i) c

from-cu' : ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
           →  T[ cu n  Ct[ n , (λ _ → A) ] ] → (c : NCube n) → A
from-cu' {n = zero} x c = lowerω x
from-cu' {n = suc n} {A} x (end x₁ ∷ c) = from-cu' {n = n} {A} (x (Bool→I x₁)) c
from-cu' {n = suc n} {A} x (inside i ∷ c) = from-cu' {n = n} {A} (x i) c



-- ---------

Ie-fromFoldL : (I → I → I) → I → ∀ n → Ie n
Ie-fromFoldL _ e0 zero = e0
Ie-fromFoldL f e0 (suc zero) i = f i e0
Ie-fromFoldL f e0 (suc (suc n)) i j = Ie-fromFoldL f e0 (suc n) (f i j)

Ie-map : ∀ n → Ie n → (I → I) → Ie n 
Ie-map zero x x₁ = x₁ x
Ie-map (suc n) x x₁ i = Ie-map n (x i) x₁

Ie-fromFoldR : (I → I → I) → I → ∀ n → Ie n
Ie-fromFoldR _ e0 zero = e0
Ie-fromFoldR f e0 (suc zero) i = f i e0
Ie-fromFoldR f e0 (suc (suc n)) i j =  Ie-map n (Ie-fromFoldR f e0 (suc n) j) (f i)

[_]Iexpr : ∀ {n} → I → Ie n 
[_]Iexpr {zero} x = x
[_]Iexpr {suc n} x i = [_]Iexpr x
 
↑Expr : ∀ {n} → ∀ k → Ie n → Ie (k + n) 
↑Expr {n} zero x = x
↑Expr {n} (suc k) x _ = ↑Expr k x

i0ⁿ : ∀ {n} → Ie n
i0ⁿ = [ i0 ]Iexpr

i1ⁿ : ∀ {n} → Ie n
i1ⁿ = [ i1 ]Iexpr

fold-∨ : ∀ n → (Ie n)
fold-∨ = Ie-fromFoldR _∨_ i0

fold-∧ : ∀ n → (Ie n)
fold-∧ = Ie-fromFoldR _∧_ i1

_∨ⁿ_ : ∀ {n} → Ie n → Ie n → Ie n
_∨ⁿ_ {zero} x x₁ = x ∨ x₁
_∨ⁿ_ {suc n} x x₁ i = x i ∨ⁿ x₁ i 

_∧ⁿ_ : ∀ {n} → Ie n → Ie n → Ie n
_∧ⁿ_ {zero} x x₁ = x ∧ x₁
_∧ⁿ_ {suc n} x x₁ i = x i ∧ⁿ x₁ i

~ⁿ : ∀ {n} → Ie n → Ie n
~ⁿ {zero} x = ~ x 
~ⁿ {suc n} x i = ~ⁿ (x i)

boundaryExpr : ∀ n → Ie n
boundaryExpr zero = i0
boundaryExpr (suc zero) i = i ∨ (~ i)
boundaryExpr (suc (suc n)) i = ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr ) ∨ⁿ (boundaryExpr (suc n))

faceExpr : ∀ {n} → ℕ → Bool → Ie (suc n)
faceExpr  zero x₁ i = [ (negIf x₁ i) ]Iexpr
faceExpr {zero} (suc _) x₁ i = [ (negIf x₁ i) ]Iexpr
faceExpr {suc n} (suc x) x₁ _ = faceExpr {n} x x₁


-- this will not typechck
-- 
-- Ie-eval : ∀ n → Ie n → NCube (suc n) → I
-- Ie-eval zero x x₁ = x
-- Ie-eval (suc n) x x₁ = {!Ie-eval n !}

--- POSET of expresions

record ωPOSET : Typeω₁ where
  field
    Carrier : Typeω
    _⊆_ : Carrier → Carrier → Typeω
    PO-trans : {a b c : Carrier} → a ⊆ b → b ⊆ c 
   

⊆I : ∀ {n} → Ie n → Ie n → (Typeω)
⊆I {zero} x x₁ = (IsOne x) → (IsOne x₁) 
⊆I {suc n} x x₁ = (i : I) → ⊆I (x i) (x₁ i)

⊆I-trans : ∀ n → {a b c : Ie n} → ⊆I a b → ⊆I b c → ⊆I a c
⊆I-trans zero x x₁ x₂ = x₁ (x x₂)
⊆I-trans (suc n) x x₁ i = ⊆I-trans n (x i) (x₁ i)

-- ⊆'I : ∀ {n} → Ie n → Ie n → (Typeω)
-- ⊆'I {zero} x x₁ = ∀ {ℓ} → {A : Type ℓ} → ((.(IsOne x₁) → A) → (.(IsOne x) → A)) 
-- ⊆'I {suc n} x x₁ = (i : I) → ⊆'I (x i) (x₁ i)


⊂-∨~B : ∀ n → ∀ b → 
               let i = (Bool→I b)  in
                ⊆I {n = n} i1ⁿ ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) 
⊂-∨~B zero false x = x
⊂-∨~B zero true x = x
⊂-∨~B (suc n) b _ = ⊂-∨~B n b

⊆I-∨2 : ∀ {n} → (x y : Ie n) → ⊆I y (x ∨ⁿ y)
⊆I-∨2 {zero} x y = IsOne2 x y 
⊆I-∨2 {suc n} x y i = ⊆I-∨2 {n} (x i) (y i)

⊆I-∨1 : ∀ {n} → (x y : Ie n) → ⊆I x (x ∨ⁿ y)
⊆I-∨1 {zero} x y = IsOne1 x y 
⊆I-∨1 {suc n} x y i = ⊆I-∨1 {n} (x i) (y i)

0∨ⁿ : ∀ {n} → (x : Ie n) → (⊆I (i0ⁿ ∨ⁿ x) x)  
0∨ⁿ {zero} x y = y
0∨ⁿ {suc n} x i = 0∨ⁿ (x i)

face⊆Iboundary : ∀ n → ∀ {k} → ∀ {b} → ⊆I {suc n} (faceExpr k b) (boundaryExpr (suc n))
face⊆Iboundary zero {zero} {false} i = IsOne2 i (~ i)
face⊆Iboundary zero {zero} {true} i = IsOne1 i (~ i)
face⊆Iboundary (suc n) {zero} {false} i =
                      ⊆I-trans (suc n) ((⊆I-∨2 {n = (suc n)} [ i ]Iexpr [ ~ i ]Iexpr))
                          (⊆I-∨1 (λ z → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) z) (boundaryExpr (suc n)))
face⊆Iboundary (suc n) {zero} {true} i = 
                       ⊆I-trans (suc n) ((⊆I-∨1 {n = (suc n)} [ i ]Iexpr [ ~ i ]Iexpr))
                          (⊆I-∨1 (λ z → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) z) (boundaryExpr (suc n)))
face⊆Iboundary zero {suc k} {false} i = IsOne2 i (~ i)
face⊆Iboundary zero {suc k} {true} i = IsOne1 i (~ i)
face⊆Iboundary (suc n) {suc k} {b} i i₁ =
  ⊆I-trans n (face⊆Iboundary n {k} {b} i₁) (⊆I-∨2 _ _)

-- those are not definational for unknown n 
∧-comm : ∀ {n} → (x y : Ie n) → ⊆I (x ∧ⁿ y) (y ∧ⁿ x)
∧-comm {zero} x y x₁ = x₁
∧-comm {suc n} x y i = ∧-comm (x i) (y i)

∨-comm : ∀ {n} → (x y : Ie n) → ⊆I (x ∨ⁿ y) (y ∨ⁿ x)
∨-comm {zero} x y x₁ = x₁
∨-comm {suc n} x y i = ∨-comm (x i) (y i)





-------- Partialⁿ 

Partialⁿ : ∀ {ℓ} → ∀ n → Ie n → (T[ CType ℓ n ]) → ωType

T[_] (Partialⁿ zero e A) = Partial e (lowerω A)
(Partialⁿ zero e A ωType.≡ω x) x₁ = PartialP e λ o → x o ≡ x₁ o
ωType.symω (Partialⁿ zero e A) x p = sym (x p)
(Partialⁿ zero e A ωType.transω x) x₁ p =  x p ∙ x₁ p 

Partialⁿ (suc n) e A = ∀I λ i → Partialⁿ n (e i) (A i)

CTypeP :  ∀ ℓ → ∀ n → (e : Ie n) → ωType
CTypeP ℓ n e = Partialⁿ n e Cu[ n , Type ℓ ]

PartialPⁿ : ∀ {ℓ} → ∀ n → (e : Ie n) → T[ CTypeP ℓ n e ] → ωType
T[_] (PartialPⁿ zero e x) = PartialP e x
(PartialPⁿ {ℓ} zero e x ωType.≡ω x₁) x₂ =  PartialP {ℓ} e λ o → Path (x o) (x₁ o) (x₂ o)
ωType.symω (PartialPⁿ zero e x) x₁ p =  sym (x₁ p)
(PartialPⁿ zero e x ωType.transω x₁) x₂ p =  x₁ p ∙ x₂ p 

PartialPⁿ (suc n) e x = ∀I λ i → PartialPⁿ n (e i) (x i)

Partialⁿ-map→ : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → {A : T[ CType ℓ n ]}
               → {B : T[ CType ℓ' n ]}
               → T[ Partialⁿ n e (Cu→ n A B) ]
               → T[ Partialⁿ n e A ]
               → T[ Partialⁿ n e B ]
Partialⁿ-map→ zero x x₁ x₂ = x x₂ (x₁ x₂)
Partialⁿ-map→ (suc n) x x₁ i = Partialⁿ-map→ n (x i) (x₁ i)



paⁿ : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]} → {e : Ie n}
     →  T[ cu n A ] → T[ Partialⁿ n e A ]
paⁿ zero x x₁ = x 1=1
paⁿ (suc n) x i = paⁿ n (x i)

-- paPⁿ : ∀ {ℓ} → ∀ n → {A : T[ CTypeP ℓ n ]} → {e : Ie n}
--      →  T[ cu n A ] → T[ Partialⁿ n e A ]
-- paPⁿ = ?

Partialⁿ-mapΠ : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → {A : T[ CType ℓ n ]}
               → {B : T[ cu n (Cu→ n A Cu[ n , Type ℓ' ]) ]}
               → T[ cu n (Cu-Π n A B) ]
               → (a : T[ Partialⁿ n e A ])
               → T[ PartialPⁿ n e ( Partialⁿ-map→ n (paⁿ n B) a) ]
Partialⁿ-mapΠ zero f a e=1 = lowerω f (a e=1) 
Partialⁿ-mapΠ (suc n) f a i = Partialⁿ-mapΠ n (f i) (a i)


CuP-→ : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
        → (A : T[ CTypeP ℓ n e ])
        → (B : T[ CTypeP ℓ' n e ])
        →  T[ CTypeP (ℓ-max ℓ ℓ') n e ]
CuP-→ zero A B e=1 = A e=1 → B e=1
CuP-→ (suc n) A B i = CuP-→ n (A i) (B i)


PartialPⁿ-map→ : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → {A : T[ CTypeP ℓ n e ]}
               → {B : T[ CTypeP ℓ' n e ]}
               → T[ PartialPⁿ n e (CuP-→ n A B) ]
               → T[ PartialPⁿ n e A ]
               → T[ PartialPⁿ n e B ]
PartialPⁿ-map→ zero  f a e=1 = (f e=1) (a e=1)
PartialPⁿ-map→ (suc n) f a i = PartialPⁿ-map→ n (f i) (a i)


CuP-Π : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → (A : T[ CTypeP ℓ n e ])
               → (B : T[ PartialPⁿ n e ((CuP-→ n A (paⁿ n cuC[ n , Type ℓ' ]))) ])
               → T[ CTypeP (ℓ-max ℓ ℓ') n e ]
CuP-Π zero A B x = (a : A x) → B x a
CuP-Π (suc n) A B i = CuP-Π n (A i) (B i)

fromCuc : ∀ {ℓ} → ∀ n → ∀ {e} → T[ PartialPⁿ n e (paⁿ n cuC[ n , Type ℓ ]) ]
                    → T[ CTypeP ℓ n e ]
fromCuc zero x x₁ = x x₁
fromCuc (suc n) x i = fromCuc n (x i)

PartialPⁿ-mapΠ : ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → {A : T[ CTypeP ℓ n e ]}
               → {B : T[ PartialPⁿ n e ((CuP-→ n A (paⁿ n cuC[ n , Type ℓ' ]))) ]}
               → T[ PartialPⁿ n e (CuP-Π n A B) ]
               → (a : T[ PartialPⁿ n e A ])
               → T[ PartialPⁿ n e
                      (fromCuc n (PartialPⁿ-map→ n B a)) ]
PartialPⁿ-mapΠ zero x a p =  (x p) (a p)
PartialPⁿ-mapΠ (suc n) x a i = PartialPⁿ-mapΠ n (x i) (a i)

Partialⁿ-i1-elim : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]}
                   → T[ Partialⁿ n i1ⁿ A ]
                   → T[ cu n A ]
Partialⁿ-i1-elim {ℓ} zero x = x
Partialⁿ-i1-elim {ℓ} (suc n) x i = Partialⁿ-i1-elim {ℓ} n (x i)

Subⁿ : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]} → (e : Ie n) →  (T[ Partialⁿ n e A ]) → ωType

T[_] (Subⁿ zero e x) = Sub (lowerω _) _ x
(Subⁿ zero e x ωType.≡ω x₁) x₂ = Liftω (outS x₁ ≡ outS x₂)
ωType.symω (Subⁿ zero e x) x₁ x₂ = sym (lowerω x₁)
(Subⁿ zero e x ωType.transω x₁) x₂ x₃ = lowerω x₁ ∙ lowerω x₂ 

Subⁿ (suc n) e x = ∀I λ i → Subⁿ n (e i) (x i)




Subⁿ-map' :  ∀ {ℓ ℓ'} → ∀ n → {e : Ie n}
               → {A : NCube n → Type ℓ}
               → {B : NCube n → Type ℓ'}            
               → (f : ∀ c → A c → B c )
               → (a : T[ Partialⁿ n e Ct[ n , A ] ])
               → T[ Subⁿ n e a ]       
               → T[ Subⁿ n e (Partialⁿ-map→ n (paⁿ n cu→[ n , f ]) a) ]       
Subⁿ-map' zero f a x = inS (f [] (outS x))
Subⁿ-map' (suc n) f a x i = Subⁿ-map' n (f i∷ i) (a i) (x i)


hlp-Sub-f :  ∀ {ℓ ℓ' ℓ'' ℓ'''} → ∀ n → {e : Ie n}
               → {A : Type ℓ}
               → {B : Type ℓ'}
               → {A' : Type ℓ''}
               → {B' : Type ℓ'''}
               → (f : T[ Partialⁿ n e (Cu→ n Ct[ n , const A ] Ct[ n , const B ]) ])
               → (f' : (A → B) → (A' → B'))
               → T[ Partialⁿ n e (Cu→ n Ct[ n , const A' ] Ct[ n , const B' ]) ]
hlp-Sub-f zero f g e=1 = g (f e=1)
hlp-Sub-f (suc n) f g i = hlp-Sub-f n (f i) g



Subⁿ-map-∘' :  ∀ {ℓ ℓ' ℓ''} → ∀ n → {e : Ie n}
               → {A : NCube n → Type ℓ}
               → {B : NCube n → Type ℓ'}
               → {B' : NCube n →  Type ℓ''}
               → (f : ∀ c → A c → B c )
               → (f' : ∀ c → B c → B' c)
               → (a : T[ Partialⁿ n e Ct[ n , A ] ])
               → T[ Subⁿ n e ((Partialⁿ-map→ n (paⁿ n cu→[ n , f ]) a))]       
               → T[ Subⁿ n e ((Partialⁿ-map→ n (paⁿ n cu→[ n , (λ c → f' c ∘ f c) ]) a))]
Subⁿ-map-∘' zero f f' a x = inS (f' [] (outS x))
Subⁿ-map-∘' (suc n) f f' a x i = Subⁿ-map-∘' n (f i∷ i) (f' i∷ i) (a i) (x i)


-- Subⁿ-map :  ∀ {ℓ ℓ' ℓ''} → ∀ n → {e : Ie n}
--                → {A : T[ CType ℓ n ]}
--                → {B : T[ CType ℓ' n ]}
--                → {B' : T[ CType ℓ'' n ]}
--                → (f : T[ cu n (Cu→ n A B) ] )
--                → (f' : T[ cu n (Cu→ n B B') ])
--                → (a : T[ Partialⁿ n e A ])
--                → T[ Subⁿ n e ((Partialⁿ-map→ n (paⁿ n f) a))]       
--                → {!T[ Subⁿ n e ((Partialⁿ-map→ n (paⁿ n f) a))]!}
-- Subⁿ-map = {!!}

-- Subⁿ-map'' : ∀ n → {e : Ie n}
--                → {A A' B B' : NCube n → Type₀}
--                → (f : ∀ c → A c → B c )
--                → (f' : ∀ c → A' c → B' c )
--                → (g : ∀ c → A c → A' c )
--                → (a : T[ Partialⁿ n e Ct[ n , A ] ])
--                → (f= : T[ PartialPⁿ n e {!!} ] )
--                → T[ Subⁿ n e (Partialⁿ-map→ n (paⁿ n cu→[ n , f ]) a) ]
--                → T[ Subⁿ n e (Partialⁿ-map→ n (paⁿ n cu→[ n , (λ c → f' c ∘ g c)  ]) a) ]       
-- Subⁿ-map'' = {!!} 

inSⁿ : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]} → (e : Ie n)
       →  (a : T[ cu n A ])
       → T[ Subⁿ n e (paⁿ n a) ]
inSⁿ zero e x = inS (x 1=1) 
inSⁿ (suc n) e x i = inSⁿ n (e i) (x i)

outSⁿ : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]} → {e : Ie n}
       → {pa : T[ Partialⁿ n e A ]}
       → T[ Subⁿ n e pa ]
       → T[ cu n A ]
outSⁿ zero x = liftω (outS x)
outSⁿ (suc n) x i = outSⁿ n (x i)


⊆'I : ∀ {n} → Ie n → Ie n → (Typeω)
⊆'I {n} e₁ e₂ = ∀ {ℓ} → {A : T[ CType ℓ n ]}
                     → T[ Partialⁿ n e₂ A ]
                     → T[ Partialⁿ n e₁ A ] 

⊆I→⊆'I :  ∀ n → {x y : Ie n} → .(⊆I x y) → ⊆'I x y 
⊆I→⊆'I zero x x₁ x₃ = x₁ (x x₃)
⊆I→⊆'I (suc n) x y i = ⊆I→⊆'I n (x i) (y i)

⊆'1-∧ : ∀ {n} → (x y : Ie n) → ⊆'I (x ∧ⁿ y) x
⊆'1-∧ {zero} x y {ℓ} {A} x₂ = zz
  where
    zz : T[ Partialⁿ zero (x ∧ⁿ y) A ]
    zz (x = i1)(y = i1) = x₂ 1=1
⊆'1-∧ {suc n} x y {ℓ} {A} x₂ i = ⊆'1-∧ {n} (x i) (y i) (x₂ i)


⊆'2-∧ : ∀ {n} → (x y : Ie n) → ⊆'I (x ∧ⁿ y) y
⊆'2-∧ {zero} x y {ℓ} {A} x₂ = zz 
  where
    zz : T[ Partialⁿ zero (x ∧ⁿ y) A ]
    zz (x = i1)(y = i1) = x₂ 1=1
⊆'2-∧ {suc n} x y {ℓ} {A} x₂ i = ⊆'2-∧ {n} (x i) (y i) (x₂ i)

Partialⁿ-Sub : ∀ {ℓ} → ∀ n
               → {A : T[ CType ℓ n ]}
               → {i j : Ie n}
               → T[ Partialⁿ n (i ∧ⁿ j) A ] → ωType
T[_] (Partialⁿ-Sub zero {A} {i} {j} x) =
   .(i=1 : (IsOne i)) → Sub (lowerω A) (i ∧ j) x
(Partialⁿ-Sub zero {A} {i} {j} x ωType.≡ω x₁) x₂ =
   .(i=1 : (IsOne i)) → outS (x₁ i=1) ≡ outS (x₂ i=1) 
ωType.symω (Partialⁿ-Sub zero {A} {i} {j} x) x₁ i=1 = sym (x₁ i=1)
(Partialⁿ-Sub zero {A} {i} {j} x ωType.transω x₁) x₂ i=1 = x₁ i=1 ∙ x₂ i=1 

Partialⁿ-Sub (suc n) x = ∀I λ i → Partialⁿ-Sub n (x i)


inPartialⁿ-Sub : ∀ {ℓ} → ∀ n
               → {A : T[ CType ℓ n ]}
               → {i j : Ie n}
               → (a : T[ Partialⁿ n i A ])
               → T[ Partialⁿ-Sub n (⊆'1-∧ i j a) ]
inPartialⁿ-Sub zero a i=1 = inS (a i=1)
inPartialⁿ-Sub (suc n) a i = inPartialⁿ-Sub n (a i)


-- --------

Partial∨ :  ∀ {ℓ} → {A : Type ℓ} → (i j : I)
           → {xy : Partial (i ∧ j) A} 
           → ( .(i=1 : (IsOne i)) → (Sub A j (λ { (j = i1) → xy i=1  })))
           → ( .(j=1 : (IsOne j)) → (Sub A i (λ { (i = i1) → xy j=1  })))
           → Partial (i ∨ j) A
Partial∨ i j x y = primPOr i j (λ p → outS (x p)) (λ p → outS (y p))


Partialⁿ∨  :  ∀ {ℓ}  → ∀ n → {A : T[ CType ℓ n ]}
              → (i j : Ie n)
              → (∩a : T[ Partialⁿ n (i ∧ⁿ j) A ])
              → T[ Partialⁿ-Sub n ∩a ]
              → T[ Partialⁿ-Sub n (⊆I→⊆'I n (∧-comm j i) ∩a) ]
              → T[ Partialⁿ n (i ∨ⁿ j) A ]   
Partialⁿ∨ zero i j ∩a ai aj = primPOr i j (λ p → outS (ai p)) (λ p → outS (aj p))
Partialⁿ∨ (suc n) i j ∩a ai aj i' = Partialⁿ∨ n (i i') (j i') (∩a i') (ai i') (aj i')

-- -------

inSⁿ→-const : ∀ {ℓ ℓ'} → ∀ n → (e : Ie n) → (A : NCube n → Type ℓ) → (B : NCube n → Type ℓ')
      → (pa : T[ Partialⁿ (n) e Ct[ n , A ] ])
      → (f : ∀ c → B c) 
      →    T[
           Subⁿ n e
           (Partialⁿ-map→ n
            (paⁿ n cu→[ n , (λ c _ → f c) ]) (pa))
           ]
inSⁿ→-const zero e A B pa f = inS (f [])
inSⁿ→-const (suc n) e A B pa f i = inSⁿ→-const n (e i) (A i∷ i) (B i∷ i) (pa i) (f i∷ i)


Partialⁿ-attach-Ends :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
                      → (y : (j : I) → T[ Partialⁿ n e (A j) ])
                      → (end0 : T[ Subⁿ n _ (y i0) ])
                      → (end1 : T[ Subⁿ n _ (y i1) ])
                      → T[ Partialⁿ (suc n)
                                 ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
                                 A ] 
Partialⁿ-attach-Ends zero {e = e} y end0 end1 i = zzz
 where
   zzz : _
   zzz (i = i0) = outS end0
   zzz (i = i1) = outS end1
   zzz (e = i1) = y i 1=1
    
Partialⁿ-attach-Ends (suc zero) {A = A} {e = e} y end0 end1 i i₁ =
  Partialⁿ-attach-Ends (zero) {A = λ x → A x i₁} {e = e i₁}
                     (λ j x → y j i₁ x) (end0 i₁) ((end1 i₁)) i 
Partialⁿ-attach-Ends (suc (suc n)) {A = A} {e = e} y end0 end1 i i₁ =
  Partialⁿ-attach-Ends (suc n) {A = λ x → A x i₁} {e = λ x → e i₁ x}
                     (λ x → y x i₁) (λ x → end0 i₁ x) (λ x → end1 i₁ x) i




-- Partialⁿ-attach-Ends-swap :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
--                       → (y : I → (j : I) → T[ Partialⁿ n e (A j) ])
--                       → (end0 : ∀ i' → T[ Subⁿ n _ (y i' i0) ])
--                       → (end1 : ∀ i' → T[ Subⁿ n _ (y i' i1) ])
--                       → T[ Partialⁿ (suc n)
--                                  ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
--                                  A ] 
-- Partialⁿ-attach-Ends-swap zero {e = e} y end0 end1 i =
--   let z = {!(~ (i ∨ ~ i)) !} in
--     λ {
--      (i = i0) → outS (end0 z)
--    ; (i = i1) → outS (end1 z)
--    ; (e = i1) → y z i 1=1
--     }
-- Partialⁿ-attach-Ends-swap (suc zero) {A = A} {e = e} y end0 end1 i i₁ = {!!}
-- Partialⁿ-attach-Ends-swap (suc (suc n)) {A = A} {e = e} y end0 end1 i i₁ = {!!}



Partialⁿ-attach-Ends' :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
                      → (y : (j : I) → T[ Partialⁿ n e (A j) ])
                      → ((j : I) → T[ Subⁿ n e (y j) ])
                      → T[ Partialⁿ (suc n)
                                 ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
                                 A ] 
Partialⁿ-attach-Ends' zero {e = e} y x i =
    λ {
     (i = i0) → outS (x i0)
   ; (i = i1) → outS (x i1)
   ; (e = i1) → y i 1=1
    }
Partialⁿ-attach-Ends' (suc zero) {A = A} {e = e} y x i i₁ =
     Partialⁿ-attach-Ends' (zero) {A = λ x → A x i₁} {e = e i₁}
                     (λ j x → y j i₁ x) (λ j → x j i₁) i 
Partialⁿ-attach-Ends' (suc (suc n)) {A = A} {e = e} y x i i₁ =
     Partialⁿ-attach-Ends' (suc n) {A = λ x → A x i₁} {e = λ x → e i₁ x}
                     (λ j → y j i₁) (λ j → x j i₁) i

Subⁿ-attach-Ends' :  ∀ {ℓ} → ∀ n → {A : T[ CType ℓ (suc n) ]} → {e : Ie n}
                      → (y : (j : I) → T[ Partialⁿ n e (A j) ])
                      → (x : (i : I) → T[ Subⁿ n e (y i) ])
                      → T[ Subⁿ (suc n)
                             ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e)
                              (Partialⁿ-attach-Ends' n y x) ]
Subⁿ-attach-Ends' zero y x i = inS (outS (x i))
Subⁿ-attach-Ends' (suc zero) y x i i₁ =
   Subⁿ-attach-Ends' zero (λ j → y j i₁ ) (λ j → x j i₁) i
Subⁿ-attach-Ends' (suc (suc n)) y x i i₁ =
   Subⁿ-attach-Ends' (suc n) (λ j → y j i₁ ) (λ j → x j i₁) i



inSⁿ→i0 : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]}
        → {pa : T[ Partialⁿ n [ i0 ]Iexpr A ]}
        → T[ cu n A ]  →  T[ Subⁿ n i0ⁿ pa ]
inSⁿ→i0 zero a = inS (lowerω a)  
inSⁿ→i0 (suc n) a i = inSⁿ→i0 n (a i) 
-- -----

Boundaryω : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ n ]) → ωType
Boundaryω n A = Partialⁿ n (boundaryExpr n) A


Boundaryω-getFace : ∀ {ℓ} → ∀ n → ∀ k → ∀ b → (A : T[ CType ℓ (suc n) ])
          → T[ Boundaryω (suc n) A ]
          → T[ cu n (CType-face n k b A)  ]
Boundaryω-getFace zero zero false A x = x i0
Boundaryω-getFace zero zero true A x = x i1
Boundaryω-getFace (suc n) zero false A x =
 let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨2 {n = suc n} i0ⁿ i1ⁿ))
                   (⊆I-∨1 (i0ⁿ ∨ⁿ i1ⁿ) (boundaryExpr (suc n)))
                    )) (x i0)
 in Partialⁿ-i1-elim (suc n) z
Boundaryω-getFace (suc n) zero true A x =
   let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨1 {n = suc n} i1ⁿ i0ⁿ))
                   (⊆I-∨1 (i1ⁿ ∨ⁿ i0ⁿ) (boundaryExpr (suc n)))
                    )) (x i1)
 in Partialⁿ-i1-elim (suc n) z
  
Boundaryω-getFace zero (suc k) false A x = x i0
Boundaryω-getFace zero (suc k) true A x = x i1
Boundaryω-getFace (suc n) (suc k) b A x i =
  Boundaryω-getFace n k b (A i) (⊆I→⊆'I (suc n)
    (⊆I-∨2 _ (boundaryExpr (suc n))) (x i) )


Boundaryω-getFace' : ∀ {ℓ} → ∀ n → ℕ → Bool → {A : Type ℓ}
          → T[ Boundaryω (suc n) (Ct[ (suc n) , const A ]) ]
          → T[ cu n (Ct[ n , const A ])  ]
Boundaryω-getFace' zero zero false x = x i0
Boundaryω-getFace' zero zero true x = x i1
Boundaryω-getFace' (suc n) zero false x =
 let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨2 {n = suc n} i0ⁿ i1ⁿ))
                   (⊆I-∨1 (i0ⁿ ∨ⁿ i1ⁿ) (boundaryExpr (suc n)))
                    )) (x i0)
 in Partialⁿ-i1-elim (suc n) z
Boundaryω-getFace' (suc n) zero true x =
   let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨1 {n = suc n} i1ⁿ i0ⁿ))
                   (⊆I-∨1 (i1ⁿ ∨ⁿ i0ⁿ) (boundaryExpr (suc n)))
                    )) (x i1)
 in Partialⁿ-i1-elim (suc n) z
  
Boundaryω-getFace' zero (suc k) false x = x i0
Boundaryω-getFace' zero (suc k) true x = x i1
Boundaryω-getFace' (suc n) (suc k) b x i =
  Boundaryω-getFace' n k b (⊆I→⊆'I (suc n)
    (⊆I-∨2 _ (boundaryExpr (suc n))) (x i) )




Partialⁿ-getLid : ∀ {ℓ} → ∀ n → (e : Ie n) → ∀ b → (A : T[ CType ℓ (suc n) ])
          → T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ (↑Expr 1 e)) A ]
          → T[ cu n (A (Bool→I b))  ]
Partialⁿ-getLid zero e false A x = x i0
Partialⁿ-getLid zero e true A x = x i1
Partialⁿ-getLid (suc n) e false A x =
     let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨2 {n = suc n} i0ⁿ i1ⁿ))
                   (⊆I-∨1 (i0ⁿ ∨ⁿ i1ⁿ) (e))
                    )) (x i0)
 in Partialⁿ-i1-elim (suc n) z
Partialⁿ-getLid (suc n) e true A x =
     let z = (⊆I→⊆'I (suc n)
             ( ⊆I-trans (suc n) ((⊆I-∨1 {n = suc n} i1ⁿ i0ⁿ))
                   (⊆I-∨1 (i1ⁿ ∨ⁿ i0ⁿ) (e))
                    )) (x i1)
 in Partialⁿ-i1-elim (suc n) z


Boundaryω-getLid : ∀ {ℓ} → ∀ n → ∀ b → (A : T[ CType ℓ (suc n) ])
          → T[ Boundaryω (suc n) A ]
          → T[ cu n (A (Bool→I b))  ]
Boundaryω-getLid zero b A = Partialⁿ-getLid zero (boundaryExpr zero) b A
Boundaryω-getLid (suc n) b A = Partialⁿ-getLid (suc n) (boundaryExpr (suc n)) b A

InsideOfω : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]}
             → (x : T[ Boundaryω n A ]) → ωType
InsideOfω n x = Subⁿ n _ x


hcompⁿ :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ n ]}
            →  (sides : I → T[ Partialⁿ n e A ])
            → T[ Subⁿ n e (sides i0) ]
            → T[ Subⁿ n e (sides i1) ]
hcompⁿ zero sides x = inS (hcomp sides (outS x))
hcompⁿ (suc n) sides x i = hcompⁿ n (λ j → sides j i) (x i)

hfillⁿ :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ n ]}
            →  (sides : I → T[ Partialⁿ n e A ])
            → T[ Subⁿ n e (sides i0) ]
            → (i : I) → T[ Subⁿ n e (sides i) ]
hfillⁿ zero sides x i = inS (hfill sides x i)
hfillⁿ (suc n) sides x i i' = hfillⁿ n (λ x₁ → sides x₁ i') (x i') i

hcompⁿ≡ω :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ n ]}
            → {sides0 : T[ Partialⁿ n e A ]}
            → {sides1 : T[ Partialⁿ n e A ]}
            → ωType._≡ω_ (Partialⁿ n e A) sides0 sides1 
            → T[ Subⁿ n e (sides0) ]
            → T[ Subⁿ n e (sides1) ]
hcompⁿ≡ω zero s= x = inS (hcomp (λ i x₁ → s= x₁ i) (outS x))
hcompⁿ≡ω (suc n) s= x i = hcompⁿ≡ω n (s= i) (x i)


Partial-PathTy :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                → T[ Partialⁿ (suc n) (↑Expr 1 e) A ]
                → T[ CTypeP ℓ n e ]
Partial-PathTy zero {A = A} x e=1 = PathP (λ x₁ → A x₁ 1=1) (x i0 e=1) (x i1 e=1) 
Partial-PathTy (suc n) {e} {A} x i = Partial-PathTy n {e i} λ i₁ → x i₁ i

Partial-Path :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                → (a : T[ Partialⁿ (suc n) (↑Expr 1 e) A ])
                → T[ PartialPⁿ {ℓ} n e (Partial-PathTy n a)] 
Partial-Path zero a e=1 i = a i e=1
Partial-Path (suc n) a i = Partial-Path n λ i₁ → a i₁ i


Partial-SidesPathTy :  ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                → T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e) A ]
                → T[ CType ℓ n ]
Partial-SidesPathTy zero {A = A} a e=1 = PathP (λ i → A i 1=1) (a i0 1=1) (a i1 1=1)
Partial-SidesPathTy (suc n) a i = Partial-SidesPathTy n λ i₁ → a i₁ i

Partial-SidesPath : ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                → (a : T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e) A ])
                → T[ Partialⁿ {ℓ} n e (Partial-SidesPathTy n a)] 
Partial-SidesPath zero {e = e} a e=1 i = a i (IsOne2 (i ∨ ~ i) e e=1)
Partial-SidesPath (suc n) a i = Partial-SidesPath n λ i₁ → a i₁ i


sidesPath : ∀ {ℓ} → ∀ n → {e :  Ie n} → {A : T[ CType ℓ (suc n) ]}
                   → (a : T[ Partialⁿ (suc n) ((λ i → ([ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) ∨ⁿ ↑Expr 1 e) A ])
                   → T[ Partialⁿ {ℓ} n e
                          Ct[ n ,
                             (λ c → PathP (λ i → ((CType-ev (suc n) A) i∷ i) c)
                                     (from-cu (Partialⁿ-getLid n _ false A a) c)
                                     (from-cu (Partialⁿ-getLid n _ true A a) c))
                             ] ]
sidesPath zero {e = e} a e=1 i = a i (IsOne2 (i ∨ ~ i) e e=1)
sidesPath (suc zero) a i = sidesPath zero λ i₁ → a i₁ i
sidesPath (suc (suc n)) a i =  sidesPath (suc n) λ i₁ → a i₁ i

Boundaryω-getCyl : ∀ {ℓ} → ∀ n 
          → {A : T[ CType ℓ (suc n) ]}
          → (x : T[ Boundaryω (suc n) A ])
          → T[ Boundaryω n
                Ct[ n ,
                   (λ c → PathP (λ i → ((CType-ev (suc n) A) i∷ i) c)
                           (from-cu (Boundaryω-getLid n false A x) c)
                           (from-cu (Boundaryω-getLid n true A x) c))
                   ] ]
Boundaryω-getCyl zero x ()
Boundaryω-getCyl (suc n) x = sidesPath (suc n) x



InsideOfBω : ∀ {ℓ} → ∀ n → {A : T[ CType ℓ n ]}
             → (x : T[ Boundaryω n A ]) → Type ℓ
InsideOfBω zero {A = A} x = lowerω A
InsideOfBω (suc n) {A = A} x = PathP (λ i → Π ((CType-ev (suc n) A) i∷ i))
                               (from-cu (Boundaryω-getLid n false A x))
                               (from-cu (Boundaryω-getLid n true A x))

cylTy : ∀ {ℓ} → ∀ n → (A : T[ CType ℓ (suc n) ])
                 → (l0 : T[ cu (n) (A i0) ])
                 → (l1 : T[ cu (n) (A i1) ])
                 → ωType
cylTy n A l0 l1 = Boundaryω n 
                    Ct[ n ,
                   (λ c → PathP (λ i → ((CType-ev (suc n) A) i∷ i) c)
                           (from-cu l0 c)
                           (from-cu l1 c))
                      ] 

Boundaryω-map : ∀ {ℓ ℓ'} → ∀ n
                   → {A : T[ CType ℓ n ]}
                   → {B : T[ CType ℓ' n ]}
                   → T[ cu n (Cu→ n A B) ]
                   → T[ Boundaryω n (A) ]
                   → T[ Boundaryω n (B) ]
Boundaryω-map n f = Partialⁿ-map→ n (paⁿ n f)




appLastTy : ∀ {ℓ} → ∀ {n}
            → (A : NCube (suc n) → Type ℓ)
            → I → NCube n → Type ℓ
appLastTy {ℓ} {zero} A i c = A (inside i ∷ c)
appLastTy {ℓ} {suc n} A i c = appLastTy {n = n} (A ∘ ((head c) ∷_)) i (tail c)

appLast :  ∀ {ℓ} → ∀ {n}
           → {A : NCube (suc n) → Type ℓ}
           → (a : ∀ x → A x)
           → ∀ i → ∀ x → (appLastTy A i x)
appLast {ℓ} {zero} {A} a i c = a (inside i ∷ c)
appLast {ℓ} {suc n} {A} a i c = appLast {n = n} (a ∘ ((head c) ∷_)) i (tail c)


IsoInterval' : ∀ {ℓ} 
           → {A : Type ℓ}
           → Iso (Interval' → A)
                 (Σ[ y ∈ (Bool → A) ]
                     (y false) ≡ (y true) )
Iso.fun IsoInterval' x = (λ b → x (end b)) , (λ i → x (inside i))
Iso.inv IsoInterval' x (end x₁) = fst x x₁
Iso.inv IsoInterval' x (inside i) = snd x i
fst (Iso.rightInv IsoInterval' b i) b₁ = fst b b₁
snd (Iso.rightInv IsoInterval' b i) = snd b
Iso.leftInv IsoInterval' b i (end x) = b (end x)
Iso.leftInv IsoInterval' b i (inside i₁) = b (inside i₁)


IsoIntervalP' : ∀ {ℓ} 
           → {A : Interval' → Type ℓ}
           → Iso (∀ x → A x)
                 (Σ[ y ∈ (∀ b → A (end b)) ]
                    PathP (λ i → A (inside i)) (y false) (y true) )
Iso.fun IsoIntervalP' x = (λ b → x (end b)) , (λ i → x (inside i))
Iso.inv IsoIntervalP' x (end x₁) = fst x x₁
Iso.inv IsoIntervalP' x (inside i) = snd x i
fst (Iso.rightInv IsoIntervalP' b i) b₁ = fst b b₁
snd (Iso.rightInv IsoIntervalP' b i) = snd b
Iso.leftInv IsoIntervalP' b i (end x) = b (end x)
Iso.leftInv IsoIntervalP' b i (inside i₁) = b (inside i₁)

-- fromVecIso : ∀ ℓ ℓ' → {A : Type ℓ} → {B : Type ℓ'}
--               →  ∀ n m
--               → Iso (Vec A n → Vec A m → B) (Vec A (n + m) → B)
-- fromVecIso ℓ ℓ' n m = {!!}

iso-popTy : ∀ {ℓa ℓ} → ∀ {n} → ∀ {A : Type ℓa}  
              → Iso (Vec A (suc n) → Type ℓ) (Vec A n → A → Type ℓ)
Iso.fun iso-popTy x x₁ x₂ = x (x₁ ∷ₗ x₂) 
Iso.inv iso-popTy x x₁ = x (removeLast x₁) (last x₁)
Iso.rightInv iso-popTy b i x x₁ =
 let h = removeLast-last x x₁
 in b (fst h (~ i)) (snd h (~ i))
Iso.leftInv iso-popTy a i x = a (last-removeLast x i) 

subst-removeLast : ∀ {ℓa ℓ} → ∀ {A : Type ℓa} → ∀ {n} → {B : Vec A (suc n) → Type ℓ}
                       → (f : (x₂ : Vec A n) (a : A) → B (x₂ ∷ₗ a))
                       → ∀ x → B x
subst-removeLast {n = zero} f (x ∷ []) = f [] x 
subst-removeLast {n = suc n} {B = B} f (x ∷ x₁) =
  subst-removeLast {n = n} {B = B ∘ (x ∷_)} (λ x₃ a → f (x ∷ x₃) a) x₁

-- iso-pop : ∀ {ℓa ℓ} → ∀ {n} → ∀ {A : Type ℓa} → {B : Vec A (suc n) → Type ℓ}
--             → Iso (∀ x → B x) ( ∀ x → ∀ a → (Iso.fun iso-popTy B) x a) 
-- Iso.fun iso-pop  x x₁ x₂ = x (x₁ ∷ₗ x₂) 
-- Iso.inv (iso-pop {B = B}) x x₁ = subst-removeLast x x₁

-- Iso.rightInv iso-pop b i x a = {!!}
-- Iso.leftInv iso-pop a i x = {!  !}


