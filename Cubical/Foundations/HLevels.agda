{-

Basic theory about h-levels/n-types:

- Basic properties of isContr, isProp and isSet (definitions are in Prelude)

- Hedberg's theorem can be found in Cubical/Relation/Nullary/Properties

-}
module Cubical.Foundations.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence using (ua ; univalenceIso)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat   using (ℕ; zero; suc; _+_; +-zero; +-comm)

open Iso

HLevel : Type₀
HLevel = ℕ

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
    A A' : Type ℓ
    B : A → Type ℓ
    C : (x : A) → B x → Type ℓ
    D : (x : A) (y : B x) → C x y → Type ℓ
    E : (x : A) (y : B x) → (z : C x y) → D x y z → Type ℓ
    F : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) → Type ℓ
    G : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) (u : F x y z w v) → Type ℓ
    w x y z : A
    n : HLevel

isOfHLevel : HLevel → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

isOfHLevelFun : (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isOfHLevelFun n f = ∀ b → isOfHLevel n (fiber f b)

isOfHLevelΩ→isOfHLevel :
  ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → ((x : A) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (2 + n) A
isOfHLevelΩ→isOfHLevel zero hΩ x y =
  J (λ y p → (q : x ≡ y) → p ≡ q) (hΩ x refl)
isOfHLevelΩ→isOfHLevel (suc n) hΩ x y =
  J (λ y p → (q : x ≡ y) → isOfHLevel (suc n) (p ≡ q)) (hΩ x refl)

TypeOfHLevel : ∀ ℓ → HLevel → Type (ℓ-suc ℓ)
TypeOfHLevel ℓ n = TypeWithStr ℓ (isOfHLevel n)

hProp hSet hGroupoid h2Groupoid : ∀ ℓ → Type (ℓ-suc ℓ)
hProp      ℓ = TypeOfHLevel ℓ 1
hSet       ℓ = TypeOfHLevel ℓ 2
hGroupoid  ℓ = TypeOfHLevel ℓ 3
h2Groupoid ℓ = TypeOfHLevel ℓ 4

-- lower h-levels imply higher h-levels

isOfHLevelSuc : (n : HLevel) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc 0 = isContr→isProp
isOfHLevelSuc 1 = isProp→isSet
isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)

isSet→isGroupoid : isSet A → isGroupoid A
isSet→isGroupoid = isOfHLevelSuc 2

isGroupoid→is2Groupoid : isGroupoid A → is2Groupoid A
isGroupoid→is2Groupoid = isOfHLevelSuc 3

isOfHLevelPlus : (m : HLevel) → isOfHLevel n A → isOfHLevel (m + n) A
isOfHLevelPlus zero hA = hA
isOfHLevelPlus (suc m) hA = isOfHLevelSuc _ (isOfHLevelPlus m hA)

isContr→isOfHLevel : (n : HLevel) → isContr A → isOfHLevel n A
isContr→isOfHLevel zero cA = cA
isContr→isOfHLevel (suc n) cA = isOfHLevelSuc _ (isContr→isOfHLevel n cA)

isProp→isOfHLevelSuc : (n : HLevel) → isProp A → isOfHLevel (suc n) A
isProp→isOfHLevelSuc zero pA = pA
isProp→isOfHLevelSuc (suc n) pA = isOfHLevelSuc _ (isProp→isOfHLevelSuc n pA)

isOfHLevelPlus' : (m : HLevel) → isOfHLevel m A → isOfHLevel (m + n) A
isOfHLevelPlus' {n = n} 0 = isContr→isOfHLevel n
isOfHLevelPlus' {n = n} 1 = isProp→isOfHLevelSuc n
isOfHLevelPlus' {n = n} (suc (suc m)) hA a₀ a₁ = isOfHLevelPlus' (suc m) (hA a₀ a₁)

-- When proving a type has h-level n+1, we can assume it is inhabited.
-- To prove a type is a proposition, it suffices to prove it is contractible if inhabited

isOfHLevelSucIfInhabited→isOfHLevelSuc : ∀ n
  → (A → isOfHLevel (suc n) A) → isOfHLevel (suc n) A
isOfHLevelSucIfInhabited→isOfHLevelSuc zero hA a = hA a a
isOfHLevelSucIfInhabited→isOfHLevelSuc (suc n) hA a = hA a a

isContrIfInhabited→isProp : (A → isContr A) → isProp A
isContrIfInhabited→isProp hA =
  isOfHLevelSucIfInhabited→isOfHLevelSuc 0 (isContr→isProp ∘ hA)

-- hlevel of path types

isProp→isContrPath : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath h x y = h x y , isProp→isSet h x y _

isContr→isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath cA = isProp→isContrPath (isContr→isProp cA)

isOfHLevelPath' : (n : HLevel) → isOfHLevel (suc n) A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath' 0 = isProp→isContrPath
isOfHLevelPath' (suc n) h x y = h x y

isOfHLevelPath'⁻ : (n : HLevel) → ((x y : A) → isOfHLevel n (x ≡ y)) → isOfHLevel (suc n) A
isOfHLevelPath'⁻ zero h x y = h x y .fst
isOfHLevelPath'⁻ (suc n) h = h

isOfHLevelPath : (n : HLevel) → isOfHLevel n A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath 0 h x y = isContr→isContrPath h x y
isOfHLevelPath (suc n) h x y = isOfHLevelSuc n (isOfHLevelPath' n h x y)

-- h-level of isOfHLevel

isPropIsOfHLevel : (n : HLevel) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 = isPropIsContr
isPropIsOfHLevel 1 = isPropIsProp
isPropIsOfHLevel (suc (suc n)) f g i a b =
  isPropIsOfHLevel (suc n) (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet = isPropIsOfHLevel 2

isPropIsGroupoid : isProp (isGroupoid A)
isPropIsGroupoid = isPropIsOfHLevel 3

isPropIs2Groupoid : isProp (is2Groupoid A)
isPropIs2Groupoid = isPropIsOfHLevel 4

TypeOfHLevel≡ : (n : HLevel) {X Y : TypeOfHLevel ℓ n} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
TypeOfHLevel≡ n = Σ≡Prop (λ _ → isPropIsOfHLevel n)

-- hlevels are preserved by equalities

≡-from-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n A → isOfHLevel n B
≡-from-isOfHLevel→isOfHLevel {n = n} = subst (isOfHLevel n)

≡-to-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n B → isOfHLevel n A
≡-to-isOfHLevel→isOfHLevel {n = n} = subst⁻ (isOfHLevel n)

≡-to-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr B → isContr A
≡-to-isContr→isContr = ≡-to-isOfHLevel→isOfHLevel {n = 0}

≡-from-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr A → isContr B
≡-from-isContr→isContr = ≡-from-isOfHLevel→isOfHLevel {n = 0}

≡-to-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp B → isProp A
≡-to-isProp→isProp = ≡-to-isOfHLevel→isOfHLevel {n = 1}

≡-from-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp A → isProp B
≡-from-isProp→isProp = ≡-from-isOfHLevel→isOfHLevel {n = 1}

≡-to-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet B → isSet A
≡-to-isSet→isSet = ≡-to-isOfHLevel→isOfHLevel {n = 2}

≡-from-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet A → isSet B
≡-from-isSet→isSet = ≡-from-isOfHLevel→isOfHLevel {n = 2}



-- hlevels are preserved by retracts (and consequently equivalences)

isContrRetract
  : ∀ {B : Type ℓ}
  → (f : A → B) (g : B → A)
  → (h : retract f g)
  → (v : isContr B) → isContr A
fst (isContrRetract f g h (b , p)) = g b
snd (isContrRetract f g h (b , p)) x = (cong g (p (f x))) ∙ (h x)

isPropRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isProp B → isProp A
isPropRetract f g h p x y i =
  hcomp
    (λ j → λ
      { (i = i0) → h x j
      ; (i = i1) → h y j})
    (g (p (f x) (f y) i))

isSetRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isSet B → isSet A
isSetRetract f g h set x y p q i j =
  hcomp (λ k → λ { (i = i0) → h (p j) k
                 ; (i = i1) → h (q j) k
                 ; (j = i0) → h x k
                 ; (j = i1) → h y k})
        (g (set (f x) (f y)
                (cong f p) (cong f q) i j))

isGroupoidRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isGroupoid B → isGroupoid A
isGroupoidRetract f g h grp x y p q P Q i j k =
  hcomp ((λ l → λ { (i = i0) → h (P j k) l
                  ; (i = i1) → h (Q j k) l
                  ; (j = i0) → h (p k) l
                  ; (j = i1) → h (q k) l
                  ; (k = i0) → h x l
                  ; (k = i1) → h y l}))
       (g (grp (f x) (f y) (cong f p) (cong f q)
                           (cong (cong f) P) (cong (cong f) Q) i j k))

is2GroupoidRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → is2Groupoid B → is2Groupoid A
is2GroupoidRetract f g h grp x y p q P Q R S i j k l =
  hcomp (λ r → λ { (i = i0) → h (R j k l) r
                 ; (i = i1) → h (S j k l) r
                 ; (j = i0) → h (P k l) r
                 ; (j = i1) → h (Q k l) r
                 ; (k = i0) → h (p l) r
                 ; (k = i1) → h (q l) r
                 ; (l = i0) → h x r
                 ; (l = i1) → h y r})
       (g (grp (f x) (f y) (cong f p) (cong f q)
               (cong (cong f) P) (cong (cong f) Q)
               (cong (cong (cong f)) R) (cong (cong (cong f)) S) i j k l))

isOfHLevelRetract
  : (n : HLevel) {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isOfHLevel n B → isOfHLevel n A
isOfHLevelRetract 0 = isContrRetract
isOfHLevelRetract 1 = isPropRetract
isOfHLevelRetract 2 = isSetRetract
isOfHLevelRetract 3 = isGroupoidRetract
isOfHLevelRetract 4 = is2GroupoidRetract
isOfHLevelRetract (suc (suc (suc (suc (suc n))))) f g h ofLevel x y p q P Q R S =
  isOfHLevelRetract (suc n) (cong (cong (cong (cong f))))
                    (λ s i j k l →
                      hcomp (λ r → λ { (i = i0) → h (R j k l) r
                                     ; (i = i1) → h (S j k l) r
                                     ; (j = i0) → h (P k l) r
                                     ; (j = i1) → h (Q k l) r
                                     ; (k = i0) → h (p l) r
                                     ; (k = i1) → h (q l) r
                                     ; (l = i0) → h x r
                                     ; (l = i1) → h y r})
                            (g (s i j k l)))
                    (λ s i j k l m →
                    hcomp (λ n → λ { (i = i1) → s j k l m
                                   ; (j = i0) → h (R k l m) (i ∨ n)
                                   ; (j = i1) → h (S k l m) (i ∨ n)
                                   ; (k = i0) → h (P l m) (i ∨ n)
                                   ; (k = i1) → h (Q l m) (i ∨ n)
                                   ; (l = i0) → h (p m) (i ∨ n)
                                   ; (l = i1) → h (q m) (i ∨ n)
                                   ; (m = i0) → h x (i ∨ n)
                                   ; (m = i1) → h y (i ∨ n) })
                          (h (s j k l m) i))
                    (ofLevel (f x) (f y)
                             (cong f p) (cong f q)
                             (cong (cong f) P) (cong (cong f) Q)
                             (cong (cong (cong f)) R) (cong (cong (cong f)) S))

isOfHLevelRetractFromIso : {A : Type ℓ} {B : Type ℓ'} (n : HLevel) → Iso A B → isOfHLevel n B → isOfHLevel n A
isOfHLevelRetractFromIso n e hlev = isOfHLevelRetract n (Iso.fun e) (Iso.inv e) (Iso.ret e) hlev

isOfHLevelRespectEquiv : {A : Type ℓ} {B : Type ℓ'} → (n : HLevel) → A ≃ B → isOfHLevel n A → isOfHLevel n B
isOfHLevelRespectEquiv n eq = isOfHLevelRetract n (invEq eq) (eq .fst) (secEq eq)

isContrRetractOfConstFun : {A : Type ℓ} {B : Type ℓ'} (b₀ : B)
   → Σ[ f ∈ (B → A) ] ((x : A) → (f ∘ (λ _ → b₀)) x ≡ x)
   → isContr A
fst (isContrRetractOfConstFun b₀ ret) = ret .fst b₀
snd (isContrRetractOfConstFun b₀ ret) y = ret .snd y

-- h-level of dependent path types

isOfHLevelPathP' : {A : I → Type ℓ} (n : HLevel)
                   → isOfHLevel (suc n) (A i1)
                   → (x : A i0) (y : A i1) → isOfHLevel n (PathP A x y)
isOfHLevelPathP' {A = A} n h x y =
  isOfHLevelRetractFromIso n (PathPIsoPath _ x y) (isOfHLevelPath' n h _ _)

isOfHLevelPathP : {A : I → Type ℓ} (n : HLevel)
                  → isOfHLevel n (A i1)
                  → (x : A i0) (y : A i1) → isOfHLevel n (PathP A x y)
isOfHLevelPathP {A = A} n h x y =
  isOfHLevelRetractFromIso n (PathPIsoPath _ x y) (isOfHLevelPath n h _ _)

-- Fillers for cubes from h-level

isSet→SquareP :
  {A : I → I → Type ℓ}
  (isSet : (i j : I) → isSet (A i j))
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
isSet→SquareP isset a₀₋ a₁₋ a₋₀ a₋₁ =
  PathPIsoPath _ _ _ .Iso.inv (isOfHLevelPathP' 1 (isset _ _) _ _ _ _ )

isGroupoid→isGroupoid' : isGroupoid A → isGroupoid' A
isGroupoid→isGroupoid' {A = A} Agpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathPIsoPath (λ i → Square (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋ .Iso.inv
    (isGroupoid→isPropSquare _ _ _ _ _ _)
  where
  isGroupoid→isPropSquare :
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → isProp (Square a₀₋ a₁₋ a₋₀ a₋₁)
  isGroupoid→isPropSquare a₀₋ a₁₋ a₋₀ a₋₁ =
    isOfHLevelRetractFromIso 1 (PathPIsoPath (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋) (Agpd _ _ _ _)

isGroupoid'→isGroupoid : isGroupoid' A → isGroupoid A
isGroupoid'→isGroupoid Agpd' x y p q r s = Agpd' r s refl refl refl refl
-- h-level of Σ-types

isProp∃! : isProp (∃! A B)
isProp∃! = isPropIsContr

isContrΣ : isContr A → ((x : A) → isContr (B x)) → isContr (Σ A B)
isContrΣ {A = A} {B = B} (a , p) q =
  let h : (x : A) (y : B x) → (q x) .fst ≡ y
      h x y = (q x) .snd y
  in (( a , q a .fst)
     , ( λ x i → p (x .fst) i
       , h (p (x .fst) i) (transp (λ j → B (p (x .fst) (i ∨ ~ j))) i (x .snd)) i))

isContrΣ' : (ca : isContr A) → isContr (B (fst ca)) → isContr (Σ A B)
isContrΣ' ca cb = isContrΣ ca (λ x → subst _ (snd ca x) cb)

section-Σ≡Prop
  : (pB : (x : A) → isProp (B x)) {u v : Σ A B}
  → section (Σ≡Prop pB {u} {v}) (cong fst)
section-Σ≡Prop {A = A} pB {u} {v} p j i =
  (p i .fst) , isProp→PathP (λ i → isOfHLevelPath 1 (pB (fst (p i)))
                                       (Σ≡Prop pB {u} {v} (cong fst p) i .snd)
                                       (p i .snd) )
                                       refl refl i j

isEquiv-Σ≡Prop
  : (pB : (x : A) → isProp (B x)) {u v : Σ A B}
  → isEquiv (Σ≡Prop pB {u} {v})
isEquiv-Σ≡Prop {A = A} pB {u} {v} = isoToIsEquiv (iso (Σ≡Prop pB) (cong fst) (section-Σ≡Prop pB) (λ _ → refl))

isPropΣ : isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ pA pB t u = Σ≡Prop pB (pA (t .fst) (u .fst))

isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x))
                  → isOfHLevel n (Σ A B)
isOfHLevelΣ 0 = isContrΣ
isOfHLevelΣ 1 = isPropΣ
isOfHLevelΣ {B = B} (suc (suc n)) h1 h2 x y =
  isOfHLevelRetractFromIso (suc n)
    (invIso (IsoΣPathTransportPathΣ _ _))
    (isOfHLevelΣ (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)

isSetΣ : isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
isSetΣ = isOfHLevelΣ 2

-- Useful consequence
isSetΣSndProp : isSet A → ((x : A) → isProp (B x)) → isSet (Σ A B)
isSetΣSndProp h p = isSetΣ h (λ x → isProp→isSet (p x))

isGroupoidΣ : isGroupoid A → ((x : A) → isGroupoid (B x)) → isGroupoid (Σ A B)
isGroupoidΣ = isOfHLevelΣ 3

is2GroupoidΣ : is2Groupoid A → ((x : A) → is2Groupoid (B x)) → is2Groupoid (Σ A B)
is2GroupoidΣ = isOfHLevelΣ 4

-- h-level of ×

isProp× : {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → isProp (A × B)
isProp× pA pB = isPropΣ pA (λ _ → pB)

isProp×2 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → isProp A → isProp B → isProp C → isProp (A × B × C)
isProp×2 pA pB pC = isProp× pA (isProp× pB pC)

isProp×3 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
         → isProp A → isProp B → isProp C → isProp D → isProp (A × B × C × D)
isProp×3 pA pB pC pD = isProp×2 pA pB (isProp× pC pD)

isProp×4 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} {E : Type ℓ''''}
         → isProp A → isProp B → isProp C → isProp D → isProp E → isProp (A × B × C × D × E)
isProp×4 pA pB pC pD pE = isProp×3 pA pB pC (isProp× pD pE)

isProp×5 : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} {E : Type ℓ''''} {F : Type ℓ'''''}
         → isProp A → isProp B → isProp C → isProp D → isProp E → isProp F
         → isProp (A × B × C × D × E × F)
isProp×5 pA pB pC pD pE pF = isProp×4 pA pB pC pD (isProp× pE pF)


isOfHLevel× : ∀ {A : Type ℓ} {B : Type ℓ'} n → isOfHLevel n A → isOfHLevel n B
                                             → isOfHLevel n (A × B)
isOfHLevel× n hA hB = isOfHLevelΣ n hA (λ _ → hB)

isSet× : ∀ {A : Type ℓ} {B : Type ℓ'} → isSet A → isSet B → isSet (A × B)
isSet× = isOfHLevel× 2

isGroupoid× : ∀ {A : Type ℓ} {B : Type ℓ'} → isGroupoid A → isGroupoid B
                                           → isGroupoid (A × B)
isGroupoid× = isOfHLevel× 3

is2Groupoid× : ∀ {A : Type ℓ} {B : Type ℓ'} → is2Groupoid A → is2Groupoid B
                                            → is2Groupoid (A × B)
is2Groupoid× = isOfHLevel× 4

-- h-level of Π-types

isOfHLevelΠ : ∀ n → ((x : A) → isOfHLevel n (B x))
                  → isOfHLevel n ((x : A) → B x)
isOfHLevelΠ 0 h = (λ x → fst (h x)) , λ f i y → snd (h y) (f y) i
isOfHLevelΠ 1 h f g i x = (h x) (f x) (g x) i
isOfHLevelΠ 2 h f g F G i j z = h z (f z) (g z) (funExt⁻ F z) (funExt⁻ G z) i j
isOfHLevelΠ 3 h f g p q P Q i j k z =
  h z (f z) (g z)
      (funExt⁻ p z) (funExt⁻ q z)
      (cong (λ f → funExt⁻ f z) P) (cong (λ f → funExt⁻ f z) Q) i j k
isOfHLevelΠ 4 h f g p q P Q R S i j k l z =
  h z (f z) (g z)
      (funExt⁻ p z) (funExt⁻ q z)
      (cong (λ f → funExt⁻ f z) P) (cong (λ f → funExt⁻ f z) Q)
      (cong (cong (λ f → funExt⁻ f z)) R) (cong (cong (λ f → funExt⁻ f z)) S) i j k l
isOfHLevelΠ (suc (suc (suc (suc (suc n))))) h f g p q P Q R S =
  isOfHLevelRetract (suc n)
    (cong (cong (cong funExt⁻))) (cong (cong (cong funExt))) (λ _ → refl)
    (isOfHLevelΠ (suc (suc (suc (suc n)))) (λ x → h x (f x) (g x))
                  (funExt⁻ p) (funExt⁻ q)
                  (cong funExt⁻ P) (cong funExt⁻ Q)
                  (cong (cong funExt⁻) R) (cong (cong funExt⁻) S))

isOfHLevelΠ2 : (n : HLevel) → ((x : A) → (y : B x) → isOfHLevel n (C x y))
             → isOfHLevel n ((x : A) → (y : B x) → C x y)
isOfHLevelΠ2 n f = isOfHLevelΠ n (λ x → isOfHLevelΠ n (f x))

isContrΠ : (h : (x : A) → isContr (B x)) → isContr ((x : A) → B x)
isContrΠ = isOfHLevelΠ 0

isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ = isOfHLevelΠ 1

isPropΠ2 : (h : (x : A) (y : B x) → isProp (C x y))
         → isProp ((x : A) (y : B x) → C x y)
isPropΠ2 h = isPropΠ λ x → isPropΠ λ y → h x y

isPropΠ3 : (h : (x : A) (y : B x) (z : C x y) → isProp (D x y z))
         → isProp ((x : A) (y : B x) (z : C x y) → D x y z)
isPropΠ3 h = isPropΠ λ x → isPropΠ λ y → isPropΠ λ z → h x y z

isPropΠ4 : (h : (x : A) (y : B x) (z : C x y) (w : D x y z) → isProp (E x y z w))
            → isProp ((x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w)
isPropΠ4 h = isPropΠ λ _ → isPropΠ3 (h _)

isPropΠ5 : (h : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) → isProp (F x y z w v))
            → isProp ((x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) → F x y z w v)
isPropΠ5 h = isPropΠ λ _ → isPropΠ4 (h _)

isPropΠ6 : (h : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) (u : F x y z w v) → isProp (G x y z w v u))
            → isProp ((x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) (u : F x y z w v) → G x y z w v u)
isPropΠ6 h = isPropΠ λ _ → isPropΠ5 (h _)

isPropImplicitΠ : (h : (x : A) → isProp (B x)) → isProp ({x : A} → B x)
isPropImplicitΠ h f g i {x} = h x (f {x}) (g {x}) i

isPropImplicitΠ2 : (h : (x : A) (y : B x) → isProp (C x y)) → isProp ({x : A} {y : B x} → C x y)
isPropImplicitΠ2 h = isPropImplicitΠ (λ x → isPropImplicitΠ (λ y → h x y))

isPropImplicitΠ3 : (h : (x : A) (y : B x) (z : C x y) → isProp (D x y z)) →
    isProp ({x : A} {y : B x} {z : C x y} → D x y z)
isPropImplicitΠ3 h = isPropImplicitΠ (λ x → isPropImplicitΠ2 (λ y → h x y))

isPropImplicitΠ4 : (h : (x : A) (y : B x) (z : C x y) (w : D x y z) → isProp (E x y z w)) →
    isProp ({x : A} {y : B x} {z : C x y} {w : D x y z} → E x y z w)
isPropImplicitΠ4 h = isPropImplicitΠ (λ x → isPropImplicitΠ3 (λ y → h x y))

isProp→ : {A : Type ℓ} {B : Type ℓ'} → isProp B → isProp (A → B)
isProp→ pB = isPropΠ λ _ → pB

isSetΠ : ((x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ = isOfHLevelΠ 2

isSetImplicitΠ : (h : (x : A) → isSet (B x)) → isSet ({x : A} → B x)
isSetImplicitΠ h f g F G i j {x} = h x (f {x}) (g {x}) (λ i → F i {x}) (λ i → G i {x}) i j

isSetImplicitΠ2 : (h : (x : A) → (y : B x) → isSet (C x y)) → isSet ({x : A} → {y : B x} → C x y)
isSetImplicitΠ2 h = isSetImplicitΠ (λ x → isSetImplicitΠ (λ y → h x y))

isSetImplicitΠ3 : (h : (x : A) → (y : B x) → (z : C x y) → isSet (D x y z)) →
    isSet ({x : A} → {y : B x} → {z : C x y} → D x y z)
isSetImplicitΠ3 h = isSetImplicitΠ (λ x → isSetImplicitΠ2 (λ y → λ z → h x y z))

isSet→ : isSet A' → isSet (A → A')
isSet→ isSet-A' = isOfHLevelΠ 2 (λ _ → isSet-A')

isSetΠ2 : (h : (x : A) (y : B x) → isSet (C x y))
        → isSet ((x : A) (y : B x) → C x y)
isSetΠ2 h = isSetΠ λ x → isSetΠ λ y → h x y

isSetΠ3 : (h : (x : A) (y : B x) (z : C x y) → isSet (D x y z))
         → isSet ((x : A) (y : B x) (z : C x y) → D x y z)
isSetΠ3 h = isSetΠ λ x → isSetΠ λ y → isSetΠ λ z → h x y z

isGroupoidΠ : ((x : A) → isGroupoid (B x)) → isGroupoid ((x : A) → B x)
isGroupoidΠ = isOfHLevelΠ 3

isGroupoidΠ2 : (h : (x : A) (y : B x) → isGroupoid (C x y)) → isGroupoid ((x : A) (y : B x) → C x y)
isGroupoidΠ2 h = isGroupoidΠ λ _ → isGroupoidΠ λ _ → h _ _

isGroupoidΠ3 : (h : (x : A) (y : B x) (z : C x y) → isGroupoid (D x y z))
            → isGroupoid ((x : A) (y : B x) (z : C x y) → D x y z)
isGroupoidΠ3 h = isGroupoidΠ λ _ → isGroupoidΠ2 λ _ → h _ _

isGroupoidΠ4 : (h : (x : A) (y : B x) (z : C x y) (w : D x y z) → isGroupoid (E x y z w))
            → isGroupoid ((x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w)
isGroupoidΠ4 h = isGroupoidΠ λ _ → isGroupoidΠ3 λ _ → h _ _

is2GroupoidΠ : ((x : A) → is2Groupoid (B x)) → is2Groupoid ((x : A) → B x)
is2GroupoidΠ = isOfHLevelΠ 4

isOfHLevelΠ⁻ : ∀ {A : Type ℓ} {B : Type ℓ'} n
             → isOfHLevel n (A → B) → (A → isOfHLevel n B)
isOfHLevelΠ⁻ 0 h x = fst h x , λ y → funExt⁻ (snd h (const y)) x
isOfHLevelΠ⁻ 1 h x y z = funExt⁻ (h (const y) (const z)) x
isOfHLevelΠ⁻ (suc (suc n)) h x y z =
  isOfHLevelΠ⁻ (suc n) (isOfHLevelRetractFromIso (suc n) funExtIso (h _ _)) x

isOfHLevel→∙ : {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ)
  → isOfHLevel n (fst B) → isOfHLevel n (A →∙ B)
isOfHLevel→∙ n hlev =
  isOfHLevelΣ n (isOfHLevelΠ n (λ _ → hlev))
    λ _ → isOfHLevelPath n hlev _ _

-- h-level of A ≃ B and A ≡ B

isOfHLevel≃
  : ∀ n {A : Type ℓ} {B : Type ℓ'}
  → (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≃ B)
isOfHLevel≃ zero {A = A} {B = B} hA hB = isContr→Equiv hA hB , contr
  where
  contr : (y : A ≃ B) → isContr→Equiv hA hB ≡ y
  contr y = Σ≡Prop isPropIsEquiv (funExt (λ a → snd hB (fst y a)))

isOfHLevel≃ (suc n) {A = A} {B = B} hA hB =
  isOfHLevelΣ (suc n) (isOfHLevelΠ _ λ _ → hB)
              (λ f → isProp→isOfHLevelSuc n (isPropIsEquiv f))

isOfHLevel≡ : ∀ n → {A B : Type ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≡ B)
isOfHLevel≡ n hA hB = isOfHLevelRetractFromIso n univalenceIso (isOfHLevel≃ n hA hB)

isOfHLevel⁺≃ₗ
  : ∀ n {A : Type ℓ} {B : Type ℓ'}
  → isOfHLevel (suc n) A → isOfHLevel (suc n) (A ≃ B)
isOfHLevel⁺≃ₗ zero pA e = isOfHLevel≃ 1 pA (isOfHLevelRespectEquiv 1 e pA) e
isOfHLevel⁺≃ₗ (suc n) hA e = isOfHLevel≃ m hA (isOfHLevelRespectEquiv m e hA) e
  where
  m = suc (suc n)

isOfHLevel⁺≃ᵣ
  : ∀ n {A : Type ℓ} {B : Type ℓ'}
  → isOfHLevel (suc n) B → isOfHLevel (suc n) (A ≃ B)
isOfHLevel⁺≃ᵣ zero pB e
  = isOfHLevel≃ 1 (isPropRetract (e .fst) (invEq e) (retEq e) pB) pB e
isOfHLevel⁺≃ᵣ (suc n) hB e
  = isOfHLevel≃ m (isOfHLevelRetract m (e .fst) (invEq e) (retEq e) hB) hB e
  where
  m = suc (suc n)

isOfHLevel⁺≡ₗ
  : ∀ n → {A B : Type ℓ}
  → isOfHLevel (suc n) A → isOfHLevel (suc n) (A ≡ B)
isOfHLevel⁺≡ₗ zero pA P = isOfHLevel≡ 1 pA (subst isProp P pA) P
isOfHLevel⁺≡ₗ (suc n) hA P
  = isOfHLevel≡ m hA (subst (isOfHLevel m) P hA) P
  where
  m = suc (suc n)

isOfHLevel⁺≡ᵣ
  : ∀ n → {A B : Type ℓ}
  → isOfHLevel (suc n) B → isOfHLevel (suc n) (A ≡ B)
isOfHLevel⁺≡ᵣ zero pB P = isOfHLevel≡ 1 (subst⁻ isProp P pB) pB P
isOfHLevel⁺≡ᵣ (suc n) hB P
  = isOfHLevel≡ m (subst⁻ (isOfHLevel m) P hB) hB P
  where
  m = suc (suc n)

-- h-level of TypeOfHLevel

isPropHContr : isProp (TypeOfHLevel ℓ 0)
isPropHContr x y = Σ≡Prop (λ _ → isPropIsContr) (isOfHLevel≡ 0 (x .snd) (y .snd) .fst)

isOfHLevelTypeOfHLevel : ∀ n → isOfHLevel (suc n) (TypeOfHLevel ℓ n)
isOfHLevelTypeOfHLevel zero = isPropHContr
isOfHLevelTypeOfHLevel (suc n) (X , a) (Y , b) =
  isOfHLevelRetract (suc n) (cong fst) (Σ≡Prop λ _ → isPropIsOfHLevel (suc n))
    (section-Σ≡Prop λ _ → isPropIsOfHLevel (suc n))
    (isOfHLevel≡ (suc n) a b)

isSetHProp : isSet (hProp ℓ)
isSetHProp = isOfHLevelTypeOfHLevel 1

isGroupoidHSet : isGroupoid (hSet ℓ)
isGroupoidHSet = isOfHLevelTypeOfHLevel 2


-- h-level of lifted type

isOfHLevelLift : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} → isOfHLevel n A → isOfHLevel n (Lift ℓ' A)
isOfHLevelLift n = isOfHLevelRetract n lower lift λ _ → refl

isOfHLevelLower : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} → isOfHLevel n (Lift ℓ' A) → isOfHLevel n A
isOfHLevelLower n = isOfHLevelRetract n lift lower λ _ → refl

----------------------------

-- More consequences of isProp and isContr

inhProp→isContr : A → isProp A → isContr A
inhProp→isContr x h = x , h x

extend : isContr A → (∀ φ → (u : Partial φ A) → Sub A φ u)
extend (x , p) φ u = inS (hcomp (λ { j (φ = i1) → p (u 1=1) j }) x)

isContrPartial→isContr : ∀ {ℓ} {A : Type ℓ}
                       → (extend : ∀ φ → Partial φ A → A)
                       → (∀ u → u ≡ (extend i1 λ { _ → u}))
                       → isContr A
isContrPartial→isContr {A = A} extend law
  = ex , λ y → law ex ∙ (λ i → Aux.v y i) ∙ sym (law y)
    where ex = extend i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial φ A
            u = λ { (i = i0) → ex ; (i = i1) → y }
            v = extend φ u

-- Dependent h-level over a type

isOfHLevelDep : HLevel → {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isOfHLevelDep 0 {A = A} B = {a : A} → Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a ≡ a') → PathP (λ i → B (p i)) b b')
isOfHLevelDep 1 {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 ≡ a1) → PathP (λ i → B (p i)) b0 b1
isOfHLevelDep (suc (suc  n)) {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) → isOfHLevelDep (suc n) {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1)

isContrDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isContrDep = isOfHLevelDep 0

isPropDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isPropDep = isOfHLevelDep 1

isContrDep∘
  : {A' : Type ℓ} (f : A' → A) → isContrDep B → isContrDep (B ∘ f)
isContrDep∘ f cB {a} = λ where
  .fst → cB .fst
  .snd b' p → cB .snd b' (cong f p)

isPropDep∘ : {A' : Type ℓ} (f : A' → A) → isPropDep B → isPropDep (B ∘ f)
isPropDep∘ f pB b0 b1 = pB b0 b1 ∘ cong f

isOfHLevelDep→isOfHLevel : (n : HLevel)
  → {A : Type ℓ} {B : A → Type ℓ'} → isOfHLevelDep n {A = A} B → (a : A) → isOfHLevel n (B a)
isOfHLevelDep→isOfHLevel 0 h a = h .fst , λ b → h .snd b refl
isOfHLevelDep→isOfHLevel 1 h a x y = h x y refl
isOfHLevelDep→isOfHLevel (suc (suc n)) h a x y = isOfHLevelDep→isOfHLevel (suc n) (h x y) refl

isOfHLevel→isOfHLevelDep : (n : HLevel)
  → {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isOfHLevel n (B a)) → isOfHLevelDep n {A = A} B
isOfHLevel→isOfHLevelDep 0 h {a} =
  (h a .fst , λ b' p → isProp→PathP (λ i → isContr→isProp (h (p i))) (h a .fst) b')
isOfHLevel→isOfHLevelDep 1 h = λ b0 b1 p → isProp→PathP (λ i → h (p i)) b0 b1
isOfHLevel→isOfHLevelDep (suc (suc n)) {A = A} {B} h {a0} {a1} b0 b1 =
  isOfHLevel→isOfHLevelDep (suc n) (λ p → helper p)
  where
  helper : (p : a0 ≡ a1) →
    isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1)
  helper p = J (λ a1 p → ∀ b1 → isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1))
                     (λ _ → h _ _ _) p b1

isContrDep→isPropDep : isOfHLevelDep 0 B → isOfHLevelDep 1 B
isContrDep→isPropDep {B = B} Bctr {a0 = a0} b0 b1 p i
  = comp (λ k → B (p (i ∧ k))) (λ k → λ where
        (i = i0) → Bctr .snd b0 refl k
        (i = i1) → Bctr .snd b1 p k)
      (c0 .fst)
  where
  c0 = Bctr {a0}

isPropDep→isSetDep : isOfHLevelDep 1 B → isOfHLevelDep 2 B
isPropDep→isSetDep {B = B} Bprp b0 b1 b2 b3 p i j
  = comp (λ k → B (p (i ∧ k) (j ∧ k))) (λ k → λ where
        (j = i0) → Bprp b0 b0 refl k
        (i = i0) → Bprp b0 (b2 j) (λ k → p i0 (j ∧ k)) k
        (i = i1) → Bprp b0 (b3 j) (λ k → p k (j ∧ k)) k
        (j = i1) → Bprp b0 b1 (λ k → p (i ∧ k) (j ∧ k)) k)
      b0

isOfHLevelDepSuc : (n : HLevel) → isOfHLevelDep n B → isOfHLevelDep (suc n) B
isOfHLevelDepSuc 0 = isContrDep→isPropDep
isOfHLevelDepSuc 1 = isPropDep→isSetDep
isOfHLevelDepSuc (suc (suc n)) Blvl b0 b1 = isOfHLevelDepSuc (suc n) (Blvl b0 b1)

isPropDep→isSetDep'
  : isOfHLevelDep 1 B
  → {p : w ≡ x} {q : y ≡ z} {r : w ≡ y} {s : x ≡ z}
  → {tw : B w} {tx : B x} {ty : B y} {tz : B z}
  → (sq : Square p q r s)
  → (tp : PathP (λ i → B (p i)) tw tx)
  → (tq : PathP (λ i → B (q i)) ty tz)
  → (tr : PathP (λ i → B (r i)) tw ty)
  → (ts : PathP (λ i → B (s i)) tx tz)
  → SquareP (λ i j → B (sq i j)) tp tq tr ts
isPropDep→isSetDep' {B = B} Bprp {p} {q} {r} {s} {tw} sq tp tq tr ts i j
  = comp (λ k → B (sq (i ∧ k) (j ∧ k))) (λ k → λ where
        (i = i0) → Bprp tw (tp j) (λ k → p (k ∧ j)) k
        (i = i1) → Bprp tw (tq j) (λ k → sq (i ∧ k) (j ∧ k)) k
        (j = i0) → Bprp tw (tr i) (λ k → r (k ∧ i)) k
        (j = i1) → Bprp tw (ts i) (λ k → sq (k ∧ i) (j ∧ k)) k)
      tw

isOfHLevelΣ' : ∀ n → isOfHLevel n A → isOfHLevelDep n B → isOfHLevel n (Σ A B)
isOfHLevelΣ' 0 Actr Bctr .fst = (Actr .fst , Bctr .fst)
isOfHLevelΣ' 0 Actr Bctr .snd (x , y) i
  = Actr .snd x i , Bctr .snd y (Actr .snd x) i
isOfHLevelΣ' 1 Alvl Blvl (w , y) (x , z) i .fst = Alvl w x i
isOfHLevelΣ' 1 Alvl Blvl (w , y) (x , z) i .snd = Blvl y z (Alvl w x) i
isOfHLevelΣ' {A = A} {B = B} (suc (suc n)) Alvl Blvl (w , y) (x , z)
  = isOfHLevelRetract (suc n)
      (λ p → (λ i → p i .fst) , λ i → p i .snd)
      ΣPathP
      (λ x → refl)
      (isOfHLevelΣ' (suc n) (Alvl w x) (Blvl y z))

ΣSquareSet : ((x : A) → isSet (B x)) → {u v w x : Σ A B}
          → {p : u ≡ v} {q : v ≡ w} {r : x ≡ w} {s : u ≡ x}
          → Square (cong fst p) (cong fst r)
                    (cong fst s) (cong fst q)
          → Square p r s q
fst (ΣSquareSet pB sq i j) = sq i j
snd (ΣSquareSet {B = B} pB {p = p} {q = q} {r = r} {s = s} sq i j) = lem i j
  where
  lem : SquareP (λ i j → B (sq i j))
          (cong snd p) (cong snd r) (cong snd s) (cong snd q)
  lem = toPathP (isOfHLevelPathP' 1 (pB _) _ _ _ _)

module _ (isSet-A : isSet A) (isSet-A' : isSet A') where


  isSet-SetsIso : isSet (Iso A A')
  isSet-SetsIso x y p₀ p₁ = h
    where

     module X = Iso x
     module Y = Iso y

     f-p : ∀ i₁ → (Iso.fun (p₀ i₁) , Iso.inv (p₀ i₁)) ≡
                  (Iso.fun (p₁ i₁) , Iso.inv (p₁ i₁))
     fst (f-p i₁ i) a  = isSet-A' (X.fun a ) (Y.fun a ) (cong _ p₀) (cong _ p₁) i i₁
     snd (f-p i₁ i) a' = isSet-A  (X.inv a') (Y.inv a') (cong _ p₀) (cong _ p₁) i i₁

     s-p : ∀ b → _
     s-p b =
       isSet→SquareP (λ i j → isProp→isSet (isSet-A' _ _))
         refl refl (λ i₁ → (Iso.sec (p₀ i₁) b)) (λ i₁ → (Iso.sec (p₁ i₁) b))

     r-p : ∀ a → _
     r-p a =
       isSet→SquareP (λ i j → isProp→isSet (isSet-A _ _))
         refl refl (λ i₁ → (Iso.ret (p₀ i₁) a)) (λ i₁ → (Iso.ret (p₁ i₁) a))


     h : p₀ ≡ p₁
     Iso.fun (h i i₁) = fst (f-p i₁ i)
     Iso.inv (h i i₁) = snd (f-p i₁ i)
     Iso.sec (h i i₁) b = s-p b i₁ i
     Iso.ret  (h i i₁) a = r-p a i₁ i


  SetsIso≡-ext : ∀ {a b : Iso A A'}
            → (∀ x → Iso.fun a x ≡ Iso.fun b x)
            → (∀ x → Iso.inv a x ≡ Iso.inv b x)
            → a ≡ b
  Iso.fun (SetsIso≡-ext {a} {b} fun≡ inv≡ i) x = fun≡ x i
  Iso.inv (SetsIso≡-ext {a} {b} fun≡ inv≡ i) x = inv≡ x i
  Iso.sec (SetsIso≡-ext {a} {b} fun≡ inv≡ i) b₁ =
     isSet→SquareP (λ _ _ → isSet-A')
       (Iso.sec a b₁)
       (Iso.sec b b₁)
       (λ i → fun≡ (inv≡ b₁ i) i)
       refl i
  Iso.ret (SetsIso≡-ext {a} {b} fun≡ inv≡ i) a₁ =
     isSet→SquareP (λ _ _ → isSet-A)
       (Iso.ret a a₁)
       (Iso.ret b a₁)
       (λ i → inv≡ (fun≡ a₁ i) i )
       refl i

  SetsIso≡ : ∀ {a b : Iso A A'}
            → (Iso.fun a ≡ Iso.fun b)
            → (Iso.inv a ≡ Iso.inv b)
            → a ≡ b
  SetsIso≡ p q =
    SetsIso≡-ext (funExt⁻ p) (funExt⁻ q)

  isSet→Iso-Iso-≃ : Iso (Iso A A') (A ≃ A')
  isSet→Iso-Iso-≃ = ww
    where
      open Iso

      ww : Iso _ _
      fun ww = isoToEquiv
      inv ww = equivToIso
      sec ww b = equivEq refl
      ret ww a = SetsIso≡ refl refl


  isSet→isEquiv-isoToPath : isEquiv isoToEquiv
  isSet→isEquiv-isoToPath = isoToIsEquiv isSet→Iso-Iso-≃



isSet→Iso-Iso-≡ : (isSet-A : isSet A) → (isSet-A' : isSet A') →  Iso (Iso A A') (A ≡ A')
isSet→Iso-Iso-≡ isSet-A isSet-A' = ww
  where
    open Iso

    ww : Iso _ _
    fun ww = isoToPath
    inv ww = pathToIso
    sec ww b = isInjectiveTransport (funExt λ _ → transportRefl _)
    ret ww a = SetsIso≡-ext isSet-A isSet-A' (λ _ → transportRefl (fun a _)) λ _ → cong (inv a) (transportRefl _)

hSet-Iso-Iso-≡ : (A : hSet ℓ) → (A' : hSet ℓ) → Iso (Iso (fst A) (fst A')) (A ≡ A')
hSet-Iso-Iso-≡ A A' = compIso (isSet→Iso-Iso-≡ (snd A) (snd A')) (equivToIso (_ , isEquiv-Σ≡Prop λ _ → isPropIsSet))

module _ (B : (i j k : I) → Type ℓ)
  {c₀₀₀ : B i0 i0 i0} {c₀₀₁ : B i0 i0 i1} {c₀₁₀ : B i0 i1 i0} {c₀₁₁ : B i0 i1 i1}
  {c₁₀₀ : B i1 i0 i0} {c₁₀₁ : B i1 i0 i1} {c₁₁₀ : B i1 i1 i0} {c₁₁₁ : B i1 i1 i1}
  {c₀₀₋ : PathP (λ k → B i0 i0 k) c₀₀₀ c₀₀₁} {c₀₁₋ : PathP (λ k → B i0 i1 k) c₀₁₀ c₀₁₁}
  {c₀₋₀ : PathP (λ i → B i0 i i0) c₀₀₀ c₀₁₀} {c₀₋₁ : PathP (λ i → B i0 i i1) c₀₀₁ c₀₁₁}
  {c₁₀₋ : PathP (λ k → B i1 i0 k) c₁₀₀ c₁₀₁} {c₁₁₋ : PathP (λ k → B i1 i1 k) c₁₁₀ c₁₁₁}
  {c₁₋₀ : PathP (λ i → B i1 i i0) c₁₀₀ c₁₁₀} {c₁₋₁ : PathP (λ i → B i1 i i1) c₁₀₁ c₁₁₁}
  {c₋₀₀ : PathP (λ i → B i i0 i0) c₀₀₀ c₁₀₀} {c₋₀₁ : PathP (λ i → B i i0 i1) c₀₀₁ c₁₀₁}
  {c₋₁₀ : PathP (λ i → B i i1 i0) c₀₁₀ c₁₁₀} {c₋₁₁ : PathP (λ i → B i i1 i1) c₀₁₁ c₁₁₁}
  (c₀₋₋ : SquareP (λ j k → B i0 j k) c₀₀₋ c₀₁₋ c₀₋₀ c₀₋₁)
  (c₁₋₋ : SquareP (λ j k → B i1 j k) c₁₀₋ c₁₁₋ c₁₋₀ c₁₋₁)
  (c₋₀₋ : SquareP (λ i k → B i i0 k) c₀₀₋ c₁₀₋ c₋₀₀ c₋₀₁)
  (c₋₁₋ : SquareP (λ i k → B i i1 k) c₀₁₋ c₁₁₋ c₋₁₀ c₋₁₁)
  (c₋₋₀ : SquareP (λ i j → B i j i0) c₀₋₀ c₁₋₀ c₋₀₀ c₋₁₀)
  (c₋₋₁ : SquareP (λ i j → B i j i1) c₀₋₁ c₁₋₁ c₋₀₁ c₋₁₁) where

  CubeP : Type ℓ
  CubeP = PathP (λ i → SquareP (λ j k → B i j k)
                      (c₋₀₋ i) (c₋₁₋ i)
                      (c₋₋₀ i) (c₋₋₁ i))
                 c₀₋₋ c₁₋₋

  isGroupoid→CubeP : isGroupoid (B i1 i1 i1) → CubeP
  isGroupoid→CubeP grpd =
    isOfHLevelPathP' 0 (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 grpd _ _) _ _) _ _ .fst


Π-contractDomIso : (c : isContr A) → Iso ((x : A) → B x) (B (c .fst))
Π-contractDomIso {B = B} c .fun f = f (c .fst)
Π-contractDomIso {B = B} c .inv b x = subst B (c .snd x) b
Π-contractDomIso {B = B} c .sec b i = transp (λ j → B (isProp→isSet (isContr→isProp c) _ _ (c .snd (c .fst)) refl i j)) i b
Π-contractDomIso {B = B} c .ret f = funExt λ x → fromPathP (cong f (c .snd x))

Π-contractDom : (c : isContr A) → ((x : A) → B x) ≃ B (c .fst)
Π-contractDom c = isoToEquiv (Π-contractDomIso c)
