{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.BoundaryHIT where

open import Cubical.Data.Empty
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Data.NatMinusOne.Base

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Susp.Properties


open import Cubical.HITs.S1

open import Cubical.HITs.Join


open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Cubes
-- NBoundary and boundaryInj are recursively defined

data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true

NCube : ℕ -> Type₀
NCube = Vec Interval'

NBoundary : ℕ → Type₀

boundaryInj : ∀ {n} → NBoundary n → NCube n

data NBoundary' {n} : Type₀ where
   lid : Bool → NCube (n) → NBoundary'
   cyl : ∀ x → lid false (boundaryInj x) ≡ lid true (boundaryInj x)

NBoundary zero = ⊥
NBoundary (suc n) = NBoundary' {n}

boundaryInj {suc n} (lid x x₁) = end x ∷ x₁
boundaryInj {suc n} (cyl x i) = inside i ∷ boundaryInj x

boundaryEndMap : ∀ {n} → Bool → NBoundary n → NBoundary (suc n)
boundaryEndMap {n} x = lid x ∘ boundaryInj

cyl' : ∀ {n} → (bd : NBoundary (suc n)) →
               boundaryEndMap false bd ≡ boundaryEndMap true bd 
cyl' = cyl

lid' : ∀ {n} → Bool  → NCube n → NBoundary (suc n) 
lid' = lid

cyl'' : ∀ {n} →  Interval' → NBoundary n → NBoundary (suc n)
cyl'' (end false) y = cyl y i0
cyl'' (end true) y = cyl y i1
cyl'' (inside i) y = cyl y i


cylEx : ∀ {n} → boundaryEndMap {n} false ≡ boundaryEndMap true 
cylEx i x = cyl x i

faceInj : ∀ {n}
          → ℕ → Bool
          → NCube n → NBoundary (suc n)  
faceInj {suc n} (suc k) s (end x₂ ∷ x₃) = lid x₂ (boundaryInj (faceInj k s x₃))
faceInj {suc n} (suc k) s (inside i ∷ x₃) = cyl (faceInj k s x₃) i
faceInj  _  = lid

faceMap : ∀ {n}
          → ℕ → Bool
          → NCube n → NCube (suc n)  
faceMap n b = boundaryInj ∘ faceInj n b 

boundaryProj : ∀ {n} → NBoundary (suc n) → NCube n
boundaryProj {zero} _ = []
boundaryProj {suc n} (lid _ x₁) = x₁
boundaryProj {suc n} (cyl x _) = boundaryInj x


boundaryHead : ∀ {n} → NBoundary (suc n) →  Interval'
boundaryHead (lid x x₁) = end x
boundaryHead (cyl x i) = inside i

corner0 : ∀ {n} → NCube n
corner0 {zero} = []
corner0 {suc n} =  end false ∷ corner0

corner1 : ∀ {n} → NCube n
corner1 {zero} = []
corner1 {suc n} =  end true ∷ corner1

corner0Bd : ∀ {n} → NBoundary (suc n)
corner0Bd {zero} = lid false []
corner0Bd {suc n} = lid false corner0

corner1Bd : ∀ {n} → NBoundary (suc n)
corner1Bd {zero} = lid true []
corner1Bd {suc n} = lid true corner1

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


corner0Bd-≡-corner1Bd : ∀ {n} → corner0Bd {n = suc n} ≡ corner1Bd {n = suc n}
corner0Bd-≡-corner1Bd {n} i = ((λ i₁ → cyl (lid false (corner0-≡  corner0 i₁)) i₁)
                             ∙ λ i₁ → lid true (inside i₁ ∷ (corner0-≡-corner1 i₁))) i




NBoundary1-≡-Bool : NBoundary 1 ≡ Bool
NBoundary1-≡-Bool = isoToPath h 
  where

  h : Iso (NBoundary 1) Bool
  Iso.fun h (lid x _) = x
  Iso.inv h x = lid x []
  Iso.rightInv h b = refl
  Iso.leftInv h (lid x []) = refl


-- this version of Bool≃Susp⊥' is consistent with convention in Interval'

Bool≃Susp⊥' : Bool ≃ Susp ⊥
Bool≃Susp⊥' =
  isoToEquiv
    (iso
      (λ {false  → north; true → south})
      (λ {north → false;  south → true})
      (λ {north → refl;  south → refl})
      (λ {true  → refl;  false → refl}))



--Equality of NBoundary and S

NBoundary-≡-S : ∀ {n} → NBoundary n ≡ S (-1+ n)
NBoundary-≡-S {zero} = refl
NBoundary-≡-S {suc zero} = NBoundary1-≡-Bool ∙  ua Bool≃Susp⊥'
NBoundary-≡-S {suc (suc n)} = (isoToPath (lem) ) ∙ cong Susp (NBoundary-≡-S) 
  where

  lem : Iso NBoundary' (Susp NBoundary')
  Iso.fun (lem) (lid false x₁) = north
  Iso.fun (lem) (lid true x₁) = south
  Iso.fun (lem) (cyl x i) = merid x i
  Iso.inv (lem) north = lid false (corner0)
  Iso.inv (lem) south = lid true (corner1)
  Iso.inv (lem) (merid x i) =   ((cong (lid false) (corner0-≡ (boundaryInj x)))
                              ∙∙ (cyl x)
                              ∙∙ (cong (lid true) (≡-corner1 (boundaryInj x)))) i

  Iso.rightInv (lem) north = refl
  Iso.rightInv (lem) south = refl
  Iso.rightInv (lem) (merid x i₁) i =
          
         doubleCompPath-filler
        (λ _ → north)
        (λ j → doubleCompPath-filler
                (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∨ i) x) (i₂ ∧ j))
                (λ i₂ → merid (transp ((λ _ → NBoundary (suc n))) i x)  j )
                (λ i₂ → merid (transp (λ _ → NBoundary (suc n)) ((~ i₂) ∧ i) x) (i₂ ∨  j))
                (~ i) j )
        (λ _ → south)
        (~ i) i₁

  Iso.leftInv (lem) (lid false x₁) = cong (lid false) (corner0-≡ _)
  Iso.leftInv (lem) (lid true x₁) = sym (cong (lid true) (≡-corner1 _))
  Iso.leftInv (lem) (cyl x i₁) i =
      doubleCompPath-filler
        (cong (lid false) (corner0-≡ (boundaryInj x)))
        (cyl x)
        (cong (lid true) (≡-corner1 (boundaryInj x)))
        (~ i) i₁

IsoS₊ : ∀ n → Iso (S₊ n) (NBoundary (suc n))
IsoS₊ n = compIso (invIso (IsoS₊S n)) ((pathToIso (sym NBoundary-≡-S)))

private
  variable
   ℓ : Level
   A : Type ℓ

evalCube : ∀ n → Cube n A → NCube n → A

evalCube zero x x₁ = x
evalCube (suc zero) x (end false ∷ x₂) = x .fst .fst
evalCube (suc (suc n)) x (end false ∷ x₂) =
 evalCube (suc n) (x .fst .snd .snd i0 , snd x i0) x₂
evalCube (suc zero) x (end true ∷ x₂) = x .fst .snd
evalCube (suc (suc n)) x (end true ∷ x₂) =
 evalCube (suc n) (x .fst .snd .fst .fst , x .fst .snd .fst .snd) x₂
evalCube (suc zero) x (inside i ∷ x₂) = snd x i
evalCube (suc (suc n)) x (inside i ∷ x₂) =
 evalCube (suc n) (_ , (snd x i)) x₂


InsideOf : ∀ {ℓ}  → ∀ {n} → ∀ {A : Type ℓ}
                  → (bd : NBoundary n → A)
                  → Type ℓ

insideOf : ∀ {ℓ} → ∀ {n} → ∀ {A : Type ℓ}                  
                  → (bc : NCube n → A)                  
                  → InsideOf (bc ∘ boundaryInj)

InsideOf {n = zero} {A = A} bd = A
InsideOf {n = suc n} bd =
                       PathP
                       (λ i → InsideOf (bd ∘ cyl'' (inside i)))
                       (insideOf (bd ∘ lid false))
                       (insideOf (bd ∘ lid true))

insideOf {n = zero} bc = bc [] 
insideOf {n = suc n} bc i = insideOf (λ x₁ → bc (inside i ∷ x₁))


toCubical :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → ∀ {bd}
             → (InsideOf {n = n} {A = A} bd )
             → NCube n → A 
toCubical {n = zero} {bd} x x₁ = x
toCubical {n = suc n} {bd} x (end false ∷ x₂) = toCubical (x i0) x₂
toCubical {n = suc n} {bd} x (end true ∷ x₂) = toCubical (x i1) x₂
toCubical {n = suc n} {bd} x (inside i ∷ x₂) = toCubical (x i) x₂


toCubical∘insideOf : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
  (f : NCube n → A) → ∀ x → toCubical (insideOf f) x ≡ f x

toCubical∘insideOf {n = zero} f [] = refl
toCubical∘insideOf {n = suc n} f (end false ∷ x₁) =
  toCubical∘insideOf {n = n} (f ∘ (end false ∷_)) x₁
toCubical∘insideOf {n = suc n} f (end true ∷ x₁) =
 toCubical∘insideOf {n = n} (f ∘ (end true ∷_)) x₁
toCubical∘insideOf {n = suc n} f (inside i ∷ x₁) =
 toCubical∘insideOf {n = n} (f ∘ (inside i ∷_)) x₁


NBoundary-rec :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ}
                 → (x0 x1 : NCube n → A)
                 → x0 ∘ boundaryInj ≡ x1 ∘ boundaryInj 
                 → NBoundary (suc n) → A 
NBoundary-rec x0 x1 x (lid false x₂) = x0 x₂
NBoundary-rec x0 x1 x (lid true x₂) = x1 x₂
NBoundary-rec x0 x1 x (cyl x₁ i) = x i x₁

NBoundary-elim :  ∀ {ℓ} → ∀ {n} → {A : NBoundary (suc n) → Type ℓ}
                 → (f : (b : Bool) → (c : NCube n) → A (lid b c))
                 → PathP (λ i → (bd : NBoundary n) → A (cyl bd i))
                       (f false ∘ boundaryInj)
                       (f true ∘ boundaryInj) 
                 → (bd : NBoundary (suc n)) → A bd 
NBoundary-elim f x (lid x₁ x₂) = f x₁ x₂
NBoundary-elim f x (cyl x₁ i) = x i x₁


NBoundary-app-Interval :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                     (NBoundary (suc n) → A)
                   → (Σ (Interval' → (NBoundary n → A)) λ a → InsideOf (a (end false)) × InsideOf (a (end true))  )
NBoundary-app-Interval {n = zero} x =  (λ x₁ ()) , (x (lid false [])) , (x (lid true []))
NBoundary-app-Interval {n = suc n} x = (λ i →  x ∘ cyl'' i ) , (insideOf (x ∘ lid false )) , insideOf (x ∘ lid true )

NBoundary-rec-inv :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                     (NBoundary (suc n) → A)
                   → (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
NBoundary-rec-inv {n = zero} x = ((λ _ → (x (lid false []))) , (λ _ → (x (lid true [])))) , (funExt λ () )
NBoundary-rec-inv {n = suc n} x = ((x ∘ lid false) , (x ∘ lid true)) , funExt λ x₁ → (λ i → x (cyl x₁ i))



NBoundary-rec-Iso :  ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
                    Iso (NBoundary (suc n) → A)
                        (Σ ((NCube n → A) × (NCube n → A)) λ x0x1 → (fst x0x1) ∘ boundaryInj ≡ (snd x0x1) ∘ boundaryInj   )
Iso.fun NBoundary-rec-Iso = NBoundary-rec-inv
Iso.inv NBoundary-rec-Iso ((x0 , x1) , p) = NBoundary-rec x0 x1 p
fst (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = fst₁ []
snd (fst (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i)) [] = snd₂ []
snd (Iso.rightInv (NBoundary-rec-Iso {n = zero}) ((fst₁ , snd₂) , snd₁) i) i₁ ()


Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid false []) =  a (lid false [])
Iso.leftInv (NBoundary-rec-Iso {n = zero}) a i (lid true []) =  a (lid true [])

Iso.rightInv (NBoundary-rec-Iso {n = suc n}) b = refl

Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid false x₁) = a (lid false x₁)
Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (lid true x₁) = a (lid true x₁)
Iso.leftInv (NBoundary-rec-Iso {n = suc n}) a i (cyl x i₁) = a (cyl x i₁)


NBoundary-rec-Iso-Σ : ∀ {ℓ} → ∀ n → (A : Type ℓ) →
     Iso
      (Σ ((NCube n → A) × (NCube n → A))
       λ (x0 , x1) → Path (Σ (NBoundary n → A) InsideOf)
         (x0 ∘ boundaryInj , insideOf x0)
         (x1 ∘ boundaryInj , insideOf x1))
       (Σ (NBoundary (suc n) → A) InsideOf)
NBoundary-rec-Iso-Σ n A =
   compIso (compIso (Σ-cong-iso-snd w) (invIso Σ-assoc-Iso ))
    (Σ-cong-iso-fst {B = InsideOf {n = (suc n)} {A = A}}
              (invIso (NBoundary-rec-Iso {n = n} {A}))) 

 where
  w : (x : (NCube n → A) × (NCube n → A)) →
      Iso (Path (Σ (NBoundary n → A) InsideOf)
        (_ , insideOf (fst x)) (_ , insideOf (snd x)))
      (Σ-syntax (fst x ∘ boundaryInj ≡ snd x ∘ boundaryInj)
       (λ z → (InsideOf ∘ Iso.fun (invIso NBoundary-rec-Iso)) (x , z)))
  w (x0 , x1) .Iso.fun p = _ , λ i → snd (p i)
  w (x0 , x1) .Iso.inv (_ , p) i = _ , p i
  w (x0 , x1) .Iso.rightInv _ = refl
  w (x0 , x1) .Iso.leftInv _ = refl



reflⁿ : ∀ {ℓ} → {A : Type ℓ} → ∀ n → (a : A) → InsideOf {n = n} (λ _ → a)
reflⁿ zero a = a
reflⁿ (suc n) a = refl

Iso≡bdInj : ∀ (A : Type ℓ) n →
 Iso
   (Σ (NBoundary n → A)
    λ bd → Σ (NCube n → A) λ c → ∀ b → bd b ≡ c (boundaryInj b))
   (NCube n → A)
Iso≡bdInj A n .Iso.fun = fst ∘ snd
Iso≡bdInj A n .Iso.inv x = _ , x , λ _ → refl
Iso≡bdInj A n .Iso.rightInv _ = refl
Iso≡bdInj A n .Iso.leftInv a i .fst z = snd (snd a) z (~ i)
Iso≡bdInj A n .Iso.leftInv a i .snd .fst = a .snd .fst
Iso≡bdInj A n .Iso.leftInv a i .snd .snd z j = a .snd .snd z (j ∨ ~ i)





-- PathIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
--   Iso A B → Iso (Σ (A × A) λ (x , y) → x ≡ y) (Σ (B × B) λ (x , y) → x ≡ y) 
-- PathIso isom = w
--  where
--  open Iso isom
--  w : Iso _ _
--  w .Iso.fun (_ , p) = _ , cong fun p
--  w .Iso.inv (_ , p) = _ , cong inv p
--  w .Iso.rightInv (_ , p) j = _ , λ i → rightInv (p i) j 
--  w .Iso.leftInv (_ , p) j = _ , λ i → leftInv (p i) j


ΣPathIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
  Iso A B → Iso (Σ (A × A) λ (x , y) → x ≡ y) (Σ (B × B) λ (x , y) → x ≡ y) 
ΣPathIso isom = w
 where
 open Iso isom
 w : Iso _ _
 w .Iso.fun (_ , p) = _ , cong fun p
 w .Iso.inv (_ , p) = _ , cong inv p
 w .Iso.rightInv (_ , p) j = _ , λ i → rightInv (p i) j 
 w .Iso.leftInv (_ , p) j = _ , λ i → leftInv (p i) j

-- NCubeEnsdIso : ∀ n → (A : Type ℓ)
--   → Iso (NCube (suc n) → A)
--     (Σ ((NCube n → A) × (NCube n → A))
--      (λ (x0 , x1) →
--         Path (Σ (NBoundary n → A) InsideOf)
--         (x0 ∘ boundaryInj , insideOf x0)
--         (x1 ∘ boundaryInj , insideOf x1)))
-- NCubeEnsdIso n A = w
--  where
--  w : Iso _ _ 
--  w .Iso.fun p = _ , λ i → _ , insideOf p i
--  w .Iso.inv (_ , p) (end false ∷ x₁) = toCubical (snd (p i0)) x₁
--  w .Iso.inv (_ , p) (end true ∷ x₁) = toCubical (snd (p i1)) x₁
--  w .Iso.inv (_ , p) (inside i ∷ x₁) = toCubical (snd (p i)) x₁ 
--  w .Iso.rightInv b i .fst .fst z = toCubical∘insideOf (b .fst .fst) z i 
--  w .Iso.rightInv b i .fst .snd z = toCubical∘insideOf (b .fst .snd) z i
--  w .Iso.rightInv b i .snd x .fst z = {!!}
--  w .Iso.rightInv b i .snd x .snd = {!!}
--  w .Iso.leftInv a i (end false ∷ x₁) =
--   toCubical∘insideOf (λ x → a (end false ∷ x)) x₁ i
--  w .Iso.leftInv a i (end true ∷ x₁) =
--   toCubical∘insideOf (λ x → a (end true ∷ x)) x₁ i
--  w .Iso.leftInv a i (inside i₁ ∷ x₁) =
--    toCubical∘insideOf (λ x → a (inside i₁ ∷ x)) x₁ i

NCubeEndsIso : ∀ n → (A : Type ℓ)
  → Iso (NCube (suc n) → A)
    (Σ ((NCube n → A) × (NCube n → A))
     (λ (x0 , x1) → x0 ≡ x1))
NCubeEndsIso n A = w
 where
  w : Iso (NCube (suc n) → A)
       _
  w .Iso.fun x = _ , λ i xs → x (inside i ∷ xs) 
  w .Iso.inv (q , x) (end false ∷ xs) = q .fst xs
  w .Iso.inv (q , x) (end true ∷ xs) = q .snd xs
  w .Iso.inv (_ , x) (inside i ∷ xs) = x i xs
  w .Iso.rightInv _ = refl
  w .Iso.leftInv a i (end false ∷ x₁) = a (end false ∷ x₁)
  w .Iso.leftInv a i (end true ∷ x₁) = a (end true ∷ x₁)
  w .Iso.leftInv a i (inside i₁ ∷ x₁) = a (inside i₁ ∷ x₁)



-- ΣInsideOf-Iso : ∀ n → (A : Type ℓ)
--   → Iso
--     (NCube (suc n) → A)
--     (Σ (NBoundary (suc n) → A) InsideOf)
-- ΣInsideOf-Iso n A = compIso
--  (compIso (NCubeEndsIso n A)
--    (Σ-cong-iso-snd λ (x0 , x1) →
--     {!!}))
--   (NBoundary-rec-Iso-Σ n A) 

-- ΣInsideOf-Iso zero A = w
--  where
--  w : Iso (NCube zero → A) (Σ (NBoundary zero → A) InsideOf)
--  w .Iso.fun x = (λ ()) , x []
--  w .Iso.inv (_ , x) _ = x
--  w .Iso.rightInv _ i .fst ()
--  w .Iso.rightInv b i .snd = b .snd
--  w .Iso.leftInv z i [] = z []
-- ΣInsideOf-Iso (suc n) A =
--  compIso
--    (compIso {!!}
--      (Σ-cong-iso-snd λ _ → invIso (congIso (invIso (ΣInsideOf-Iso n A)))))
--   (NBoundary-rec-Iso-Σ  n A)
--  where
--  w : Iso _ _
--  w .Iso.fun p = ((λ xx → p (end false ∷ xx)) , (λ xx → p (end true ∷ xx)))
--    , λ i xx → Iso.inv (ΣInsideOf-Iso n A)
--          ((λ x → p (inside i ∷ boundaryInj x)) ,
--           insideOf (λ xx₁ → p (inside i ∷ xx₁)))
--          xx 
--  w .Iso.inv (_ , p) (end false ∷ x₁) = p i0 x₁
--  w .Iso.inv (_ , p) (end true ∷ x₁) = p i1 x₁
--  w .Iso.inv (_ , p) (inside i ∷ x₁) = p i x₁
--  w .Iso.rightInv p = {!!}
--  w .Iso.leftInv p = {!!}
-- -- -- toCubical∘boundaryInj : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} →
-- -- --   ∀ bd (f : InsideOf {n = n} {A = A} bd)
-- -- --    → ∀ x → toCubical f (boundaryInj x) ≡ bd x
-- -- -- toCubical∘boundaryInj {n = suc zero} bd f (lid false []) = refl
-- -- -- toCubical∘boundaryInj {n = suc zero} bd f (lid true []) = refl
-- -- -- toCubical∘boundaryInj {n = suc (suc n)} bd f b =
-- -- --  {!!}

-- -- -- -- (λ j → toCubical  (λ i → f (i ∨ j)) (boundaryInj b))

-- -- --  -- where
-- -- --  -- w : {!!}
-- -- --  -- w = toCubical∘boundaryInj {n = suc n} (bd ∘ λ xx → cyl xx i₁ )
-- -- --  --   λ i → {! !}

-- -- -- -- eval∂Cube : ∀ n → ∂Cube n A → NBoundary n → A
-- -- -- -- eval∂Cube zero x ()
-- -- -- -- eval∂Cube (suc zero) x (lid false x₂) = fst x
-- -- -- -- eval∂Cube (suc zero) x (lid true x₂) = snd x
-- -- -- -- eval∂Cube (suc (suc zero)) (l0 , l1 , p) (lid false x₁) = {!!}
 
-- -- -- -- eval∂Cube (suc (suc (suc n))) (l0 , l1 , p) (lid false x₁) = {!!}
-- -- -- -- -- evalCube (suc n) l0 x₁
-- -- -- --  -- {!!} -- evalCube (suc n) l0 x₁
-- -- -- -- eval∂Cube (suc (suc zero)) (l0 , l1 , p) (lid true x₁) = {!!}
-- -- -- -- eval∂Cube (suc (suc (suc n))) (l0 , l1 , p) (lid true x₁) = {!!}
-- -- -- -- -- evalCube (suc n) l1 x₁
-- -- -- --  -- {!evalCube (suc n) l1 x₁!} --
-- -- -- -- eval∂Cube (suc (suc zero)) (l0 , l1 , p) (cyl x i) =
-- -- -- --   eval∂Cube (suc zero) (p i) x
-- -- -- -- eval∂Cube (suc (suc (suc n))) (l0 , l1 , p) (cyl x i) = {!!}
-- -- -- --  -- eval∂Cube (suc n) (p i) x
-- -- -- --  -- eval∂Cube (suc n) (p i) x --

-- uuuzzz : ∀ (A : Type ℓ) (a : A) n p → (b : NBoundary n) →
--            toCubical {bd = λ _ → a}
--                p (boundaryInj b) ≡ a
-- uuuzzz A a (suc n) p (lid false x₁) = 
--  toCubical∘insideOf {n = suc n} (λ _ → a) (end false ∷ x₁)
-- uuuzzz A a (suc n) p (lid true x₁) = 
--  toCubical∘insideOf {n = suc n} (λ _ → a) (end false ∷ x₁)
-- uuuzzz A a (suc (suc n)) p (cyl x i) j =
--   hcomp
--     (λ k → λ {
--       (i = i0) → {!!}
--      ;(i = i1) → {!!}
--      ;(j = i0) → {!toCubical∘insideOf {n = suc n} (λ _ → a) (boundaryInj x) (~ k)!}
--      ;(j = i1) → {!!}
--      })
--     {!!}

-- reflⁿIso : ∀ (A : Type ℓ) n (a : A) →
--  Iso (Σ (NCube n → A) λ c → ∀ b → c (boundaryInj b) ≡ a)
--      (InsideOf {n = n} λ _ → a)
-- reflⁿIso A n a .Iso.fun (c , p) = subst InsideOf (funExt p) (insideOf c)
-- reflⁿIso A n a .Iso.inv p = toCubical p , uuuzzz A a n p
-- reflⁿIso A n a .Iso.rightInv = {!!}
-- reflⁿIso A n a .Iso.leftInv = {!!}

from-surfⁿ : ∀ (A : Type ℓ) n →
   (Σ A λ a → Σ (NCube n → A) λ c → ∀ b → c (boundaryInj b) ≡ a )
 → (NBoundary (suc n) → A) 
from-surfⁿ A n (a , c , p) (lid false x₁) = c x₁
from-surfⁿ A n (a , c , p) (lid true x₁) = a
from-surfⁿ A n (a , c , p) (cyl x i) = p x i

to-surfⁿ : ∀ (A : Type ℓ) n 
 → (NBoundary (suc n) → A)
 → (Σ A λ a → Σ (NCube n → A) λ c → ∀ b → c (boundaryInj b) ≡ a )
 
to-surfⁿ A n b .fst = b (lid true corner0 )
to-surfⁿ A n b .snd .fst c = b (lid false c)
to-surfⁿ A (suc n) b .snd .snd (lid false x₁) i =
  b (cyl (lid false (corner0-≡ x₁ (~ i))) i)
to-surfⁿ A (suc n) b .snd .snd (lid true x₁) =
  (λ i → b (lid false (inside (~ i) ∷ x₁)))
   ∙' (λ i → b (cyl (lid false (corner0-≡ x₁ (~ i))) i))

to-surfⁿ A (suc n) b .snd .snd (cyl x i) i₁ =
  compPath'-filler (λ i → b (lid false (inside (~ i) ∷ boundaryInj x)))
   (λ i → b (cyl (lid false (corner0-≡ (boundaryInj x) (~ i))) i)) i i₁


from-surfⁿ-refl : ∀ (A : Type ℓ) n → (a : A) →
     ∀ b → from-surfⁿ A n (a , (λ _ → a) , (λ _ → refl)) b ≡ a
from-surfⁿ-refl A n a (lid false x₁) = refl
from-surfⁿ-refl A n a (lid true x₁) = refl
from-surfⁿ-refl A n a (cyl x i) _ = a

-- surfⁿIso-sec : ∀ (A : Type ℓ) n → section (to-surfⁿ A n) (from-surfⁿ A n)
-- surfⁿIso-sec A zero b i .fst = b .fst
-- surfⁿIso-sec A zero b i .snd .fst z = b .snd .fst z
-- surfⁿIso-sec A zero b i .snd .snd () j
-- surfⁿIso-sec A (suc n) b i .fst = b .fst
-- surfⁿIso-sec A (suc n) b i .snd .fst z = b .snd .fst z
-- surfⁿIso-sec A (suc n) b i .snd .snd (lid false x₁) j =
--  b .snd .snd (lid false (corner0-≡ x₁ (~ j ∨  i))) j
-- surfⁿIso-sec A (suc n) b i .snd .snd (lid true x₁) j =
--  {!!}
-- surfⁿIso-sec A (suc n) b i .snd .snd (cyl x i₁) j = {!!}

-- surfⁿIso-ret : ∀ (A : Type ℓ) n  b bd →
--   from-surfⁿ A n (to-surfⁿ A n b) bd ≡ b bd
-- surfⁿIso-ret A zero b (lid false []) = refl
-- surfⁿIso-ret A zero b (lid true []) = refl
-- surfⁿIso-ret A (suc n) b (lid false x₁) = refl
-- surfⁿIso-ret A (suc n) b (lid true x) = 
--   cong (b ∘ lid true) (corner0-≡ x)
-- surfⁿIso-ret A (suc n) b (cyl (lid false x₁) i) j =
--  b (cyl (lid false (corner0-≡ x₁ (~ i ∨ j))) i)
-- surfⁿIso-ret A (suc n) b (cyl (lid true x₁) i) j =
--  {!!}
-- surfⁿIso-ret A (suc n) b (cyl (cyl x i₁) i) j = {!!}

-- surfⁿIso : ∀ (A : Type ℓ) n →
--   Iso (NBoundary (suc n) → A)
--       (Σ A λ a → Σ (NCube n → A) λ c → ∀ b → c (boundaryInj b) ≡ a)

-- surfⁿIso A n .Iso.fun = to-surfⁿ A n
-- surfⁿIso A n .Iso.inv = from-surfⁿ A n
-- surfⁿIso A n .Iso.rightInv = surfⁿIso-sec A n
-- surfⁿIso A n .Iso.leftInv = funExt ∘ surfⁿIso-ret A n
