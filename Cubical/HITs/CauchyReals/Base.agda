{-# OPTIONS --safe #-}
module Cubical.HITs.CauchyReals.Base where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int as ℤ
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Data.NatPlusOne

private
  variable
    ℓ ℓ' : Level

-- HoTT Definition 11.3.2.

data ℝ : Type

data _∼[_]_  : ℝ → ℚ₊ → ℝ → Type

data ℝ where
 rat : ℚ → ℝ
 -- HoTT (11.3.3)
 lim : (x : ℚ₊ → ℝ) →
       (∀ ( δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε) →  ℝ
 -- HoTT (11.3.4)
 eqℝ : ∀ x y → (∀ ε → x ∼[ ε ] y) → x ≡ y

data _∼[_]_   where
 rat-rat : ∀ q r ε
   → (ℚ.- fst ε) ℚ.< (q ℚ.- r)
   → (q ℚ.- r) ℚ.< fst ε → (rat q) ∼[ ε ] (rat r)
 rat-lim : ∀ q y ε δ p v →
        (rat q) ∼[ fst ε ℚ.- fst δ , v ] ( y δ )
        → (rat q) ∼[ ε ] (lim y p )
 lim-rat : ∀ x r ε δ p v →
        (x δ) ∼[ fst ε ℚ.- fst δ , v ] ( rat r )
        → (lim x p) ∼[ ε ] (rat r )
 lim-lim : ∀ x y ε δ η p p' v →
        (x δ) ∼[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , v ] (y η )
        → (lim x p) ∼[ ε ] (lim y p' )
 isProp∼ : ∀ r q r' → isProp (r ∼[ q ] r')

rat-rat-fromAbs : ∀ q r ε
   → ℚ.abs (q ℚ.- r) ℚ.< fst ε → (rat q) ∼[ ε ] (rat r)
rat-rat-fromAbs q r ε x =
  rat-rat _ _ _
      (isTrans<≤ (ℚ.- fst ε) (ℚ.- ℚ.abs (q ℚ.- r)) (q ℚ.- r)
         (minus-< (ℚ.abs (q ℚ.- r)) (fst ε)  x)
           (isTrans≤ (ℚ.- ℚ.abs (q ℚ.- r))
             (ℚ.- (ℚ.- (q ℚ.- r))) (q ℚ.- r)
             (minus-≤ (ℚ.- (q ℚ.- r)) (ℚ.abs (q ℚ.- r))
               (isTrans≤ (ℚ.- (q ℚ.- r)) _ (ℚ.abs (q ℚ.- r))
                  (ℚ.≤max (ℚ.- (q ℚ.- r)) (q ℚ.- r))
                    (≡Weaken≤ (ℚ.max (ℚ.- (q ℚ.- r)) (q ℚ.- r))
                     _
                       (ℚ.maxComm (ℚ.- (q ℚ.- r)) (q ℚ.- r) ))))
              (≡Weaken≤ (ℚ.- (ℚ.- (q ℚ.- r))) (((q ℚ.- r)))
                 (ℚ.-Invol (q ℚ.- r)))))
    ( isTrans≤< (q ℚ.- r) (ℚ.abs (q ℚ.- r)) (fst ε)
      (ℚ.≤max (q ℚ.- r) (ℚ.- (q ℚ.- r)) ) x)


_∼[_]ₚ_ : ℝ → ℚ₊ → ℝ → hProp ℓ-zero
x ∼[ ε ]ₚ y = x ∼[ ε ] y , isProp∼ _ _ _


instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }

instance
  fromNegℝ : HasFromNeg ℝ
  fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → rat [ neg n / 1 ] }


record Elimℝ {ℓ} {ℓ'} (A : ℝ → Type ℓ)
               (B : ∀ {x y : ℝ} →
                  A x → A y →
                ∀ ε → x ∼[ ε ] y → Type ℓ') : Type (ℓ-max ℓ ℓ') where
 field
  ratA : ∀ x → A (rat x)
  -- HoTT (11.3.5)
  limA : ∀ x p → (a : ∀ q → A (x q)) →
             (∀ δ ε → B {x δ} {x ε} (a δ) (a ε) (δ ℚ₊+ ε) (p δ ε) ) → A (lim x p)
  eqA : ∀ {x y} p a a' → (∀ δ ε → B a a' _ (p (δ ℚ₊+ ε)))
   → (∀ ε → B a a' ε (p ε))
   → PathP (λ i → A (eqℝ x y p i)) a a'

  rat-rat-B : ∀ q r ε x x₁ → B (ratA q) (ratA r) ε (rat-rat q r ε x x₁)
  rat-lim-B : ∀ q y ε δ p v r v' u' →
       B (ratA q) (v' δ) ((fst ε ℚ.- fst δ) , v) r →
       B (ratA q) (limA y p v' u') ε (rat-lim q y ε δ p v r)
  lim-rat-B : ∀ x r ε δ p v u v' u'
    → B (v' δ) (ratA r) ((fst ε ℚ.- fst δ) , v) u
    → B (limA x p v' u') (ratA r) ε (lim-rat x r ε δ p v u)
  lim-lim-B : ∀ x y ε δ η p p' v r v' u' v'' u''
     → B (v' δ) (v'' η) ((fst ε ℚ.- (fst δ ℚ.+ fst η)) , v) r
     → B (limA x p v' u') (limA y p' v'' u'')
     ε (lim-lim x y ε δ η p p' v r)

  isPropB : ∀ {x y} a a' ε u → isProp (B {x} {y} a a' ε u)

 go : ∀ x → A x

 go∼ : ∀ {x x' ε} → (r : x ∼[ ε ] x') →
         B (go x) (go x') ε r

 go (rat x) = ratA x
 go (lim x x₁) = limA x x₁ (λ q → go (x q))
   λ _ _ → go∼ _
 go (eqℝ x x₁ x₂ i) =
   eqA x₂ (go x) (go x₁) (λ _ _ → go∼  _)
      (λ ε → go∼ (x₂ ε)) i


 go∼ (rat-rat q r ε x x₁) = rat-rat-B q r ε x x₁
 go∼ (rat-lim q y ε δ p v r) =
  rat-lim-B q y ε δ p v r (λ q → go (y q))
       (λ _ _ → go∼ (p _ _)) (go∼ {rat q} {y δ} r )
 go∼ (lim-rat x r ε δ p v u) =
  lim-rat-B x r ε δ p v u (λ q → go (x q))
       (λ _ _ → go∼ (p _ _)) (go∼ {x δ} {rat r} u )
 go∼ (lim-lim x y ε δ η p p' v r) =
   lim-lim-B x y ε δ η p p' v r
    (λ q → go (x q))
       (λ _ _ → go∼ (p _ _))
       (λ q → go (y q))
       (λ _ _ → go∼ (p' _ _)) (go∼ {x δ} {y η} r)
 go∼ (isProp∼ r ε r' r₁ r₂ i) =
  isProp→PathP (λ i → isPropB (go r) (go r') ε ((isProp∼ r ε r' r₁ r₂ i)))
     (go∼ r₁) (go∼ r₂) i

 -- HoTT (11.3.6)
 β-go-rat : ∀ q → go (rat q) ≡ ratA q
 β-go-rat _ = refl

 -- HoTT (11.3.7)
 β-go-lim : ∀ x y → go (lim x y) ≡ limA x y _ _
 β-go-lim _ _ = refl

record Elimℝ-Prop {ℓ} (A : ℝ → Type ℓ) : Type ℓ where
 field
  ratA : ∀ x → A (rat x)
  limA : ∀ x p → (∀ q → A (x q)) → A (lim x p)
  isPropA : ∀ x → isProp (A x)


 go : ∀ x → A x
 go (rat x) = ratA x
 go (lim x x₁) = limA x x₁ λ q → go (x q)
 go (eqℝ x x₁ x₂ i) =
  isProp→PathP (λ i → isPropA (eqℝ x x₁ x₂ i))  (go x) (go x₁) i

record Elimℝ-Prop2 {ℓ} (A : ℝ → ℝ → Type ℓ) : Type ℓ where
 field
  rat-ratA : ∀ r q → A (rat r) (rat q)
  rat-limA : ∀ r x y → (∀ q → A (rat r) (x q)) → A (rat r) (lim x y)
  lim-ratA : ∀ x y r → (∀ q → A (x q) (rat r)) → A (lim x y) (rat r)
  lim-limA : ∀ x y x' y' → (∀ q q' → A (x q) (x' q')) → A (lim x y) (lim x' y')
  isPropA : ∀ x y → isProp (A x y)




 go : ∀ x y → A x y
 go = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop (λ z → (y : ℝ) → A z y)
  w .Elimℝ-Prop.ratA x = Elimℝ-Prop.go w'
   where
   w' : Elimℝ-Prop _
   w' .Elimℝ-Prop.ratA = rat-ratA x
   w' .Elimℝ-Prop.limA = rat-limA x
   w' .Elimℝ-Prop.isPropA _ = isPropA _ _
  w .Elimℝ-Prop.limA x p x₁ = Elimℝ-Prop.go w'
   where
   w' : Elimℝ-Prop _
   w' .Elimℝ-Prop.ratA x' = lim-ratA x p x' (flip x₁ (rat x'))
   w' .Elimℝ-Prop.limA x' p' _ = lim-limA x p x' p' λ q q' → x₁ q (x' q')
   w' .Elimℝ-Prop.isPropA _ = isPropA _ _
  w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isPropA _ _




record Elimℝ-Prop2Sym {ℓ} (A : ℝ → ℝ → Type ℓ) : Type ℓ where
 field
  rat-ratA : ∀ r q → A (rat r) (rat q)
  rat-limA : ∀ r x y → (∀ q → A (rat r) (x q)) → A (rat r) (lim x y)
  lim-limA : ∀ x y x' y' → (∀ q q' → A (x q) (x' q')) → A (lim x y) (lim x' y')
  isSymA : ∀ x y → A x y → A y x
  isPropA : ∀ x y → isProp (A x y)


 go : ∀ x y → A x y
 go = Elimℝ-Prop2.go w
  where
  w : Elimℝ-Prop2 (λ z z₁ → A z z₁)
  w .Elimℝ-Prop2.rat-ratA = rat-ratA
  w .Elimℝ-Prop2.rat-limA = rat-limA
  w .Elimℝ-Prop2.lim-ratA x y r x₁ =
   isSymA _ _ (rat-limA r x y (isSymA _ _ ∘ x₁))
  w .Elimℝ-Prop2.lim-limA = lim-limA
  w .Elimℝ-Prop2.isPropA = isPropA

-- HoTT (11.3.13)
record Recℝ {ℓ} {ℓ'} (A : Type ℓ)
               (B : A → A → ℚ₊ → Type ℓ') : Type (ℓ-max ℓ ℓ') where
 field
  ratA : ℚ → A
  limA : (a : ℚ₊ → A) →
             (∀ δ ε → B (a δ) (a ε) (δ ℚ₊+ ε)) → A
  eqA : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

  rat-rat-B : ∀ q r ε
       → (ℚ.- fst ε) ℚ.< (q ℚ.- r)
       → (q ℚ.- r) ℚ.< fst ε
       → B (ratA q) (ratA r) ε
  rat-lim-B : ∀ q y ε p δ v →
       (B (ratA q) (y δ) ((fst ε ℚ.- fst δ) , v)) →
       B (ratA q) (limA y p) ε
  lim-rat-B : ∀ x r ε δ p v
    → B (x δ) (ratA r) ((fst ε ℚ.- fst δ) , v)
    → B (limA x p) (ratA r) ε
  lim-lim-B : ∀ x y ε δ η p p' v
     → B (x δ) (y η) (((fst ε ℚ.- (fst δ ℚ.+ fst η)) , v))
     → B (limA x p) (limA y p') ε

  isPropB : ∀ a a' ε → isProp (B a a' ε)

 d : Elimℝ (λ _ → A) λ a a' ε _ → B a a' ε
 d .Elimℝ.ratA = ratA
 d .Elimℝ.limA x p a x₁ = limA a x₁
 d .Elimℝ.eqA p a a' x x₁ = eqA a a' x₁
 d .Elimℝ.rat-rat-B q r ε x x₁ = rat-rat-B q r ε x x₁
 d .Elimℝ.rat-lim-B q y ε δ p v r v' u' x = rat-lim-B q v' ε u' δ v x
 d .Elimℝ.lim-rat-B x r ε δ p v u v' u' x₁ =
  lim-rat-B v' r ε δ u' v x₁
 d .Elimℝ.lim-lim-B x y ε δ η p p' v r v' u' v'' u'' x₁ =
   lim-lim-B v' v'' ε δ η u' u'' v x₁
 d .Elimℝ.isPropB a a' ε u = isPropB a a' ε

 go : ℝ → A
 go~ : {x x' : ℝ} {ε : ℚ₊} (r : x ∼[ ε ] x') →
         B (go x) (go x') ε
 go = Elimℝ.go d



 go~ = Elimℝ.go∼ d

subst∼ : ∀ {u v ε ε'} → fst ε ≡ fst ε' → u ∼[ ε ] v → u ∼[ ε' ] v
subst∼ = subst (_ ∼[_] _) ∘ ℚ₊≡

_subst∼[_]_ : ∀ {x x' y y' ε ε'} →
              x ≡ x' → ε ≡ ε' → y ≡ y' →
               x ∼[ ε ] y → x' ∼[ ε' ] y'
_subst∼[_]_ p q r = transport λ i → p i ∼[ q i ] r i

record Casesℝ {ℓ} {ℓ'} (A : Type ℓ)
               (B : A → A → ℚ₊ → Type ℓ') : Type (ℓ-max ℓ ℓ') where
 field
  ratA : ℚ → A
  limA : (x : ℚ₊ → ℝ) →
             ((δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε) → A
  eqA : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

  rat-rat-B : (q r : ℚ) (ε : ℚ₊) (x : (ℚ.- fst ε) ℚ.< (q ℚ.- r))
      (x₁ : (q ℚ.- r) ℚ.< fst ε) →
      B (ratA q) (ratA r) ε
  rat-lim-B : (q : ℚ) (y : ℚ₊ → ℝ) (ε δ : ℚ₊)
      (p : (δ₁ ε₁ : ℚ₊) → y δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] y ε₁)
      (v : 0< (fst ε ℚ.- fst δ))
      (r : rat q ∼[ (fst ε ℚ.- fst δ) , v ] y δ) (v' : (q₁ : ℚ₊) → A)
      (u' : (δ₁ ε₁ : ℚ₊) → B (v' δ₁) (v' ε₁) (δ₁ ℚ₊+ ε₁)) →
      B (ratA q) (v' δ) ((fst ε ℚ.- fst δ) , v) → B (ratA q) (limA y p) ε
  lim-rat-B : (x : ℚ₊ → ℝ) (r : ℚ) (ε δ : ℚ₊)
      (p : (δ₁ ε₁ : ℚ₊) → x δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] x ε₁)
      (v : 0< (fst ε ℚ.- fst δ))
      (u : x δ ∼[ (fst ε ℚ.- fst δ) , v ] rat r) (v' : (q : ℚ₊) → A)
      (u' : (δ₁ ε₁ : ℚ₊) → B (v' δ₁) (v' ε₁) (δ₁ ℚ₊+ ε₁)) →
      B (v' δ) (ratA r) ((fst ε ℚ.- fst δ) , v) → B (limA x p) (ratA r) ε
  lim-lim-B : (x y : ℚ₊ → ℝ) (ε δ η : ℚ₊)
      (p : (δ₁ ε₁ : ℚ₊) → x δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] x ε₁)
      (p' : (δ₁ ε₁ : ℚ₊) → y δ₁ ∼[ δ₁ ℚ₊+ ε₁ ] y ε₁)
      (v : 0< (fst ε ℚ.- (fst δ ℚ.+ fst η)))
      (r : x δ ∼[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , v ] y η) →
      B (limA x p) (limA y p') ε

  isPropB : ∀ a a' ε → isProp (B a a' ε)

 d : Elimℝ (λ _ → A) λ a a' ε _ → B a a' ε
 d .Elimℝ.ratA = ratA
 d .Elimℝ.limA x p a x₁ = limA x p
 d .Elimℝ.eqA p a a' x x₁ = eqA a a' x₁
 d .Elimℝ.rat-rat-B = rat-rat-B
 d .Elimℝ.rat-lim-B = rat-lim-B
 d .Elimℝ.lim-rat-B = lim-rat-B
 d .Elimℝ.lim-lim-B x y ε δ η p p' v₁ r _ _ _ _ _ =
   lim-lim-B x y ε δ η p p' v₁ r
 d .Elimℝ.isPropB a a' ε _ = isPropB a a' ε

 go : ℝ → A
 go~ : {x x' : ℝ} {ε : ℚ₊} (r : x ∼[ ε ] x') →
         B (go x) (go x') ε
 go = Elimℝ.go d
 go~ = Elimℝ.go∼ d

