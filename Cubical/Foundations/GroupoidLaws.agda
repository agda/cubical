{-

This file proves the higher groupoid structure of types
for homogeneous and heterogeneous paths

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.GroupoidLaws where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A

_⁻¹ : (x ≡ y) → (y ≡ x)
x≡y ⁻¹ = sym x≡y

infix 40 _⁻¹

-- homogeneous groupoid laws

symInvo : (p : x ≡ y) → p ≡ p ⁻¹ ⁻¹
symInvo p = refl

rUnit : (p : x ≡ y) → p ≡ p ∙ refl
rUnit p j i = compPath-filler p refl j i

-- The filler of left unit: lUnit-filler p =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) x (p (~ j ∨ i)))
-- (refl i) (λ j → compPath-filler refl p i j)) (λ k i → (p (~ k ∧ i ))) (lUnit p)

lUnit-filler : {x y : A} (p : x ≡ y) → I → I → I → A
lUnit-filler {x = x} p j k i =
  hfill (λ j → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∨ j )
                  ; (k = i0) → p i
               -- ; (k = i1) → compPath-filler refl p j i
                  }) (inS (p (~ k ∧ i ))) j

lUnit : (p : x ≡ y) → p ≡ refl ∙ p
lUnit p j i = lUnit-filler p i1 j i

symRefl : refl {x = x} ≡ refl ⁻¹
symRefl i = refl

compPathRefl : refl {x = x} ≡ refl ∙ refl
compPathRefl = rUnit refl

-- The filler of right cancellation: rCancel-filler p =
-- PathP (λ i → PathP (λ j → PathP (λ k → A) x (p (~ j ∧ ~ i)))
-- (λ j → compPath-filler p (p ⁻¹) i j) (refl i)) (λ j i → (p (i ∧ ~ j))) (rCancel p)

rCancel-filler : ∀ {x y : A} (p : x ≡ y) → (k j i : I) → A
rCancel-filler {x = x} p k j i =
  hfill (λ k → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∧ ~ j)
               -- ; (j = i0) → compPath-filler p (p ⁻¹) k i
                  ; (j = i1) → x
                  }) (inS (p (i ∧ ~ j))) k

rCancel : (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
rCancel {x = x} p j i = rCancel-filler p i1 j i

rCancel-filler' : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → (i j k : I) → A
rCancel-filler' {x = x} {y} p i j k =
  hfill
    (λ i → λ
      { (j = i1) → p (~ i ∧ k)
      ; (k = i0) → x
      ; (k = i1) → p (~ i)
      })
    (inS (p k))
    (~ i)

rCancel' : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
rCancel' p j k = rCancel-filler' p i0 j k

lCancel : (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
lCancel p = rCancel (p ⁻¹)

assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  p ∙ q ∙ r ≡ (p ∙ q) ∙ r
assoc p q r k = (compPath-filler p q k) ∙ compPath-filler' q r (~ k)


-- heterogeneous groupoid laws

symInvoP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
     PathP (λ j → PathP (λ i → symInvo (λ i → A i) j i) x y) p (symP (symP p))
symInvoP p = refl

rUnitP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
  PathP (λ j → PathP (λ i → rUnit (λ i → A i) j i) x y) p (compPathP p refl)
rUnitP p j i = compPathP-filler p refl j i

lUnitP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
  PathP (λ j → PathP (λ i → lUnit (λ i → A i) j i) x y) p (compPathP refl p)
lUnitP {A = A} {x = x} p k i =
  comp (λ j → lUnit-filler (λ i → A i) j k i)
       (λ j → λ { (i = i0) → x
                ; (i = i1) → p (~ k ∨ j )
                ; (k = i0) → p i
                }) (p (~ k ∧ i ))

rCancelP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
   PathP (λ j → PathP (λ i → rCancel (λ i → A i) j i) x x) (compPathP p (symP p)) refl
rCancelP {A = A} {x = x} p j i =
  comp (λ k → rCancel-filler (λ i → A i) k j i)
       (λ k → λ { (i = i0) → x
                ; (i = i1) → p (~ k ∧ ~ j)
                ; (j = i1) → x
                }) (p (i ∧ ~ j))

lCancelP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → (p : PathP A x y) →
   PathP (λ j → PathP (λ i → lCancel (λ i → A i) j i) y y) (compPathP (symP p) p) refl
lCancelP p = rCancelP (symP p)



assocP : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
  {C_i1 : Type ℓ} {C : (B i1) ≡ C_i1} {w : C i1} (p : PathP A x y) (q : PathP (λ i → B i) y z) (r : PathP (λ i → C i) z w) →
  PathP (λ j → PathP (λ i → assoc (λ i → A i) B C j i) x w) (compPathP p (compPathP q r)) (compPathP (compPathP p q) r)
assocP {A = A} {B = B} {C = C} p q r k i =
    comp (hfill  (λ j → λ {
                     (i = i0) → A i0
                   ; (i = i1) → compPath-filler' (λ i₁ → B i₁) (λ i₁ → C i₁) (~ k) j })
                     (inS (compPath-filler (λ i₁ → A i₁) (λ i₁ → B i₁) k i)) )
     (λ j → λ
      { (i = i0) → p i0
      ; (i = i1) →
        comp (hfill ((λ l → λ
            { (j = i0) → B k
            ; (j = i1) → C l
            ; (k = i1) → C (j ∧ l)
            })) (inS (B ( j ∨ k)) ) )
          (λ l → λ
            { (j = i0) → q k
            ; (j = i1) → r l
            ; (k = i1) → r (j ∧ l)
            })
          (q (j ∨ k))
      })
    (compPathP-filler p q k i)



-- Loic's code below

-- some exchange law for doubleCompPath and refl

rhombus-filler : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → A
rhombus-filler p q i j =
  hcomp (λ t → λ { (i = i0) → p (~ t ∨ j)
                 ; (i = i1) → q (t ∧ j)
                 ; (j = i0) → p (~ t ∨ i)
                 ; (j = i1) → q (t ∧ i) })
        (p i1)

leftright : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) →
            (refl ∙∙ p ∙∙ q) ≡ (p ∙∙ q ∙∙ refl)
leftright p q i j =
  hcomp (λ t → λ { (j = i0) → p (i ∧ (~ t))
                 ; (j = i1) → q (t ∨ i) })
        (rhombus-filler p q i j)

-- equating doubleCompPath and a succession of two compPath

split-leftright : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ∙∙ q ∙∙ r) ≡ (refl ∙∙ (p ∙∙ q ∙∙ refl) ∙∙ r)
split-leftright p q r j i =
  hcomp (λ t → λ { (i = i0) → p (~ j ∧ ~ t)
                 ; (i = i1) → r t })
        (doubleCompPath-filler p q refl j i)

split-leftright' : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) →
                  (p ∙∙ q ∙∙ r) ≡ (p ∙∙ (refl ∙∙ q ∙∙ r) ∙∙ refl)
split-leftright' p q r j i =
  hcomp (λ t → λ { (i = i0) → p (~ t)
                 ; (i = i1) → r (j ∨ t) })
        (doubleCompPath-filler refl q r j i)

doubleCompPath-elim : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                      (r : y ≡ z) → (p ∙∙ q ∙∙ r) ≡ (p ∙ q) ∙ r
doubleCompPath-elim p q r = (split-leftright p q r) ∙ (λ i → (leftright p q (~ i)) ∙ r)

doubleCompPath-elim' : {ℓ : Level} {A : Type ℓ} {w x y z : A} (p : w ≡ x) (q : x ≡ y)
                       (r : y ≡ z) → (p ∙∙ q ∙∙ r) ≡ p ∙ (q ∙ r)
doubleCompPath-elim' p q r = (split-leftright' p q r) ∙ (sym (leftright p (q ∙ r)))


cong-∙ : ∀ {B : Type ℓ} (f : A → B) (p : x ≡ y) (q : y ≡ z)
         → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
cong-∙ f p q j i = hcomp (λ k → λ { (j = i0) → f (compPath-filler p q k i)
                                  ; (i = i0) → f (p i0)
                                  ; (i = i1) → f (q k) })
                         (f (p i))

cong-∙∙ : ∀ {B : Type ℓ} (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
cong-∙∙ f p q r j i = hcomp (λ k → λ { (j = i0) → f (doubleCompPath-filler p q r k i)
                                     ; (i = i0) → f (p (~ k))
                                     ; (i = i1) → f (r k) })
                            (f (q i))

hcomp-unique : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
               (h2 : ∀ i → A [ (φ ∨ ~ i) ↦ (\ { (φ = i1) → u i 1=1; (i = i0) → outS u0}) ])
               → (hcomp u (outS u0) ≡ outS (h2 i1)) [ φ ↦ (\ { (φ = i1) → (\ i → u i1 1=1)}) ]
hcomp-unique {φ = φ} u u0 h2 = inS (\ i → hcomp (\ k → \ { (φ = i1) → u k 1=1
                                                            ; (i = i1) → outS (h2 k) })
                                                   (outS u0))


lid-unique : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
               (h1 h2 : ∀ i → A [ (φ ∨ ~ i) ↦ (\ { (φ = i1) → u i 1=1; (i = i0) → outS u0}) ])
               → (outS (h1 i1) ≡ outS (h2 i1)) [ φ ↦ (\ { (φ = i1) → (\ i → u i1 1=1)}) ]
lid-unique {φ = φ} u u0 h1 h2 = inS (\ i → hcomp (\ k → \ { (φ = i1) → u k 1=1
                                                            ; (i = i0) → outS (h1 k)
                                                            ; (i = i1) → outS (h2 k) })
                                                   (outS u0))


transp-hcomp : ∀ {ℓ} (φ : I) {A' : Set ℓ}
                     (A : (i : I) → Set ℓ [ φ ↦ (λ _ → A') ]) (let B = \ (i : I) → outS (A i))
                 → ∀ {ψ} (u : I → Partial ψ (B i0)) → (u0 : B i0 [ ψ ↦ u i0 ]) →
                 (transp B φ (hcomp u (outS u0)) ≡ hcomp (\ i o → transp B φ (u i o)) (transp B φ (outS u0)))
                   [ ψ ↦ (\ { (ψ = i1) → (\ i → transp B φ (u i1 1=1))}) ]
transp-hcomp φ A u u0 = inS (sym (outS (hcomp-unique
               ((\ i o → transp B φ (u i o))) (inS (transp B φ (outS u0)))
                 \ i → inS (transp B φ (hfill u u0 i)))))
  where
    B = \ (i : I) → outS (A i)


hcomp-cong : ∀ {ℓ} {A : Set ℓ} {φ} → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ]) →
                                    (u' : I → Partial φ A) → (u0' : A [ φ ↦ u' i0 ]) →

             (ueq : ∀ i → PartialP φ (\ o → u i o ≡ u' i o)) → (outS u0 ≡ outS u0') [ φ ↦ (\ { (φ = i1) → ueq i0 1=1}) ]
             → (hcomp u (outS u0) ≡ hcomp u' (outS u0')) [ φ ↦ (\ { (φ = i1) → ueq i1 1=1 }) ]
hcomp-cong u u0 u' u0' ueq 0eq = inS (\ j → hcomp (\ i o → ueq i o j) (outS 0eq j))


invSides-filler : {x y z : A} (p : x ≡ y) (q : x ≡ z) → PathP (λ j → q j ≡ p (~ j)) p (sym q)
invSides-filler {A = A} {x = x} p q i j =
  hcomp (λ k → λ { (i = i0) → p (k ∧ j)
                  ; (i = i1) → q (~ j ∧ k)
                  ; (j = i0) → q (i ∧ k)
                  ; (j = i1) → p (~ i ∧ k)})
        x

congFunct-filler : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z)
                → I → I → I → B
congFunct-filler {x = x} f p q i j z =
  hfill (λ k → λ { (i = i0) → f x
                  ; (i = i1) → f (q k)
                  ; (j = i0) → f (compPath-filler p q k i)})
        (inS (f (p i)))
        z

congFunct : ∀ {ℓ} {B : Type ℓ} (f : A → B) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ cong f p ∙ cong f q
congFunct f p q j i = congFunct-filler f p q i j i1


-- congFunct for dependent types
congFunct-dep : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} (f : (a : A) → B a) (p : x ≡ y) (q : y ≡ z)
         → PathP (λ i → PathP (λ j → B (compPath-filler p q i j)) (f x) (f (q i))) (cong f p) (cong f (p ∙ q))
congFunct-dep {B = B} {x = x} f p q i j = f (compPath-filler p q i j)

cong₂Funct : (f : A → A → A) →
        (p : x ≡ y) →
        {u v : A} (q : u ≡ v) →
        cong₂ f p q ≡ cong (λ x → f x u) p ∙ cong (f y) q
cong₂Funct {x = x} {y = y} f p {u = u} {v = v} q j i =
  hcomp (λ k → λ { (i = i0) → f x u
                  ; (i = i1) → f y (q k)
                  ; (j = i0) → f (p i) (q (i ∧ k))})
       (f (p i) u)


symDistr-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → I → A
symDistr-filler {A = A} {z = z} p q i j k =
  hfill (λ k → λ { (i = i0) → q (k ∨ j)
                  ; (i = i1) → p (~ k ∧ j) })
        (inS (invSides-filler q (sym p) i j))
        k

symDistr : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ sym q ∙ sym p
symDistr p q i j = symDistr-filler p q j i i1




pentagonIdentity : (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (s : w ≡ v)
                      →
            (assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s)
                              ≡
   cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)

pentagonIdentity {x = x} {y} p q r s =
        (λ i →
              (λ j → cong (p ∙_) (assoc q r s) (i ∧ j))
           ∙∙ (λ j → lemma₀₀ i j ∙ lemma₀₁ i j)
           ∙∙ (λ j → lemma₁₀ i j ∙ lemma₁₁ i j)
        )
   where


    lemma₀₀ : ( i j : I) → _ ≡ _
    lemma₀₀ i j i₁ =
         hcomp
        (λ k → λ { (j = i0) → p i₁
                 ; (i₁ = i0) → x
                 ; (i₁ = i1) → hcomp
                                 (λ k₁ → λ { (i = i0) → (q (j ∧ k))
                                           ; (k = i0) → y
                                           ; (j = i0) → y
                                           ; (j = i1)(k = i1) → r (k₁ ∧ i)})
                                 (q (j ∧ k))
        }) (p i₁)

    lemma₀₁ : ( i j : I) → hcomp
                       (λ k → λ {(i = i0) → q j
                               ; (j = i0) → y
                               ; (j = i1) → r (k ∧ i)
                          })
                       (q j) ≡ _
    lemma₀₁ i j i₁ = (hcomp
                        (λ k → λ { (j = i1) → hcomp
                                                (λ k₁ → λ { (i₁ = i0) → r i
                                                          ; (k = i0) → r i
                                                          ; (i = i1) → s (k₁ ∧  k ∧  i₁)
                                                          ; (i₁ = i1)(k = i1) → s k₁ })
                                                (r ((i₁ ∧ k) ∨ i))
                                  ; (i₁ = i0) → compPath-filler q r i j
                                  ; (i₁ = i1) → hcomp
                                                  (λ k₁ → λ { (k = i0) → r i
                                                            ; (k = i1) → s k₁
                                                            ; (i = i1) → s (k ∧ k₁)})
                                                  (r (i ∨ k))})
                         (hfill
                             (λ k → λ { (j = i1) → r k
                                      ; (i₁ = i1) → r k
                                      ; (i₁ = i0)(j = i0) → y })
                             (inS (q (i₁ ∨ j))) i))

    lemma₁₁ : ( i j : I) → (r (i ∨ j)) ≡ _
    lemma₁₁ i j i₁ =
           hcomp
             (λ k → λ { (i = i1) → s (i₁ ∧ k)
                      ; (j = i1) → s (i₁ ∧ k)
                      ; (i₁ = i0) → r (i ∨ j)
                      ; (i₁ = i1) → s k
              }) (r (i ∨ j ∨ i₁))


    lemma₁₀-back :  I → I → I → _
    lemma₁₀-back i j i₁ =
        hcomp
         (λ k → λ {
           (i₁ = i0) → x
         ; (i₁ = i1) → hcomp
                         (λ k₁ → λ { (k = i0) → q (j ∨ ~ i)
                                   ; (k = i1) → r (k₁ ∧ j)
                                   ; (j = i0) → q (k ∨ ~ i)
                                   ; (j = i1) → r (k₁ ∧ k)
                                   ; (i = i0) → r (k ∧ j ∧ k₁)
                         })
                         (q (k ∨ j ∨ ~ i))
         ; (i = i0)(j = i0) → (p ∙ q) i₁
         })
        (hcomp
           (λ k → λ { (i₁ = i0) → x
                    ; (i₁ = i1) → q ((j ∨ ~ i ) ∧ k)
                    ; (j = i0)(i = i1) → p i₁
            })
            (p i₁))


    lemma₁₀-front : I → I → I → _
    lemma₁₀-front i j i₁ =
       (((λ _ → x) ∙∙ compPath-filler p q j ∙∙
         (λ i₁ →
             hcomp
                (λ k → λ { (i₁ = i0) → q j
                         ; (i₁ = i1) → r (k ∧ (j ∨ i))
                         ; (j = i0)(i = i0) → q i₁
                         ; (j = i1) → r (i₁ ∧ k)
               })
            (q (j ∨ i₁))
         )) i₁)

    compPath-filler-in-filler :
                (p : _ ≡ y) → (q : _ ≡ _ )
              → _≡_ {A = Square (p ∙ q) (p ∙ q) (λ _ → x) (λ _ → z)}
               (λ i j → hcomp
                          (λ i₂ →
                           λ { (j = i0) → x
                             ; (j = i1) → q (i₂ ∨ ~ i)
                             ; (i = i0) → (p ∙ q) j
                            })
                          (compPath-filler p q (~ i) j))
               (λ _ → p ∙ q)
    compPath-filler-in-filler p q z i j =
       hcomp
         (λ k → λ {
            (j = i0) → p i0
          ; (j = i1) → q (k ∨ ~ i ∧ ~ z)
          ; (i = i0) → hcomp
                       (λ i₂ → λ {
                         (j = i0) → p i0
                        ;(j = i1) → q ((k ∨  ~ z) ∧ i₂)
                        ;(z = i1) (k = i0) → p j
                       })
                      (p j)
          ; (i = i1) →  compPath-filler p (λ i₁ → q (k ∧ i₁)) k j
          ; (z = i0) → hfill
                         ((λ i₂ → λ { (j = i0) → p i0
                             ; (j = i1) → q (i₂ ∨ ~ i)
                             ; (i = i0) → (p ∙ q) j
                            }))
                         (inS ((compPath-filler p q (~ i) j))) k
          ; (z = i1) → compPath-filler p q k j
         })
         (compPath-filler p q (~ i ∧ ~ z) j)


    cube-comp₋₀₋ :
        (c : I → I → I → A)
      → {a' : Square _ _ _ _}
      → (λ i i₁ → c i i0 i₁) ≡ a'
      → (I → I → I → A)
    cube-comp₋₀₋ c p i j k =
       hcomp
         (λ l → λ {
            (i = i0) → c i0 j k
           ;(i = i1) → c i1 j k
           ;(j = i0) → p l i k
           ;(j = i1) → c i i1 k
           ;(k = i0) → c i j i0
           ;(k = i1) → c i j i1
          })
        (c i j k)

    cube-comp₀₋₋ :
        (c : I → I → I → A)
      → {a' : Square _ _ _ _}
      → (λ i i₁ → c i0 i i₁) ≡ a'
      → (I → I → I → A)
    cube-comp₀₋₋ c p i j k =
       hcomp
         (λ l → λ {
            (i = i0) → p l j k
           ;(i = i1) → c i1 j k
           ;(j = i0) → c i i0 k
           ;(j = i1) → c i i1 k
           ;(k = i0) → c i j i0
           ;(k = i1) → c i j i1
          })
        (c i j k)



    lemma₁₀-back' : _
    lemma₁₀-back' k j i₁ =
       (cube-comp₋₀₋ (lemma₁₀-back)
         (compPath-filler-in-filler p q)) k j i₁


    lemma₁₀ : ( i j : I) → _ ≡ _
    lemma₁₀ i j i₁ =
        (cube-comp₀₋₋ lemma₁₀-front (sym lemma₁₀-back')) i j i₁
