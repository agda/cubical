{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.Mnd.Examples where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.MndContainer.Base
open import Cubical.Algebra.MndContainer.Examples
open import Cubical.Algebra.DistributiveLaw.Mnd.Base
open import Cubical.Data.Containers.Set.Base
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open MndContainer
open IsMndContainer
open MndDistributiveLaw

private
  variable
    ℓs ℓp : Level

MaybeDistr : (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)}
             (MC : MndContainer {ℓs} {ℓp} (S ◁ P & setS & setP)) →
             MndDistributiveLaw {ℓs} {ℓp} Bool* JustOrNothing isSetBool* isSetJustOrNothing S P setS setP MaybeM MC
u₁ (MaybeDistr S P MC) (lift true) f = f tt*
u₁ (MaybeDistr S P MC) (lift false) f = MC .ι
u₂ (MaybeDistr S P MC) (lift true) f _ = true*
u₂ (MaybeDistr S P MC) (lift false) f _ = false*
v₁ (MaybeDistr S P MC) {lift true} _ x = tt*
v₂ (MaybeDistr S P MC) {lift true} {f} p x = p
unit-ιB-shape₁ (MaybeDistr S P MC) (lift true) = refl
unit-ιB-shape₁ (MaybeDistr S P MC) (lift false) = refl
unit-ιB-shape₂ (MaybeDistr S P MC) (lift true) = refl
unit-ιB-shape₂ (MaybeDistr S P MC) (lift false) = refl
unit-ιB-pos₁ (MaybeDistr S P MC) (lift true) i q tt* = tt*
unit-ιB-pos₂ (MaybeDistr S P MC) (lift true) i q tt* = q
unit-ιA-shape₁ (MaybeDistr S P MC) _ = refl
unit-ιA-shape₂ (MaybeDistr S P MC) _ = refl
unit-ιA-pos₁ (MaybeDistr S P MC) s i q tt* = tt*
unit-ιA-pos₂ (MaybeDistr S P MC) s i q tt* = q
mul-A-shape₁ (MaybeDistr S P MC) (lift true) f g = refl
mul-A-shape₁ (MaybeDistr S P MC) (lift false) f g = refl
mul-A-shape₂ (MaybeDistr S P MC) (lift true) f g = refl
mul-A-shape₂ (MaybeDistr S P MC) (lift false) f g = refl
mul-A-pos₁ (MaybeDistr S P MC) (lift true) f g = refl
mul-A-pos₁ (MaybeDistr {ℓs} {ℓp} S P MC) (lift false) f g i q ()
mul-A-pos₂₁ (MaybeDistr S P MC) (lift true) f g = refl
mul-A-pos₂₁ (MaybeDistr {ℓs} {ℓp} S P MC) (lift false) f g i q ()
mul-A-pos₂₂ (MaybeDistr S P MC) (lift true) f g = refl
mul-A-pos₂₂ (MaybeDistr S P MC) (lift false) f g i q ()
mul-B-shape₁ (MaybeDistr S P MC) (lift true) f g = refl
mul-B-shape₁ (MaybeDistr S P MC) (lift false) f g i = unit-r (isMndContainer MC) (MC .ι) (~ i)
mul-B-shape₂ (MaybeDistr S P MC) (lift true) f g = refl
mul-B-shape₂ (MaybeDistr S P MC) (lift false) f g i = λ _ → false*
mul-B-pos₁ (MaybeDistr S P MC) (lift true) f g i q tt* = tt* 
mul-B-pos₁ (MaybeDistr S P MC) (lift false) f g i q ()
mul-B-pos₂₁ (MaybeDistr S P MC) (lift true) f g i q tt* = (MC .pr₁) (f tt*) (g tt*) q
mul-B-pos₂₁ (MaybeDistr S P MC) (lift false) f g i q ()
mul-B-pos₂₂ (MaybeDistr S P MC) (lift true) f g i q tt* = (MC .pr₂) (f tt*) (g tt*) q
mul-B-pos₂₂ (MaybeDistr S P MC) (lift false) f g i q ()

lemF : ∀ {ℓ ℓ'} {A : Type ℓ} (f g : ⊥* {ℓ'} → A) → f ≡ g
lemF f g = sym (isContrΠ⊥* .snd f) ∙ isContrΠ⊥* .snd g

Unit*-singleton : ∀ {ℓ} → (x : Unit* {ℓ}) → x ≡ tt*
Unit*-singleton tt* i = tt*

module MaybeDistrUnique (S : Type ℓs) (P : S → Type ℓp) (setS : isSet S) (setP : ∀ {s} → isSet (P s))
                        (MC : MndContainer {ℓs} {ℓp} (S ◁ P & setS & setP))
                        (l : MndDistributiveLaw {ℓs} {ℓp} Bool* JustOrNothing isSetBool* isSetJustOrNothing S P setS setP MaybeM MC) where

  L₀ = MaybeDistr S P MC

  u1 : (s : Bool*) (f : JustOrNothing s → S) → u₁ L₀ s f ≡ u₁ l s f
  u1 (lift true) f i = hcomp (λ j → λ { (i = i0) → f tt*
                               ; (i = i1) → u₁ l true* (λ x → f (Unit*-singleton x (~ j)))
                               }) 
                      (unit-ιA-shape₁ l (f tt*) (~ i))
  u1 (lift false) f i = hcomp (λ j → λ { (i = i0) → ι MC
                                ; (i = i1) → u₁ l false* (lemF (const (ι MC)) f j) 
                                })
                       (unit-ιB-shape₁ l false* (~ i))

  u2 : (s : Bool*) (f : JustOrNothing s → S) →
       PathP (λ i → P (u1 s f i) → Bool*) (u₂ L₀ s f) (u₂ l s f)
  u2 (lift true) f i = comp (λ j → P (compPath-filler (λ i' → unit-ιA-shape₁ l (f tt*) (~ i')) 
                                               (λ i' → u₁ l true* (λ x → f (Unit*-singleton x (~ i')))) j i
                              ) → Bool* {ℓs})
                     (λ j → λ { (i = i0) → λ p → true* ;
                                (i = i1) → λ p → u₂ l true* (λ x → f (Unit*-singleton x (~ j))) p })
                     (λ p → unit-ιA-shape₂ l (f tt*) (~ i) p)
  u2 (lift false) f = compPathP' {B = (λ x → P x → Bool*)}
                          {x' = λ x → unit-ιB-shape₂ l false* (~ i0) x}
                          {y' = λ p → unit-ιB-shape₂ l false* (~ i1) p}
                          {z' = λ p → u₂ l false* (lemF (const (ι MC)) f i1) p}
                          (λ i p → unit-ιB-shape₂ l false* (~ i) p) 
                          (λ i p → u₂ l false* (lemF (const (ι MC)) f i) p)

  v1 : (s : Bool*) (f : JustOrNothing s → S) →
       PathP (λ i → (p : P (u1 s f i)) → JustOrNothing (u2 s f i p) → JustOrNothing s)
             (λ p q → v₁ L₀ {s} {f} p q) 
             (λ p q → v₁ l {s} {f} p q)
  v1 (lift true) f i = comp (λ j → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt*) (~ k)) 
                                                    (λ k → u₁ l true* (λ x → f (Unit*-singleton x (~ k)))) j i
                                   )) → 
                            JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → Bool*)}
                                                                       (λ k p' → unit-ιA-shape₂ l (f tt*) (~ k) p') 
                                                                       (λ k p' → u₂ l true* (λ x → f (Unit*-singleton x (~ k))) p') j i p
                                          ) → 
                            Unit* {ℓp}
                     )
                     (λ j → λ { (i = i0) → λ p q → tt* ;
                                (i = i1) → λ p q → Unit*-singleton (v₁ l p q) (~ j)
                              })
                     (λ p q → tt*)
  v1 (lift false) f = toPathP (funExt λ p → funExt (λ q → rec* (subst JustOrNothing (lem p) q)))
    where
      lem : (p : P (u₁ l false* f)) → u₂ l false* f p ≡ false*
      lem p = funExt⁻ (sym (fromPathP (u2 false* f))) p

  v2 : (s : Bool*) (f : JustOrNothing s → S) →
       PathP (λ i → (p : P (u1 s f i)) (q : JustOrNothing (u2 s f i p)) → P (f (v1 s f i p q)))
             (λ p q → v₂ L₀ {s} {f} p q) 
             (λ p q → v₂ l {s} {f} p q)
  v2 (lift true) f i =    
      comp (λ j → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt*) (~ k)) 
                                          (λ k → u₁ l true* (λ x → f (Unit*-singleton x (~ k)))) j i
                         )) → 
                            (q : JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → Bool*)}
                                                                            (λ k p' → unit-ιA-shape₂ l (f tt*) (~ k) p') 
                                                                            (λ k p' → u₂ l true* (λ x → f (Unit*-singleton x (~ k))) p') j i p
                                                         )) → 
                            P (f (fill (λ k' → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt*) (~ k)) 
                                                                       (λ k → u₁ l true* (λ x → f (Unit*-singleton x (~ k)))) k' i
                                                      )) → 
                                               JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → Bool*)}
                                                                                          (λ k p' → unit-ιA-shape₂ l (f tt*) (~ k) p') 
                                                                                          (λ k p' → u₂ l true* (λ x → f (Unit*-singleton x (~ k))) p') k' i p
                                                                       ) → 
                                               Unit* {ℓp}
                                       )
                                       (λ k' → λ { (i = i0) → λ p q → tt*
                                                 ; (i = i1) → λ p q → Unit*-singleton (v₁ l p q) (~ k')
                                                 })
                                       (inS (λ p q → tt*))
                                       j p q
                              ))
             )
             (λ j → λ { (i = i0) → λ p q → p
                      ; (i = i1) → λ p q → v₂ l {true*} {λ x → f (Unit*-singleton x (~ j))} p q
                      })
             (λ p q → unit-ιA-pos₂ l (f tt*) (~ i) p q)

  v2 (lift false) f = toPathP (funExt λ p → funExt (λ q → rec* (subst JustOrNothing (lem p) q)))
    where
      lem : (p : P (u₁ l false* f)) → u₂ l false* f p ≡ false*
      lem p = funExt⁻ (sym (fromPathP (u2 false* f))) p

ReaderDistr : (A : hSet ℓp) (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)} 
              (MC : MndContainer {ℓs} {ℓp} (S ◁ P & setS & setP))
            → MndDistributiveLaw {ℓs} {ℓp} S P setS setP (Unit* {ℓs}) (const (fst A)) isSetUnit* (snd A) MC (ReaderM A)
u₁ (ReaderDistr A S P MC) s _ = tt*
u₂ (ReaderDistr A S P MC) s _ a = s
v₁ (ReaderDistr A S P MC) a p = p
v₂ (ReaderDistr A S P MC) a p = a
unit-ιB-shape₂ (ReaderDistr A S P MC) s = refl
unit-ιB-shape₁ (ReaderDistr A S P MC) s = refl
unit-ιB-pos₁ (ReaderDistr A S P MC) s = refl
unit-ιB-pos₂ (ReaderDistr A S P MC) s i a p = a
unit-ιA-shape₂ (ReaderDistr A S P MC) tt* = refl
unit-ιA-shape₁ (ReaderDistr A S P MC) tt* = refl
unit-ιA-pos₁ (ReaderDistr A S P MC) tt* = refl
unit-ιA-pos₂ (ReaderDistr A S P MC) tt* = refl
mul-A-shape₁ (ReaderDistr A S P MC) s f g = refl
mul-A-shape₂ (ReaderDistr A S P MC) s f g = refl
mul-A-pos₁ (ReaderDistr A S P MC) s f g = refl
mul-A-pos₂₁ (ReaderDistr A S P MC) s f g = refl
mul-A-pos₂₂ (ReaderDistr A S P MC) s f g = refl
mul-B-shape₁ (ReaderDistr A S P MC) s f g = refl
mul-B-shape₂ (ReaderDistr A S P MC) s f g = refl
mul-B-pos₁  (ReaderDistr A S P MC) s f g = refl
mul-B-pos₂₁ (ReaderDistr A S P MC) s f g = refl
mul-B-pos₂₂ (ReaderDistr A S P MC) s f g = refl

module ReaderDistrUnique (A : hSet ℓp) (S : Type ℓs) (P : S → Type ℓp) {setS : isSet S} {setP : ∀ {s} → isSet (P s)} 
                         (MC : MndContainer {ℓs} {ℓp} (S ◁ P & setS & setP))
                         (L : MndDistributiveLaw {ℓs} {ℓp} S P setS setP (Unit* {ℓs}) (const (fst A)) isSetUnit* (snd A) MC (ReaderM A)) where

  L₀ = ReaderDistr A S P MC

  lemUnit* : (s : S) (f : P s → Unit* {ℓs}) → f ≡ const tt*
  lemUnit* s f i p = Unit*-singleton (f p) i

  u1 : (s : S) (f : P s → Unit* {ℓs}) → u₁ L₀ s f ≡ u₁ L s f
  u1 s f i = Unit*-singleton (u₁ L s f) (~ i)

  u2 : (s : S) (f : P s → Unit* {ℓs}) (a : fst A) → u₂ L₀ s f a ≡ u₂ L s f a
  u2 s f a i = hcomp (λ j → λ { (i = i0) → s
                              ; (i = i1) → u₂ L s (lemUnit* s f (~ j)) a }) (unit-ιB-shape₂ L s (~ i) a)

  v1 : (s : S) (f : P s → Unit* {ℓs}) (a : fst A) →
       PathP (λ i → P (u2 s f a i) → P s)
             (v₁ L₀ {s} {f} a)
             (v₁ L {s} {f} a)
  v1 s f a i p = compPathP' {B = (λ x → P x → P s)} side2 side1 i p
    where
      side1 : PathP (λ i → P (u₂ L s (lemUnit* s f (~ i)) a) → P s)
                    (v₁ L {s} {const tt*} a)
                    (v₁ L {s} {f} a)
      side1 i p = v₁ L {s} {lemUnit* s f (~ i)} a p

      side2 : PathP (λ i → P (unit-ιB-shape₂ L s (~ i) a) → P s)
                    (λ p → p)
                    (v₁ L {s} {const tt*} a)
      side2 i p = unit-ιB-pos₁ L s (~ i) a p

  v2 : (s : S) (f : P s → Unit* {ℓs}) (a : fst A) →
       PathP (λ i → P (u2 s f a i) → fst A)
             (v₂ L₀ {s} {f} a)
             (v₂ L {s} {f} a)
  v2 s f a i p = compPathP' {B = (λ x → P x → fst A)} side2 side1 i p
    where
      side1 : PathP (λ i → P (u₂ L s (lemUnit* s f (~ i)) a) → fst A)
                    (v₂ L {s} {const tt*} a)
                    (v₂ L {s} {f} a)
      side1 i p = v₂ L {s} {lemUnit* s f (~ i)} a p

      side2 : PathP (λ i → P (unit-ιB-shape₂ L s (~ i) a) → fst A)
                    (λ _ → a)
                    (v₂ L {s} {const tt*} a)
      side2 i p = unit-ιB-pos₂ L s (~ i) a p

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat

-- An example of a distributive law, this one is not unique for specific S ▷ P
WriterDistr : (A S : Type ℓs) (P : S → Type ℓp) {setA : isSet A} {setS : isSet S} {setP : ∀ {s} → isSet (P s)}
              (mon : MonoidStr A) → (MC : MndContainer {ℓs} {ℓp} (S ◁ P & setS & setP)) →
              MndDistributiveLaw {ℓs} {ℓp} A (const Unit*) setA  isSetUnit* S P setS setP (WriterM (A , setA) mon) MC
u₁ (WriterDistr A S P mon MC) a s = s tt*
u₂ (WriterDistr A S P mon MC) a s _ = a
v₁ (WriterDistr A S P mon MC) _ tt* = tt*
v₂ (WriterDistr A S P mon MC) p tt* = p
unit-ιB-shape₁ (WriterDistr A S P mon MC) a = refl
unit-ιB-shape₂ (WriterDistr A S P mon MC) a = refl
unit-ιB-pos₁ (WriterDistr A S P mon MC) a i p tt* = tt*
unit-ιB-pos₂ (WriterDistr A S P mon MC) a i p tt* = p
unit-ιA-shape₁ (WriterDistr A S P mon MC) s = refl
unit-ιA-shape₂ (WriterDistr A S P mon MC) s = refl
unit-ιA-pos₁ (WriterDistr A S P mon MC) s i p tt* = tt*
unit-ιA-pos₂ (WriterDistr A S P mon MC) s i p tt* = p
mul-A-shape₁ (WriterDistr A S P mon MC) a f g = refl
mul-A-shape₂ (WriterDistr A S P mon MC) a f g = refl
mul-A-pos₁ (WriterDistr A S P mon MC) a f g i p tt* = tt*
mul-A-pos₂₁ (WriterDistr A S P mon MC) a f g i p tt* = tt*
mul-A-pos₂₂ (WriterDistr A S P mon MC) a f g i p tt* = p
mul-B-shape₁ (WriterDistr A S P mon MC) a f g = refl
mul-B-shape₂ (WriterDistr A S P mon MC) a f g = refl
mul-B-pos₁ (WriterDistr A S P mon MC) a f g i p tt* = tt*
mul-B-pos₂₁ (WriterDistr A S P mon MC) a f g i p tt* = pr₁ MC (f tt*) (g tt*) p
mul-B-pos₂₂ (WriterDistr A S P mon MC) a f g i p tt* = pr₂ MC (f tt*) (g tt*) p
