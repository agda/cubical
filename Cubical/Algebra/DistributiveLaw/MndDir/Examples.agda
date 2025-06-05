{-# OPTIONS --safe #-}

module Cubical.Algebra.DistributiveLaw.MndDir.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.DistributiveLaw.MndDir.Base
open import Cubical.Algebra.DistributiveLaw.Mnd.Examples using (Unit*-singleton)
open import Cubical.Algebra.DirContainer.Examples
open import Cubical.Algebra.MndContainer.Examples
open import Cubical.Data.Unit

open MndDirDistributiveLaw

private
  variable
    ℓs ℓp : Level

WriterCReaderMDistr : (A : Type ℓs) {setA : isSet A} (B : hSet ℓp) → 
                      MndDirDistributiveLaw {ℓs} {ℓp} A (const (Unit* {ℓp})) setA isSetUnit*
                                            (Unit* {ℓs}) (const (fst B)) isSetUnit* (snd B) (WriterC (A , setA)) (ReaderM B)
u₁ (WriterCReaderMDistr A B) a f = tt*
u₂ (WriterCReaderMDistr A B) a f b = a
v₁ (WriterCReaderMDistr A B) b tt* = tt*
v₂ (WriterCReaderMDistr A B) b tt* = b
unit-oA-shape (WriterCReaderMDistr A B) a f i = Unit*-singleton (f tt*) (~ i)
unit-oA-pos₁ (WriterCReaderMDistr A B) a f i b = tt*
unit-oA-pos₂ (WriterCReaderMDistr A B) a f i b = b
mul-A-shape₁ (WriterCReaderMDistr A B) a f = refl
mul-A-shape₂ (WriterCReaderMDistr A B) a f = refl
mul-A-shape₃ (WriterCReaderMDistr A B) a f i b tt* = a
mul-A-pos₁ (WriterCReaderMDistr A B) s f i b tt* tt* = tt*
mul-A-pos₂ (WriterCReaderMDistr A B) s f i b tt* tt* = b
unit-ιB-shape₁ (WriterCReaderMDistr A B) a = refl
unit-ιB-shape₂ (WriterCReaderMDistr A B) a = refl
unit-ιB-pos₁ (WriterCReaderMDistr A B) a i b tt* = tt*
unit-ιB-pos₂ (WriterCReaderMDistr A B) a i b tt* = b
mul-B-shape₁ (WriterCReaderMDistr A B) a f g = refl
mul-B-shape₂ (WriterCReaderMDistr A B) a f g = refl
mul-B-pos₁ (WriterCReaderMDistr A B) a f g i b tt* = tt*
mul-B-pos₂₁ (WriterCReaderMDistr A B) a f g i b tt* = b
mul-B-pos₂₂ (WriterCReaderMDistr A B) a f g i b tt* = b

module WriterCReaderMDistrUnique (A : Type ℓs) {setA : isSet A} (B : hSet ℓp)
                     (L : MndDirDistributiveLaw {ℓs} {ℓp} A (const (Unit* {ℓp})) setA isSetUnit*
                                                (Unit* {ℓs}) (const (fst B)) isSetUnit* (snd B) (WriterC (A , setA)) (ReaderM B)) where

  L₀ = WriterCReaderMDistr A {setA} B

  lemUnit* : (a : A) (f : Unit* {ℓp} → Unit* {ℓs}) → f ≡ const tt*
  lemUnit* a f i p = Unit*-singleton (f p) i

  u1 : (a : A) (f : Unit* {ℓp} → Unit* {ℓs}) → u₁ L₀ a f ≡ u₁ L a f
  u1 a f i = Unit*-singleton (u₁ L a f) (~ i)

  u2 : (a : A) (f : Unit* {ℓp} → Unit* {ℓs}) (b : fst B) → u₂ L₀ a f b ≡ u₂ L a f b
  u2 a f b i = hcomp (λ j → λ { (i = i0) → a
                              ; (i = i1) → u₂ L a (lemUnit* a f (~ j)) b }) (unit-ιB-shape₂ L a (~ i) b)

  v1 : (a : A) (f : Unit* {ℓp} → Unit* {ℓs}) (b : fst B) (x : Unit* {ℓp}) → v₁ L₀ {a} {f} b x ≡ v₁ L {a} {f} b x
  v1 a f b tt* i = hcomp (λ j → λ { (i = i0) → tt*
                                 ; (i = i1) → v₁ L {a} {lemUnit* a f (~ j)} b tt* }) (unit-ιB-pos₁ L a (~ i) b tt*)

  v2 : (a : A) (f : Unit* {ℓp} → Unit* {ℓs}) (b : fst B) (x : Unit* {ℓp}) → v₂ L₀ {a} {f} b x ≡ v₂ L {a} {f} b x
  v2 a f b tt* i = hcomp (λ j → λ { (i = i0) → b
                                 ; (i = i1) → v₂ L {a} {lemUnit* a f (~ j)} b tt* }) (unit-ιB-pos₂ L a (~ i) b tt*)


open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat

record MonoidFuncAction {ℓa ℓb : Level} (A : Type ℓa) (B : Type ℓb)
                        (monA : MonoidStr A) (monB : MonoidStr B) :
                        Type (ℓ-suc (ℓ-max ℓa ℓb)) where 
  open MonoidStr monA renaming (ε to eᴬ ; _·_ to _⊕ᴬ_) 
  open MonoidStr monB renaming (ε to eᴮ ; _·_ to _⊕ᴮ_)
  field
    χ : (A → B) → A → A
    eᴬ-pres : (f : A → B) → χ f eᴬ ≡ eᴬ
    ⊕ᴬ-pres : (f : A → B) (a a' : A) →
             χ f (a ⊕ᴬ a') ≡ χ f a ⊕ᴬ χ (λ x → f (χ f a ⊕ᴬ x)) a' 
    eᴮ-pres : (a : A) → χ (const eᴮ) a ≡ a
    ⊕ᴮ-pres : (f g : A → B) (a : A) → χ (λ x → f x ⊕ᴮ g x) a ≡ χ f (χ (λ x → g (χ f x)) a)

open import Cubical.Algebra.DirContainer.Base
open import Cubical.Algebra.Semigroup
open MonoidFuncAction
open MonoidStr
open DirContainer
open IsMonoid
open IsSemigroup

ReaderCWriterMDistr : (A : Type ℓp) (B : Type ℓs) {setB : isSet B} →
                        (monA : MonoidStr A) (monB : MonoidStr B) → 
                        (t : MonoidFuncAction A B monA monB) →
                        MndDirDistributiveLaw {ℓs} {ℓp} Unit* (const A) isSetUnit* (monA .isMonoid .isSemigroup .is-set)
                          B (const Unit*) setB isSetUnit* (ReaderC A monA) (WriterM (B , setB) monB)
u₁ (ReaderCWriterMDistr {ℓs} {ℓp} A B monA monB t) tt* f = f (o (ReaderC {ℓs} {ℓp} A monA) tt*) 
u₂ (ReaderCWriterMDistr A B monA monB t) tt* f tt* = tt*
v₁ (ReaderCWriterMDistr A B monA monB t) {tt*} {f} tt* a = χ t f a
v₂ (ReaderCWriterMDistr A B monA monB t) {tt*} {f} tt* a = tt*
unit-oA-shape (ReaderCWriterMDistr A B monA monB t) tt* f = refl
unit-oA-pos₁ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* = eᴬ-pres t f i
unit-oA-pos₂ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* = tt*
mul-A-shape₁ (ReaderCWriterMDistr A B monA monB t) tt* f i = f (monA .·IdL (monA .ε) (~ i) )
mul-A-shape₂ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* = tt*
mul-A-shape₃ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* a = tt*
mul-A-pos₁ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* a a' = (⊕ᴬ-pres t f a a' ∙ sym lem) i
  where 
    lem : (monA · χ t (λ p → f ((monA · p) (monA .ε))) a) (χ t (λ p' → f ((monA · χ t (λ p → f ((monA · p) (monA .ε))) a) p')) a')
          ≡ (monA · χ t f a) (χ t (λ x → f ((monA · χ t f a) x)) a')
    lem i = (monA · χ t (λ p → f (monA .·IdR p i)) a) (χ t (λ x → f ((monA · χ t (λ p → f (monA .·IdR p i)) a) x)) a')
mul-A-pos₂ (ReaderCWriterMDistr A B monA monB t) tt* f i tt* a a' = tt*
unit-ιB-shape₁ (ReaderCWriterMDistr A B monA monB t) tt* = refl
unit-ιB-shape₂ (ReaderCWriterMDistr A B monA monB t) tt* i tt* = tt*
unit-ιB-pos₁ (ReaderCWriterMDistr A B monA monB t) tt* i tt* a = eᴮ-pres t a i
unit-ιB-pos₂ (ReaderCWriterMDistr A B monA monB t) tt* i tt* a = tt*
mul-B-shape₁ (ReaderCWriterMDistr A B monA monB t) tt* f g i = (monB · f (monA .ε)) (g (eᴬ-pres t f (~ i)) tt*)
mul-B-shape₂ (ReaderCWriterMDistr A B monA monB t) tt* f g i tt* = tt*
mul-B-pos₁ (ReaderCWriterMDistr A B monA monB t) tt* f g i tt* a = ⊕ᴮ-pres t f (λ x → g x tt*) a i
mul-B-pos₂₁ (ReaderCWriterMDistr A B monA monB t) tt* f g i tt* a = tt*
mul-B-pos₂₂ (ReaderCWriterMDistr A B monA monB t) tt* f g i tt* a = tt*

