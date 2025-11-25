module Cubical.Data.Sequence.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Sequence
open SequenceMap renaming (map to smap)
open isHAEquiv

-- Identity map of sequences
idSequenceMap : (C : Sequence ℓ) → SequenceMap C C
smap (idSequenceMap C) n x = x
comm (idSequenceMap C) n x = refl

-- Composition of maps
composeSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'} {E : Sequence ℓ''}
  (g : SequenceMap D E) (f : SequenceMap C D) → SequenceMap C E
composeSequenceMap g f .smap n x = g .smap n (f .smap n x)
composeSequenceMap g f .comm n x =
    g .comm n _
  ∙ cong (g .smap (suc n)) (f .comm n x)

-- Composition of isos
compSequenceIso : {A : Sequence ℓ} {B : Sequence ℓ'} {C : Sequence ℓ''}
  → SequenceIso A B → SequenceIso B C → SequenceIso A C
fst (compSequenceIso e g) n = compIso (fst e n) (fst g n)
snd (compSequenceIso e g) n a =
  snd g n _ ∙ cong (Iso.fun (fst g (suc n))) (snd e n a)

-- Identity equivalence
idSequenceEquiv : (A : Sequence ℓ) → SequenceEquiv A A
fst (idSequenceEquiv A) = idSequenceMap A
snd (idSequenceEquiv A) _ = idIsEquiv _

-- inversion of equivalences
invSequenceEquiv : {A : Sequence ℓ} {B : Sequence ℓ'}
  → SequenceEquiv A B → SequenceEquiv B A
smap (fst (invSequenceEquiv eqs)) n = invEq (_ , snd eqs n)
comm (fst (invSequenceEquiv {A = A} {B} eqs)) n x =
    sym (retEq (_ , snd eqs (suc n)) (map A (invEq (_  , snd eqs n) x)))
  ∙∙ cong (invEq (_ , snd eqs (suc n))) (sym (comm (fst eqs) n (invEq (_ , snd eqs n) x)))
  ∙∙ cong (invEq (_ , snd eqs (suc n)) ∘ map B) (secEq (_ , snd eqs n) x)
snd (invSequenceEquiv eqs) n = invEquiv (_ , snd eqs n) .snd

-- inversion of the identity
invIdSequenceEquiv : {A : Sequence ℓ}
  → invSequenceEquiv (idSequenceEquiv A) ≡ idSequenceEquiv A
invIdSequenceEquiv {A = A} =
  Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsEquiv _)) main
  where
  main : invSequenceEquiv (idSequenceEquiv A) .fst ≡ idSequenceMap A
  smap (main i) n z = z
  comm (main i) n x j = rUnit (λ _ → map A x) (~ i) j

-- ua for sequences
uaSequence : {A B : Sequence ℓ} → SequenceEquiv A B → A ≡ B
obj (uaSequence {A = A} {B} (e , eqv) i) n = ua (_ , eqv n) i
map (uaSequence {A = A} {B} (e , eqv) i) {n = n} a =
  hcomp (λ k → λ {(i = i0) → map A (retEq (_ , eqv n) a k)
                 ; (i = i1) → (sym (comm e n (invEq (_ , eqv n) a))
                              ∙ cong (map B) (secEq (_ , eqv n) a)) k})
        (ua-gluePt (_ , eqv (suc n)) i
          (map A (invEq (_ , eqv n) (ua-unglue (_ , eqv n) i a))))

uaSequenceIdEquiv : ∀ {ℓ} {A : Sequence ℓ}
  → uaSequence (idSequenceEquiv A) ≡ refl
obj (uaSequenceIdEquiv {A = A} i j) n =
  uaIdEquiv {A = obj A n} i j
map (uaSequenceIdEquiv {A = A} i j) {n = n} x =
  hcomp (λ k → λ {(i = i1) → map A x
                 ; (j = i0) → map A x
                 ; (j = i1) → rUnit (refl {x = map A x}) (~ i) k})
   (glue {φ = j ∨ ~ j ∨ i}
      (λ { (j = i0) → map A x
         ; (j = i1) → map A x
         ; (i = i1) → map A x})
      (map A (unglue (j ∨ ~ j ∨ i) x)))

halfAdjointSequenceEquiv : {A : Sequence ℓ} {B : Sequence ℓ'}
  → SequenceEquiv A B → SequenceEquiv A B
fst (halfAdjointSequenceEquiv (e , eqv)) = e
snd (halfAdjointSequenceEquiv (e , eqv)) n =
  isHAEquiv→isEquiv (equiv→HAEquiv (_ , eqv n) .snd)

-- Contractibility of total space of (SequenceEquiv A)
isContrTotalSequence : (A : Sequence ℓ)
  → isContr (Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B)
fst (isContrTotalSequence A) = A , idSequenceEquiv A
snd (isContrTotalSequence A) (B , eqv*) =
  ΣPathP (uaSequence eqv , main)
  where
  eqv = halfAdjointSequenceEquiv eqv*

  eqv⁻ : {n : ℕ} → obj B n → obj A n
  eqv⁻ {n = n} = invEq (_ , snd eqv n)

  haEqv : (n : ℕ) → HAEquiv (obj A n) (obj B n)
  haEqv n = equiv→HAEquiv (_ , eqv* .snd n)


  help : (n : ℕ) (x : obj A n)
    → Square (cong (smap (fst eqv) (suc n) ∘ map A)
                    (retEq (_ , snd eqv n) x))
              (comm (fst eqv) n x)
              (sym (comm (fst eqv) n
                (eqv⁻ (smap (fst eqv) n x)))
              ∙ cong (map B) (secEq (smap (fst eqv) n , snd eqv n)
                         (smap (fst eqv) n x)))
              refl
  help n x = flipSquare ((compPath≡compPath' _ _
    ∙ cong₂ _∙'_ refl λ j i
      → map B (com
                (equiv→HAEquiv (_ , eqv* .snd n) .snd) x (~ j) i))
    ◁ λ i j →
    hcomp (λ k →
      λ {(j = i0) → comm (fst eqv) n
                      (lUnit (cong fst
                        (eqv* .snd n .equiv-proof (smap (fst eqv*) n x)
                       .snd (x , refl))) k i) k
       ; (j = i1) → comm (fst eqv) n x (i ∧ k)
       ; (i = i0) → compPath'-filler
                       (sym (comm (fst eqv) n (eqv⁻ (smap (fst eqv) n x))))
                       (cong (map B) (com (haEqv n .snd) x i0)) k j
       ; (i = i1) → comm (fst eqv) n x k
       })
          (map B (smap (fst eqv*) n
            ((cong fst (eqv* .snd n .equiv-proof (smap (fst eqv*) n x)
              .snd (x , (λ _ → smap (fst eqv*) n x)))) (i ∨ j)))))

  main : PathP (λ i → SequenceEquiv A (uaSequence eqv i))
      (idSequenceEquiv A) eqv*
  smap (fst (main i)) n x = ua-gluePt (_ , snd eqv n) i x
  comm (fst (main i)) n x j =
    hcomp (λ k → λ {(i = i0) → map A
                                  (retEq (_ , snd eqv n) x (k ∨ j))
                   ; (i = i1) → help n x k j
                   ; (j = i1) → ua-gluePt (_ , snd eqv (suc n)) i (map A x)})
          (ua-gluePt (_ , snd eqv (suc n)) i
                     (map A (retEq (_ , snd eqv n) x j)))
  snd (main i) n =
    isProp→PathP {B = λ i → isEquiv  (λ x → ua-gluePt (_ , snd eqv n) i x)}
     (λ i → isPropIsEquiv _)
     (idIsEquiv (obj A n)) (snd eqv* n) i


-- J for sequences
SequenceEquivJ : {A : Sequence ℓ}
  (P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ')
  → P A (idSequenceEquiv A)
  → (B : _) (e : _) → P B e
SequenceEquivJ {ℓ = ℓ} {A = A} P ind B e = main (B , e)
  where
  P' : Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B → Type _
  P' (B , e) = P B e

  main : (x : _) → P' x
  main (B , e) = subst P' (isContrTotalSequence A .snd (B , e)) ind

SequenceEquivJ>_ : {A : Sequence ℓ}
  {P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ'}
  → P A (idSequenceEquiv A)
  → (B : _) (e : _) → P B e
SequenceEquivJ>_ {P = P} hyp B e = SequenceEquivJ P hyp B e

SequenceEquivJRefl : ∀ {ℓ ℓ'} {A : Sequence ℓ}
  (P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ')
    (id : P A (idSequenceEquiv A))
  → SequenceEquivJ P id A (idSequenceEquiv A) ≡ id
SequenceEquivJRefl {ℓ = ℓ} {A = A} P ids =
  (λ j → subst P' (isProp→isSet (isContr→isProp (isContrTotalSequence A))
                    _ _ (isContrTotalSequence A .snd
                          (A , idSequenceEquiv A)) refl j) ids)
  ∙ transportRefl ids
  where
  P' : Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B → Type _
  P' (B , e) = P B e
