module Cubical.Data.Int.MoreInts.DiffInt.Properties where

open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int.MoreInts.DiffInt.Base
open import Cubical.Data.Nat as ℕ renaming (_+_ to _+ℕ_ ; _·_ to _*ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Foundations.Isomorphism

open BinaryRelation

relIsEquiv : isEquivRel rel
relIsEquiv = equivRel {A = ℕ × ℕ} relIsRefl relIsSym relIsTrans
  where
    relIsRefl : isRefl rel
    relIsRefl (a0 , a1) = refl

    relIsSym : isSym rel
    relIsSym (a0 , a1) (b0 , b1) p = sym p

    relIsTrans : isTrans rel
    relIsTrans (a0 , a1) (b0 , b1) (c0 , c1) p0 p1 =
      inj-m+ {m = (b0 +ℕ b1)} ((b0 +ℕ b1) +ℕ (a0 +ℕ c1) ≡⟨ ℕ.+-assoc (b0 +ℕ b1) a0 c1  ⟩
            ((b0 +ℕ b1) +ℕ a0) +ℕ c1 ≡[ i ]⟨ ℕ.+-comm b0 b1 i +ℕ a0   +ℕ c1 ⟩
            ((b1 +ℕ b0) +ℕ a0) +ℕ c1 ≡[ i ]⟨ ℕ.+-comm (b1 +ℕ b0) a0 i +ℕ c1 ⟩
            (a0 +ℕ (b1 +ℕ b0)) +ℕ c1 ≡[ i ]⟨ ℕ.+-assoc a0 b1 b0 i    +ℕ c1 ⟩
            (a0 +ℕ b1) +ℕ b0 +ℕ c1 ≡⟨ sym (ℕ.+-assoc (a0 +ℕ b1) b0 c1) ⟩
            (a0 +ℕ b1) +ℕ (b0 +ℕ c1) ≡⟨ cong (λ p → p . fst +ℕ p .snd) (transport ΣPath≡PathΣ (p0 , p1))⟩
            (b0 +ℕ a1) +ℕ (c0 +ℕ b1) ≡⟨ sym (ℕ.+-assoc b0 a1 (c0 +ℕ b1))⟩
            b0 +ℕ (a1 +ℕ (c0 +ℕ b1)) ≡[ i ]⟨ b0 +ℕ (a1 +ℕ ℕ.+-comm c0 b1 i) ⟩
            b0 +ℕ (a1 +ℕ (b1 +ℕ c0)) ≡[ i ]⟨ b0 +ℕ ℕ.+-comm a1 (b1 +ℕ c0) i ⟩
            b0 +ℕ ((b1 +ℕ c0) +ℕ a1) ≡[ i ]⟨ b0 +ℕ ℕ.+-assoc b1 c0 a1 (~ i) ⟩
            b0 +ℕ (b1 +ℕ (c0 +ℕ a1)) ≡⟨ ℕ.+-assoc b0 b1 (c0 +ℕ a1)⟩
            (b0 +ℕ b1) +ℕ (c0 +ℕ a1) ∎ )

discreteℤ : Discrete ℤ
discreteℤ = discreteSetQuotients relIsEquiv (λ _ _ → discreteℕ _ _)

private
  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 6) ]) ≡ true
  _ = refl

  _ : Dec→Bool (discreteℤ [ (3 , 5) ] [ (4 , 7) ]) ≡ false
  _ = refl

  _+ℕ'_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
  (n₁ , n₂) +ℕ' (m₁ , m₂) = (n₁ +ℕ m₁ , n₂ +ℕ m₂)

  [_-ℕ'_] : ℕ → ℕ → ℤ
  [ x -ℕ' y ] = [ x , y ]

  ℤ-cancelˡ : ∀ {a b} (c : ℕ) → [ (c ℕ.+ a) -ℕ' (c +ℕ b) ] ≡ [ a -ℕ' b ]
  ℤ-cancelˡ {a} {b} c = eq/ _ _ (tmp a b c)
    where tmp : ∀ a b c → rel (c +ℕ a , c +ℕ b) (a , b)
          tmp a b c =
            c +ℕ a +ℕ b
              ≡⟨ cong (λ x → x +ℕ b) (ℕ.+-comm c a) ⟩
            a +ℕ c +ℕ b
              ≡⟨ sym(ℕ.+-assoc a c b) ⟩
            a +ℕ (c +ℕ b) ∎

  ℤ-cancelʳ : ∀ {a b} (c : ℕ) → [ a +ℕ c -ℕ' b +ℕ c ] ≡ [ a -ℕ' b ]
  ℤ-cancelʳ {a} {b} c = eq/ _ _ (tmp a b c)
    where tmp : ∀ a b c → rel (a +ℕ c , b +ℕ c) (a , b)
          tmp a b c =
            a +ℕ c +ℕ b
              ≡⟨ sym(ℕ.+-assoc a c b) ⟩
            a +ℕ (c +ℕ b)
              ≡⟨ cong (λ x → a +ℕ x) (ℕ.+-comm c b) ⟩
            a +ℕ (b +ℕ c) ∎

  -- right congruence
  +-right-congruence : ∀ x y z → rel y z → rel (x +ℕ' y) (x +ℕ' z)
  +-right-congruence x y z  p =
    (fst x +ℕ fst y) +ℕ (snd x +ℕ snd z)
      ≡⟨ cong (λ x' → (fst x +ℕ fst y) +ℕ x') (ℕ.+-comm (snd x) (snd z)) ⟩
    (fst x +ℕ fst y) +ℕ (snd z +ℕ snd x)
      ≡⟨ ℕ.+-assoc (fst x +ℕ fst y) (snd z) (snd x) ⟩
    fst x +ℕ fst y +ℕ snd z +ℕ snd x
      ≡⟨ cong (λ x' → x' +ℕ snd x) (sym (ℕ.+-assoc (fst x) (fst y) (snd z))) ⟩
    fst x +ℕ (fst y +ℕ snd z) +ℕ snd x
      ≡⟨ cong (λ x' → fst x +ℕ x' +ℕ snd x) p ⟩
    fst x +ℕ (fst z +ℕ snd y) +ℕ snd x
      ≡⟨ cong (λ x' → x' +ℕ snd x) (ℕ.+-assoc (fst x) (fst z) (snd y)) ⟩
    fst x +ℕ fst z +ℕ snd y +ℕ snd x
      ≡⟨ sym (ℕ.+-assoc (fst x +ℕ fst z) (snd y) (snd x)) ⟩
    fst x +ℕ fst z +ℕ (snd y +ℕ snd x)
      ≡⟨ cong (λ x' → fst x +ℕ fst z +ℕ x') (ℕ.+-comm (snd y) (snd x)) ⟩
    fst x +ℕ fst z +ℕ (snd x +ℕ snd y) ∎

  +-left-congruence : ∀ x y z → rel x y → rel (x +ℕ' z) (y +ℕ' z)
  +-left-congruence x y z p =
    (fst x +ℕ fst z) +ℕ (snd y +ℕ snd z)
      ≡⟨ cong (λ x' → x' +ℕ (snd y +ℕ snd z)) (ℕ.+-comm (fst x) (fst z)) ⟩
    (fst z +ℕ fst x) +ℕ (snd y +ℕ snd z)
      ≡⟨ ℕ.+-assoc (fst z +ℕ fst x) (snd y) (snd z) ⟩
    fst z +ℕ fst x +ℕ snd y +ℕ snd z
      ≡⟨ cong (λ x' → x' +ℕ snd z) (sym (ℕ.+-assoc (fst z) (fst x) (snd y))) ⟩
    fst z +ℕ (fst x +ℕ snd y) +ℕ snd z
      ≡⟨ cong (λ x' → fst z +ℕ x' +ℕ snd z) p ⟩
    fst z +ℕ (fst y +ℕ snd x) +ℕ snd z
      ≡⟨ cong (λ x' → x' +ℕ snd z) (ℕ.+-assoc (fst z) (fst y) (snd x)) ⟩
    fst z +ℕ fst y +ℕ snd x +ℕ snd z
      ≡⟨ sym (ℕ.+-assoc (fst z +ℕ fst y) (snd x) (snd z)) ⟩
    fst z +ℕ fst y +ℕ (snd x +ℕ snd z)
      ≡⟨ cong (λ x' → x' +ℕ (snd x +ℕ snd z)) (ℕ.+-comm (fst z) (fst y)) ⟩
    fst y +ℕ fst z +ℕ (snd x +ℕ snd z) ∎

ℤ-isSet : isSet ℤ
ℤ-isSet m n p q = squash/ m n p q

_+_ : ℤ → ℤ → ℤ
_+_ = SetQuotients.rec2 ℤ-isSet (λ x y → [ x +ℕ' y ]) feql feqr
    where
      feql : (a b c : ℕ × ℕ) (r : rel a b) → [ a +ℕ' c ] ≡ [ b +ℕ' c ]
      feql a b c r = eq/ (a +ℕ' c) (b +ℕ' c) (+-left-congruence a b c r)
      feqr : (a b c : ℕ × ℕ) (r : rel b c) → [ a +ℕ' b ] ≡ [ a +ℕ' c ]
      feqr a b c r = eq/ (a +ℕ' b) (a +ℕ' c) (+-right-congruence a b c r)

private
  zero-identityˡ-lem : (a : ℕ)(b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → [ a , a ] + b ≡ b
  zero-identityˡ-lem a b ( (c , d) , p ) =
    [ a , a ] + b           ≡⟨ cong (λ x → [ a , a ] + x) (sym p) ⟩
    [ a , a ] + [ c , d ]   ≡⟨ ℤ-cancelˡ a ⟩
    [ c , d ]               ≡⟨ p ⟩
    b ∎

  zero-identityʳ-lem : (a : ℕ)(b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → b + [ a , a ] ≡ b
  zero-identityʳ-lem a b ( (c , d) , p ) =
    b + [ a , a ]           ≡⟨ cong (λ x → x + [ a , a ]) (sym(p)) ⟩
    [ c , d ] + [ a , a ]   ≡⟨ ℤ-cancelʳ a ⟩
    [ c , d ]               ≡⟨ p ⟩
    b ∎

zero-identityˡ : (a : ℕ) (b : ℤ) → [ a , a ] + b ≡ b
zero-identityˡ a b = PropositionalTruncation.rec (lem2 a b) (zero-identityˡ-lem a b) ([]surjective b)
                     where
                       lem2 : (a : ℕ) (b : ℤ) → isProp ([ a , a ] + b ≡ b)
                       lem2 a b = ℤ-isSet ([ a , a ] + b) b

zero-identityʳ : (a : ℕ)(b : ℤ) → b + [ a , a ] ≡ b
zero-identityʳ a b = PropositionalTruncation.rec (lem2 a b) (zero-identityʳ-lem a b) ([]surjective b)
                     where
                       lem2 : (a : ℕ) (b : ℤ) → isProp (b + [ a , a ] ≡ b)
                       lem2 a b = ℤ-isSet (b + [ a , a ]) b

-ℤ_  : ℤ → ℤ
-ℤ [ a ] = [ snd a , fst a ]
-ℤ eq/ a b r i = eq/ (snd a , fst a) (snd b , fst b) (tmp a b r) i
                  where
                    tmp : ∀ a b → fst a +ℕ snd b ≡ fst b +ℕ snd a → snd a +ℕ fst b ≡ snd b +ℕ fst a
                    tmp a b r =
                      snd a +ℕ fst b ≡⟨ ℕ.+-comm (snd a) (fst b) ⟩
                      fst b +ℕ snd a ≡⟨ sym r ⟩
                      fst a +ℕ snd b ≡⟨ ℕ.+-comm (fst a) (snd b) ⟩
                      snd b +ℕ fst a ∎
-ℤ squash/ a a₁ p q i i₁ = squash/ (-ℤ a) (-ℤ a₁) (cong (λ x → -ℤ x) p) (cong (λ x → -ℤ x) q) i i₁

private
  -ℤ-invʳ-lem : (b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → b + (-ℤ b) ≡ [ 0 , 0 ]
  -ℤ-invʳ-lem b ( (c , d) , p ) =
    b + (-ℤ b)
      ≡⟨ cong (λ x → x + (-ℤ b)) (sym p) ⟩
    [ c , d ] + (-ℤ b)
      ≡⟨ cong (λ x → [ c , d ] + (-ℤ x)) (sym p) ⟩
    [ c +ℕ d , d +ℕ c ]
      ≡⟨ cong (λ x → [ c +ℕ d , x ]) (ℕ.+-comm d c) ⟩
    [ c +ℕ d , c +ℕ d ]
      ≡⟨ ℤ-cancelˡ c ⟩
    [ d -ℕ' d ]
      ≡⟨ sym(ℤ-cancelʳ 0) ⟩
    [ d +ℕ 0 -ℕ' d +ℕ 0 ]
      ≡⟨ ℤ-cancelˡ d ⟩
    [ 0 , 0 ] ∎

  -ℤ-invˡ-lem : (b : ℤ) → (Σ (ℕ × ℕ) ( λ (c , d) → [ (c , d) ]  ≡ b )) → (-ℤ b) + b ≡ [ 0 , 0 ]
  -ℤ-invˡ-lem b ( (c , d) , p ) =
    (-ℤ b) + b
      ≡⟨ cong (λ x → (-ℤ b) + x) (sym p) ⟩
    (-ℤ b) + [ c , d ]
      ≡⟨ cong (λ x → (-ℤ x) + [ c , d ]) (sym p) ⟩
    [ d +ℕ c , c +ℕ d ]
      ≡⟨ cong (λ x → [ x , c +ℕ d ]) (ℕ.+-comm d c) ⟩
    [ c +ℕ d , c +ℕ d ]
      ≡⟨ ℤ-cancelˡ c ⟩
    [ d -ℕ' d ]
      ≡⟨ sym(ℤ-cancelʳ 0) ⟩
    [ d +ℕ 0 -ℕ' d +ℕ 0 ]
      ≡⟨ ℤ-cancelˡ d ⟩
    [ 0 , 0 ] ∎

_-_ : ℤ → ℤ → ℤ
a - b = a + (-ℤ b)

-ℤ-invʳ : (b : ℤ) → b + (-ℤ b) ≡ [ 0 , 0 ]
-ℤ-invʳ b = PropositionalTruncation.rec (lem2 b) (-ℤ-invʳ-lem b) ([]surjective b)
             where
               lem2 : (b : ℤ) → isProp (b + (-ℤ b) ≡ [ 0 , 0 ])
               lem2 b = ℤ-isSet (b + (-ℤ b)) [ 0 , 0 ]

-ℤ-invˡ : (b : ℤ) → (-ℤ b) + b ≡ [ 0 , 0 ]
-ℤ-invˡ b = PropositionalTruncation.rec (lem2 b) (-ℤ-invˡ-lem b) ([]surjective b)
             where
               lem2 : (b : ℤ) → isProp ((-ℤ b) + b ≡ [ 0 , 0 ])
               lem2 b = ℤ-isSet ((-ℤ b) + b) [ 0 , 0 ]

+ℤ-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+ℤ-assoc = elimProp3 (λ _ _ _ → ℤ-isSet _ _)
    (λ { (a , b) (c , d) (e , f) i → [ ℕ.+-assoc a c e i -ℕ' ℕ.+-assoc b d f i ] })

+ℤ-comm : ∀ x y → x + y ≡ y + x
+ℤ-comm = elimProp2 (λ _ _ → ℤ-isSet _ _)
         λ ( a , b ) ( c , d ) i → [ ℕ.+-comm a c i -ℕ'  ℕ.+-comm b d i ]
