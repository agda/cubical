{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Int as ℤ using (ℤ; pos·pos; pos0+)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
import Cubical.Data.Bool as 𝟚

open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Base

open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime

∼→sign≡sign : ∀ a a' b b' → (a , b) ∼ (a' , b') → ℤ.sign a ≡ ℤ.sign a'
∼→sign≡sign (ℤ.pos zero) (ℤ.pos zero) (1+ n) (1+ n₁) x = refl
∼→sign≡sign (ℤ.pos zero) (ℤ.pos (suc n₃)) (1+ n) (1+ n₁) x =
  ⊥.rec $ ℕ.znots $
     ℤ.injPos (x ∙ sym (ℤ.pos·pos (suc n₃) (suc n)))
∼→sign≡sign (ℤ.pos (suc n₂)) (ℤ.pos zero) (1+ n) (1+ n₁) x =
 ⊥.rec $ ℕ.znots $
     ℤ.injPos (sym x ∙ sym (ℤ.pos·pos (suc n₂) (suc n₁)))
∼→sign≡sign (ℤ.pos (suc n₂)) (ℤ.pos (suc n₃)) (1+ n) (1+ n₁) x = refl
∼→sign≡sign (ℤ.pos zero) (ℤ.negsuc n₃) (1+ n) (1+ n₁) x =
 ⊥.rec $ ℕ.znots $ ℤ.injPos $ cong ℤ.-_ (x ∙ ℤ.negsuc·pos n₃ (ℕ₊₁→ℕ (1+ n)))
   ∙ ℤ.-Involutive _ ∙ sym (ℤ.pos·pos (suc n₃) (ℕ₊₁→ℕ (1+ n)))
∼→sign≡sign (ℤ.pos (suc n₂)) (ℤ.negsuc n₃) (1+ n) (1+ n₁) x =
 ⊥.rec (ℤ.posNotnegsuc _ _ (ℤ.pos·pos (suc n₂) (ℕ₊₁→ℕ (1+ n₁))
  ∙∙ x ∙∙
   (ℤ.negsuc·pos n₃ (ℕ₊₁→ℕ (1+ n)) ∙ cong ℤ.-_ (sym (ℤ.pos·pos (suc n₃) (ℕ₊₁→ℕ (1+ n)))))))
∼→sign≡sign (ℤ.negsuc n₂) (ℤ.pos zero) (1+ n) (1+ n₁) x =
  ⊥.rec $ ℕ.snotz $ ℤ.injPos $
     (ℤ.pos·pos (suc n₂) (ℕ₊₁→ℕ (1+ n₁))) ∙∙
      sym (ℤ.-Involutive _) ∙∙ cong ℤ.-_ (sym (ℤ.negsuc·pos n₂ (ℕ₊₁→ℕ (1+ n₁))) ∙ x)
∼→sign≡sign (ℤ.negsuc n₂) (ℤ.pos (suc n₃)) (1+ n) (1+ n₁) x =
  ⊥.rec (ℤ.negsucNotpos _ _
     ((cong ℤ.-_ (ℤ.pos·pos (suc n₂) (ℕ₊₁→ℕ (1+ n₁)))
      ∙ sym (ℤ.negsuc·pos n₂ (ℕ₊₁→ℕ (1+ n₁))))
      ∙∙ x ∙∙ sym (ℤ.pos·pos (suc n₃) (ℕ₊₁→ℕ (1+ n)))))
∼→sign≡sign (ℤ.negsuc n₂) (ℤ.negsuc n₃) (1+ n) (1+ n₁) x = refl


·CancelL : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a / c ·₊₁ b ] ≡ [ a / b ]
·CancelL {a} {b} c = eq/ _ _
  ((ℕ₊₁→ℤ c ℤ.· a)   ℤ.· ℕ₊₁→ℤ b  ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.·Comm (ℕ₊₁→ℤ c) a) ⟩
   (a ℤ.· (ℕ₊₁→ℤ c)) ℤ.· ℕ₊₁→ℤ b  ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
    a ℤ.· (ℕ₊₁→ℤ c   ℤ.· ℕ₊₁→ℤ b) ≡⟨ cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ c) (ℕ₊₁→ℕ b))) ⟩
    a ℤ.·  ℕ₊₁→ℤ (c ·₊₁ b)         ∎)

·CancelR : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c / b ·₊₁ c ] ≡ [ a / b ]
·CancelR {a} {b} c = eq/ _ _
  (a ℤ.·  ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b   ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b)  ≡⟨ cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ c)  ≡⟨ cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ c))) ⟩
   a ℤ.· ℕ₊₁→ℤ (b ·₊₁ c) ∎)

reduced : (x : ℚ) → Σ[ (p , q) ∈ (ℤ × ℕ₊₁) ] (areCoprime (ℤ.abs p , ℕ₊₁→ℕ q) × ([ p / q ] ≡ x))
reduced = SetQuotient.Elim.go w
 where

 module cop a b where
  open ToCoprime (ℤ.abs a , b) renaming (toCoprimeAreCoprime to tcac) public


  e : ℤ.sign a ℤ.· ℤ.pos c₁ ℤ.· ℕ₊₁→ℤ b ≡ a ℤ.· ℕ₊₁→ℤ c₂
  e =     (sym (ℤ.·Assoc (ℤ.sign a) _ _)
           ∙ cong (ℤ.sign a ℤ.·_)
              (     cong (ℤ.pos c₁ ℤ.·_)
                   (cong ℤ.pos (sym p₂ ∙ ℕ.·-comm _ d ) ∙ ℤ.pos·pos d _)
                 ∙∙ ℤ.·Assoc (ℤ.pos c₁) _ _
                 ∙∙ cong (λ p → p ℤ.· ℕ₊₁→ℤ c₂ )
                     (sym (ℤ.pos·pos c₁ d) ∙ cong ℤ.pos p₁)) )
       ∙∙ ℤ.·Assoc (ℤ.sign a) _ _
       ∙∙ cong (ℤ._· ℕ₊₁→ℤ c₂) (ℤ.sign·abs a)
  p' : ∀ a c₁ → (c₁ ℕ.· suc d-1 ≡ ℤ.abs a) → c₁ ≡ ℤ.abs (ℤ.sign a ℤ.· ℤ.pos c₁)
  p' (ℤ.pos zero) zero x = refl
  p' (ℤ.pos zero) (suc c₃) x = ⊥.rec (ℕ.snotz x)
  p' (ℤ.pos (suc n)) _ x = refl
  p' (ℤ.negsuc n) zero x = refl
  p' (ℤ.negsuc n) (suc c₃) x = refl

  r = (ℤ.sign a ℤ.· ℤ.pos c₁ , c₂) , subst areCoprime (cong (_, (ℕ₊₁→ℕ c₂))
         (p' a _ (cong (c₁ ℕ.·_) (sym q) ∙ p₁))) tcac , eq/ _ _ e



 w : SetQuotient.Elim _
 w .SetQuotient.Elim.isSetB _ =
  isSetΣ (isSet× ℤ.isSetℤ (subst isSet 1+Path ℕ.isSetℕ))
    (isProp→isSet ∘ λ _ → isProp× isPropIsGCD (isSetℚ _ _))

 w .SetQuotient.Elim.f (a , b) = cop.r  a b

 w .SetQuotient.Elim.f∼ (a , b) (a' , b') r =
   ΣPathPProp
            (λ _ → isProp× isPropIsGCD (isSetℚ _ _))
     (cong (map-fst ((ℤ.sign a ℤ.·_) ∘ ℤ.pos)) (sym (toCoprime-cancelʳ (ℤ.abs a , b) b')) ∙∙
       cong₂ {x = ℤ.sign a} {y = ℤ.sign a'}
        (λ sa → (map-fst ((sa ℤ.·_) ∘ ℤ.pos) ∘ toCoprime))
        (∼→sign≡sign a a' b b' r)
        (ΣPathP (sym (ℤ.abs· a _) ∙∙ cong ℤ.abs r ∙∙ ℤ.abs· a' _ , ·₊₁-comm b b'))
      ∙∙ cong (map-fst ((ℤ.sign a' ℤ.·_) ∘ ℤ.pos)) (toCoprime-cancelʳ (ℤ.abs a' , b') b) )

-- useful functions for defining operations on ℚ

reduce : ℚ → ℚ
reduce = [_] ∘ fst ∘  reduced

record OnCommonDenom : Type where
 no-eta-equality
 field
  g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f))
  g-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
           → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d

 eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → [ g (a , b) (e , f) / b ·₊₁ f ] ≡ [ g (c , d) (e , f) / d ·₊₁ f ]
 eql (a , b) (c , d) (e , f) p =
   [ g (a , b) (e , f) / b ·₊₁ f ]
     ≡⟨ sym (·CancelL d) ⟩
   [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / d ·₊₁ (b ·₊₁ f) ]
     ≡[ i ]⟨ [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / ·₊₁-assoc d b f i ] ⟩
   [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / (d ·₊₁ b) ·₊₁ f ]
     ≡[ i ]⟨ [ g-eql (a , b) (c , d) (e , f) p i / ·₊₁-comm d b i ·₊₁ f ] ⟩
   [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / (b ·₊₁ d) ·₊₁ f ]
     ≡[ i ]⟨ [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / ·₊₁-assoc b d f (~ i) ] ⟩
   [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / b ·₊₁ (d ·₊₁ f) ]
     ≡⟨ ·CancelL b ⟩
   [ g (c , d) (e , f) / d ·₊₁ f ] ∎
 eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
      → [ g (a , b) (c , d) / b ·₊₁ d ] ≡ [ g (a , b) (e , f) / b ·₊₁ f ]
 eqr (a , b) (c , d) (e , f) p =
   [ g (a , b) (c , d) / b ·₊₁ d ]
     ≡⟨ sym (·CancelR f) ⟩
   [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / (b ·₊₁ d) ·₊₁ f ]
     ≡[ i ]⟨ [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / ·₊₁-assoc b d f (~ i) ] ⟩
   [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / b ·₊₁ (d ·₊₁ f) ]
     ≡[ i ]⟨ [ g-eqr (a , b) (c , d) (e , f) p i / b ·₊₁ ·₊₁-comm d f i ] ⟩
   [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / b ·₊₁ (f ·₊₁ d) ]
     ≡[ i ]⟨ [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / ·₊₁-assoc b f d i ] ⟩
   [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / (b ·₊₁ f) ·₊₁ d ]
     ≡⟨ ·CancelR d ⟩
   [ g (a , b) (e , f) / b ·₊₁ f ] ∎


 go : ℚ → ℚ → ℚ
 go = SetQuotient.Rec2.go w
  where
  w : SetQuotient.Rec2 ℚ
  w .SetQuotient.Rec2.isSetB = isSetℚ
  w .SetQuotient.Rec2.f (a , b) (c , d) = [ g (a , b) (c , d) / b ·₊₁ d ]
  w .SetQuotient.Rec2.f∼ (a , b) (c , d) (e , f) p = eqr (a , b) (c , d) (e , f) p
  w .SetQuotient.Rec2.∼f (a , b) (c , d) (e , f) p = eql (a , b) (c , d) (e , f) p

record OnCommonDenomSym : Type where
 no-eta-equality
 field
  g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  g-sym : ∀ x y → g x y ≡ g y x
  g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f))

 q-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
                 → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d
 q-eqr (a , b) (c , d) (e , f) p =
           (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡[ i ]⟨ ℤ.·Comm (g-sym (a , b) (c , d) i) (ℕ₊₁→ℤ f) i ⟩
           ℕ₊₁→ℤ f ℤ.· (g (c , d) (a , b)) ≡⟨ g-eql (c , d) (e , f) (a , b) p ⟩
           ℕ₊₁→ℤ d ℤ.· (g (e , f) (a , b)) ≡[ i ]⟨ ℤ.·Comm (ℕ₊₁→ℤ d) (g-sym (e , f) (a , b) i) i ⟩
           (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d ∎

 go : ℚ → ℚ → ℚ
 go = OnCommonDenom.go w
  where
  w : OnCommonDenom
  w .OnCommonDenom.g = g
  w .OnCommonDenom.g-eql = g-eql
  w .OnCommonDenom.g-eqr = q-eqr

 go-comm : ∀ x y → go x y ≡ go y x
 go-comm = SetQuotient.ElimProp2.go w
  where
  w : SetQuotient.ElimProp2 (λ z z₁ → go z z₁ ≡ go z₁ z)
  w .SetQuotient.ElimProp2.isPropB _ _ = isSetℚ _ _
  w .SetQuotient.ElimProp2.f (a , b) (c , d) i = [ g-sym (a , b) (c , d) i / ·₊₁-comm b d i ]


-- basic arithmetic operations on ℚ

infixl 6 _+_
infixl 7 _·_
infix  8 -_

private abstract
  lem₁ : ∀ a b c d e (p : a ℤ.· b ≡ c ℤ.· d) → b ℤ.· (a ℤ.· e) ≡ d ℤ.· (c ℤ.· e)
  lem₁ a b c d e p =   ℤ.·Assoc b a e
                     ∙ cong (ℤ._· e) (ℤ.·Comm b a ∙ p ∙ ℤ.·Comm c d)
                     ∙ sym (ℤ.·Assoc d c e)

  lem₂ : ∀ a b c → a ℤ.· (b ℤ.· c) ≡ c ℤ.· (b ℤ.· a)
  lem₂ a b c =   cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b
               ∙ cong (ℤ._· b) (ℤ.·Comm a c) ∙ sym (ℤ.·Assoc c a b)
               ∙ cong (c ℤ.·_) (ℤ.·Comm a b)

minR : OnCommonDenomSym
minR .OnCommonDenomSym.g (a , b) (c , d) = ℤ.min (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
minR .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.minComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
minR .OnCommonDenomSym.g-eql = eq

  where abstract

    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMin (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.min (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.min (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMin (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

min = OnCommonDenomSym.go minR

maxR : OnCommonDenomSym
maxR .OnCommonDenomSym.g (a , b) (c , d) = ℤ.max (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
maxR .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.maxComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
maxR .OnCommonDenomSym.g-eql = eq


  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMax (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.max (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.max (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMax (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

max = OnCommonDenomSym.go maxR


minComm : ∀ x y → min x y ≡ min y x
minComm = OnCommonDenomSym.go-comm minR

maxComm : ∀ x y → max x y ≡ max y x
maxComm = OnCommonDenomSym.go-comm maxR

minIdem : ∀ x → min x x ≡ x
minIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.minIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

maxIdem : ∀ x → max x x ≡ x
maxIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.maxIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

minAssoc : ∀ x y z → min x (min y z) ≡ min (min x y) z
minAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.min
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMin (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.min (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.minAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.min x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

maxAssoc : ∀ x y z → max x (max y z) ≡ max (max x y) z
maxAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.max
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMax (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.max (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.maxAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.max x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

minAbsorbLMax : ∀ x y → min x (max x y) ≡ x
minAbsorbLMax = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b) ,
           b ·₊₁ (b ·₊₁ d))
          (a , b)
          (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                         ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                (ℤ.max x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                 ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.minAbsorbLMax (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
                 ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                    cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                                   cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

maxAbsorbLMin : ∀ x y → max x (min x y) ≡ x
maxAbsorbLMin = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b) ,
                  b ·₊₁ (b ·₊₁ d))
                 (a , b)
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                             (ℤ.min x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                       ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.maxAbsorbLMin (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
             ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                               cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

+Rec : OnCommonDenomSym
+Rec .OnCommonDenomSym.g (a , b) (c , d) = a ℤ.· (ℕ₊₁→ℤ d) ℤ.+ c ℤ.· (ℕ₊₁→ℤ b)
+Rec .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.+Comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b))
+Rec .OnCommonDenomSym.g-eql = eq
  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
        ≡⟨ ℤ.·DistR+ (ℕ₊₁→ℤ d) (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b)
        ≡[ i ]⟨ lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) p i ℤ.+ lem₂ (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b) i ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d)
        ≡⟨ sym (ℤ.·DistR+ (ℕ₊₁→ℤ b) (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ∎


_+_ : ℚ → ℚ → ℚ
_+_ = OnCommonDenomSym.go +Rec

+Comm : ∀ x y → x + y ≡ y + x
+Comm = OnCommonDenomSym.go-comm +Rec

+IdL : ∀ x → 0 + x ≡ x
+IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) i → [ ((cong (ℤ._+ a ℤ.· ℕ₊₁→ℤ 1) (ℤ.·AnnihilL (ℕ₊₁→ℤ b))
                    ∙ sym (pos0+ (a ℤ.· ℕ₊₁→ℤ 1)))
                    ∙ ℤ.·IdR a) i / ·₊₁-identityˡ b i ] }

+IdR : ∀ x → x + 0 ≡ x
+IdR x = +Comm x _ ∙ +IdL x

+Assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i
    → [ (cong (λ x → a ℤ.· x ℤ.+ (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ℤ.· ℕ₊₁→ℤ b)
              (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
       ∙ eq a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ f)
       ∙ cong (λ x → (a ℤ.· ℕ₊₁→ℤ d ℤ.+ c ℤ.· ℕ₊₁→ℤ b) ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· x)
              (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))) i / ·₊₁-assoc b d f i ] })
  where eq₁ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ a ℤ.· (c ℤ.· b)
        eq₁ a b c = sym (ℤ.·Assoc a b c) ∙ cong (a ℤ.·_) (ℤ.·Comm b c)
        eq₂ : ∀ a b c → (a ℤ.· b) ℤ.· c ≡ (a ℤ.· c) ℤ.· b
        eq₂ a b c = eq₁ a b c ∙ ℤ.·Assoc a c b

        eq : ∀ a b c d e f → Path ℤ _ _
        eq a b c d e f =
          a ℤ.· (d ℤ.· f) ℤ.+ (c ℤ.· f ℤ.+ e ℤ.· d) ℤ.· b
            ≡[ i ]⟨ a ℤ.· (d ℤ.· f) ℤ.+ ℤ.·DistL+ (c ℤ.· f) (e ℤ.· d) b i ⟩
          a ℤ.· (d ℤ.· f) ℤ.+ ((c ℤ.· f) ℤ.· b ℤ.+ (e ℤ.· d) ℤ.· b)
            ≡[ i ]⟨ ℤ.+Assoc (ℤ.·Assoc a d f i) (eq₂ c f b i) (eq₁ e d b i) i ⟩
          ((a ℤ.· d) ℤ.· f ℤ.+ (c ℤ.· b) ℤ.· f) ℤ.+ e ℤ.· (b ℤ.· d)
            ≡[ i ]⟨ ℤ.·DistL+ (a ℤ.· d) (c ℤ.· b) f (~ i) ℤ.+ e ℤ.· (b ℤ.· d) ⟩
          (a ℤ.· d ℤ.+ c ℤ.· b) ℤ.· f ℤ.+ e ℤ.· (b ℤ.· d) ∎

·Rec : OnCommonDenomSym
·Rec .OnCommonDenomSym.g (a , _) (c , _) = a ℤ.· c
·Rec .OnCommonDenomSym.g-sym (a , _) (c , _) = ℤ.·Comm a c
·Rec .OnCommonDenomSym.g-eql (a , b) (c , d) (e , _) p = lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) e p

_·_ : ℚ → ℚ → ℚ
_·_ = OnCommonDenomSym.go ·Rec

·Comm : ∀ x y → x · y ≡ y · x
·Comm = OnCommonDenomSym.go-comm ·Rec

·IdL : ∀ x → 1 · x ≡ x
·IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·IdL a i / ·₊₁-identityˡ b i ] })

·IdR : ∀ x → x · 1 ≡ x
·IdR = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) i → [ ℤ.·IdR a i / ·₊₁-identityʳ b i ] })

·AnnihilL : ∀ x → 0 · x ≡ 0
·AnnihilL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / 1 ·₊₁ b ]) ∙ ·CancelR b })
  where p : ∀ a b → 0 ℤ.· a ≡ 0 ℤ.· ℕ₊₁→ℤ b
        p a b = ℤ.·AnnihilL a ∙ sym (ℤ.·AnnihilL (ℕ₊₁→ℤ b))

·AnnihilR : ∀ x → x · 0 ≡ 0
·AnnihilR = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  (λ { (a , b) → (λ i → [ p a b i / b ·₊₁ 1 ]) ∙ ·CancelL b })
  where p : ∀ a b → a ℤ.· 0 ≡ ℕ₊₁→ℤ b ℤ.· 0
        p a b = ℤ.·AnnihilR a ∙ sym (ℤ.·AnnihilR (ℕ₊₁→ℤ b))

·Assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) i → [ ℤ.·Assoc a c e i / ·₊₁-assoc b d f i ] })

·DistL+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
·DistL+ = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  (λ { (a , b) (c , d) (e , f) → sym (eq a b c d e f)})
  where lem : ∀ {ℓ} {A : Type ℓ} (_·_ : A → A → A)
                (·-comm : ∀ x y → x · y ≡ y · x)
                (·-assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z)
                a c b d
              → (a · c) · (b · d) ≡ (a · (c · d)) · b
        lem _·_ ·-comm ·-assoc a c b d =
          (a · c) · (b · d) ≡[ i ]⟨ (a · c) · ·-comm b d i ⟩
          (a · c) · (d · b) ≡⟨ ·-assoc (a · c) d b ⟩
          ((a · c) · d) · b ≡[ i ]⟨ ·-assoc a c d (~ i) · b ⟩
          (a · (c · d)) · b ∎

        lemℤ   = lem ℤ._·_ ℤ.·Comm ℤ.·Assoc
        lemℕ₊₁ = lem _·₊₁_ ·₊₁-comm ·₊₁-assoc

        eq : ∀ a b c d e f →
               [ (a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b ·₊₁ f) ℤ.+ (a ℤ.· e) ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)
                 / (b ·₊₁ d) ·₊₁ (b ·₊₁ f) ]
             ≡ [ a ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
                / b ·₊₁ (d ·₊₁ f) ]
        eq a b c d e f =
          (λ i → [ (cong (a ℤ.· c ℤ.·_) (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))
                 ∙ (lemℤ a c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) i
                   ℤ.+
                   (cong (a ℤ.· e ℤ.·_) (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d))
                 ∙ (lemℤ a e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d))) i
                   / lemℕ₊₁ b d b f i ]) ∙
          (λ i → [ (sym (ℤ.·DistL+ (a ℤ.· (c ℤ.· ℕ₊₁→ℤ f)) (a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)) (ℕ₊₁→ℤ b))) i
                   / (b ·₊₁ (d ·₊₁ f)) ·₊₁ b ]) ∙
          ·CancelR {a ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)} {b ·₊₁ (d ·₊₁ f)} b ∙
          (λ i → [ (sym (ℤ.·DistR+ a (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d))) i
                   / b ·₊₁ (d ·₊₁ f) ])

·DistR+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
·DistR+ x y z = sym ((λ i → ·Comm x z i + ·Comm y z i) ∙ (sym (·DistL+ z x y)) ∙ ·Comm z (x + y))


[/]≡· : ∀ n m → [ n / m ] ≡ [ n / 1 ] · [ 1 / m ]
[/]≡· n m = cong₂ [_/_] (sym (ℤ.·IdR n)) (sym (·₊₁-identityˡ _))

[1/n]·[1/m]≡[1/n·m] : ∀ n m → [ 1 / n ] · [ 1 / m ] ≡ [ 1 / n ·₊₁ m ]
[1/n]·[1/m]≡[1/n·m] n m = eq/ _ _ refl


[n/n]≡[m/m] : ∀ n m → [ ℤ.pos (suc n) / 1+ n ] ≡ [ ℤ.pos (suc m) / 1+ m ]
[n/n]≡[m/m] n m = eq/ _ _ (ℤ.·Comm (ℤ.pos (suc n)) (ℤ.pos (suc m)))

[0/n]≡[0/m] : ∀ n m → [ ℤ.pos zero / 1+ n ] ≡ [ ℤ.pos zero / 1+ m ]
[0/n]≡[0/m] n m = eq/ _ _ refl


-_ : ℚ → ℚ
- x = -1 · x

-[/] : ∀ n m → [ ℤ.negsuc m / n ] ≡ - [ ℤ.pos (suc m) / n ]
-[/] n m = cong [ ℤ.negsuc m /_] (sym (·₊₁-identityˡ _))


-Invol : ∀ x → - - x ≡ x
-Invol x = ·Assoc -1 -1 x ∙ ·IdL x

-Distr : ∀ x y → - (x + y) ≡ - x + - y
-Distr = ·DistL+ -1

negateEquiv : ℚ ≃ ℚ
negateEquiv = isoToEquiv (iso -_ -_ -Invol -Invol)

negateEq : ℚ ≡ ℚ
negateEq = ua negateEquiv

+InvL : ∀ x → (- x) + x ≡ 0
+InvL x = (λ i → (-1 · x) + ·IdL x (~ i)) ∙ (sym (·DistR+ -1 1 x)) ∙ ·AnnihilL x

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)


-·- : ∀ x y → (- x) · (- y) ≡ x · y
-·- x y = cong (_· (- y)) (·Comm -1 x)
            ∙∙ sym (·Assoc x (- 1) _)
            ∙∙ cong (x ·_) (-Invol y)

-[x-y]≡y-x : ∀ x y → - ( x - y ) ≡ y - x
-[x-y]≡y-x x y = -Distr x (- y) ∙ λ i → +Comm (- x) (-Invol y i) i

-Distr' : ∀ x y → - (x - y) ≡ (- x) + y
-Distr' x y = -[x-y]≡y-x x y ∙ +Comm y (- x)


+InvR : ∀ x → x - x ≡ 0
+InvR x = +Comm x (- x) ∙ +InvL x

+CancelL : ∀ x y z → x + y ≡ x + z → y ≡ z
+CancelL x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +Assoc (- x) x y ∙ cong (_+ y) (+InvL x) ∙ +IdL y

+CancelR : ∀ x y z → x + y ≡ z + y → x ≡ z
+CancelR x y z p = +CancelL y x z (+Comm y x ∙ p ∙ +Comm z y)

+CancelL- : ∀ x y z → x + y ≡ z → x ≡ z - y
+CancelL- x y z p = (sym (+IdR x)  ∙ cong (x +_) (sym (+InvR y)))
  ∙∙  (+Assoc x y (- y)) ∙∙ cong (_- y) p

abs : ℚ → ℚ
abs x = max x (- x)

abs' : ℚ → ℚ
abs' = SetQuotient.Rec.go w
 where
 w : SetQuotient.Rec ℚ
 w .SetQuotient.Rec.isSetB = isSetℚ
 w .SetQuotient.Rec.f (a , b) = [ ℤ.pos (ℤ.abs a) , b ]
 w .SetQuotient.Rec.f∼ (a , 1+ b) (a' , 1+ b') r = eq/ _ _
   ((sym (ℤ.pos·pos (ℤ.abs a) (suc b')) ∙
      cong ℤ.pos (sym (ℤ.abs· (a) (ℕ₊₁→ℤ (1+ b'))) ))
     ∙∙ cong (λ x → ℤ.pos (ℤ.abs x)) r
     ∙∙ sym ((sym (ℤ.pos·pos (ℤ.abs a') (suc b)) ∙
      cong ℤ.pos (sym (ℤ.abs· (a') (ℕ₊₁→ℤ (1+ b))) ))))

abs'≡abs : ∀ x → abs x ≡ abs' x
abs'≡abs = SetQuotient.ElimProp.go w
 where
 w : SetQuotient.ElimProp (λ z → abs z ≡ abs' z)
 w .SetQuotient.ElimProp.isPropB _ = isSetℚ _ _
 w .SetQuotient.ElimProp.f (a , 1+ b) = eq/ _ _  ww
  where

  ww : ℤ.max (a ℤ.· ℕ₊₁→ℤ (1 ·₊₁ 1+ b))
              ((ℤ.- a)  ℤ.· ℕ₊₁→ℤ (1+ b)) ℤ.· ℤ.pos (suc b) ≡
         ℤ.pos (ℤ.abs a) ℤ.·
           ℕ₊₁→ℤ ((1+ b) ·₊₁ (1 ·₊₁ 1+ b))
  ww = cong (ℤ._· ℤ.pos (suc b))
         ((λ i → ℤ.max (a ℤ.· ℕ₊₁→ℤ (·₊₁-identityˡ (1+ b) i))
              ((ℤ.- a)  ℤ.· ℕ₊₁→ℤ (1+ b))) ∙ sym (ℤ.·DistPosLMax a ((ℤ.- a)) (suc b)) ) ∙∙
      (λ i → ℤ.·Assoc (ℤ.abs-max a (~ i)) (ℕ₊₁→ℤ (1+ b))
         (ℕ₊₁→ℤ (·₊₁-identityˡ (1+ b) (~ i))) (~ i)) ∙∙
          cong (ℤ.pos (ℤ.abs a) ℤ.·_)
           (sym (pos·pos (suc b) (ℕ₊₁→ℕ (·₊₁-identityˡ (1+ b) (~ i1)))))

ℤ+→ℚ+ : ∀ m n → [ m / 1 ] + [ n / 1 ] ≡ [ m ℤ.+ n / 1 ]
ℤ+→ℚ+ m n = cong [_/ 1 ] (cong₂ ℤ._+_ (ℤ.·IdR m) (ℤ.·IdR n))

ℤ-→ℚ- : ∀ m n → [ m / 1 ] - [ n / 1 ] ≡ [ m ℤ.- n / 1 ]
ℤ-→ℚ- m n = cong [_/ 1 ]
  (cong₂
    ℤ._+_ (ℤ.·IdR m)
    (ℤ.·IdR (ℤ.- n)))

ℕ+→ℚ+ : ∀ m n → fromNat m + fromNat n ≡ fromNat (m ℕ.+ n)
ℕ+→ℚ+ m n = ℤ+→ℚ+ (ℤ.pos m) (ℤ.pos n) ∙ cong [_/ 1 ] (sym (ℤ.pos+ m n))

ℕ·→ℚ· : ∀ m n → fromNat m · fromNat n ≡ fromNat (m ℕ.· n)
ℕ·→ℚ· m n = cong [_/ 1 ] (sym (ℤ.pos·pos m n))


x+x≡2x : ∀ x → x + x ≡ 2 · x
x+x≡2x x = cong₂ _+_
    (sym (·IdL x))
    (sym (·IdL x))
    ∙ sym (·DistR+ 1 1 x)
