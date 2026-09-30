module Cubical.Data.Rationals.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence

open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; neg ; negsuc ; pos0+ ; sign)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.HITs.SetQuotients as SetQuotient using (ElimProp)
  renaming (_/_ to _//_)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Coprime
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Sum
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Base

∼→sign≡sign : ∀ a a' b b' → (a , b) ∼ (a' , b') → ℤ.sign a ≡ ℤ.sign a'
∼→sign≡sign (pos zero)    (pos zero)    _ _ = λ _ → refl
∼→sign≡sign (pos zero)    (pos (suc n)) _ _ = ⊥.rec ∘ ℕ.znots ∘ ℤ.injPos
∼→sign≡sign (pos (suc m)) (pos zero)    _ _ = ⊥.rec ∘ ℕ.snotz ∘ ℤ.injPos
∼→sign≡sign (pos (suc m)) (pos (suc n)) _ _ = λ _ → refl
∼→sign≡sign (pos m)       (negsuc n)    _ _ = ⊥.rec ∘ ℤ.posNotnegsuc _ _
∼→sign≡sign (negsuc m)    (pos n)       _ _ = ⊥.rec ∘ ℤ.negsucNotpos _ _
∼→sign≡sign (negsuc m)    (negsuc n)    _ _ = λ _ → refl

·CancelL : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a / c ·₊₁ b ] ≡ [ a / b ]
·CancelL {a} {b} c = eq/ _ _
  ((ℕ₊₁→ℤ c ℤ.· a)   ℤ.· ℕ₊₁→ℤ b  ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.·Comm (ℕ₊₁→ℤ c) a) ⟩
   (a ℤ.· (ℕ₊₁→ℤ c)) ℤ.· ℕ₊₁→ℤ b  ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
    a ℤ.· (ℕ₊₁→ℤ c   ℤ.· ℕ₊₁→ℤ b) ∎)

·CancelR : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c / b ·₊₁ c ] ≡ [ a / b ]
·CancelR {a} {b} c = eq/ _ _
  (a ℤ.·  ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b   ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ c ℤ.· ℕ₊₁→ℤ b)  ≡⟨ cong (a ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ c) (ℕ₊₁→ℤ b)) ⟩
   a ℤ.· (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ c)  ∎)

module Reduce where
  reduced : ℚ → Type
  reduced q = Σ[ (a , b) ∈ ℤ × ℕ₊₁ ] (areCoprime (ℤ.abs a , ℕ₊₁→ℕ b)) × ([ a / b ] ≡ q)

  isPropReduced : ∀ q → isProp (reduced q)
  isPropReduced q ((a , b) , cop , a/b≡q) ((c , d) , cop' , c/d≡q) = proof where
    ad≡cb : (a , b) ∼ (c , d)
    ad≡cb = eq/⁻¹ _ _ (a/b≡q ∙ sym c/d≡q)

    ∣a∣d≡∣c∣b : ℤ.abs a ℕ.· ℕ₊₁→ℕ d ≡ ℤ.abs c ℕ.· ℕ₊₁→ℕ b
    ∣a∣d≡∣c∣b = sym (ℤ.abs· a (ℕ₊₁→ℤ d)) ∙∙ cong ℤ.abs ad≡cb ∙∙ ℤ.abs· c (ℕ₊₁→ℤ b)

    num≡num : a ≡ c
    num≡num = sym (ℤ.sign·abs a)
           ∙∙ cong₂ (flip ℤ._·_ ∘ pos)
                (natDivisibility cop cop' ∣a∣d≡∣c∣b) (∼→sign≡sign a c _ _ ad≡cb)
           ∙∙ (ℤ.sign·abs c)

    den≡den : b ≡ d
    den≡den = cong 1+_ $ natDivisibility' cop cop' ∣a∣d≡∣c∣b

    proof : ((a , b) , cop , a/b≡q) ≡ ((c , d) , cop' , c/d≡q)
    proof =
      Σ≡Prop (λ (a , b) → isProp× (isPropAreCoprime (ℤ.abs a) (ℕ₊₁→ℕ b)) (isSetℚ _ q))
      (ΣPathP (num≡num , den≡den))

  reduceΣ : ∀ q → reduced q
  reduceΣ = ElimProp.go onFrac module ReduceΣ where
    onFrac : ElimProp reduced
    onFrac .ElimProp.fun (a , b₊) = reduced[] where
      open ToCoprime (ℤ.abs a , b₊) renaming (toCoprimeAreCoprime to tcac ; c₂ to c₂₊)
      b = ℕ₊₁→ℕ b₊ ; +b = pos b ; +c₁ = pos c₁ ; c₂ = ℕ₊₁→ℕ c₂₊ ; +c₂ = pos c₂

      lemma-cop : ∀ {c} {d-1} a → c ·ℕ suc d-1 ≡ ℤ.abs a → c ≡ ℤ.abs (sign a ·ℤ pos c)
      lemma-cop {zero } (pos zero)    _ = refl
      lemma-cop {suc _} (pos zero)    x = ⊥.rec (ℕ.snotz x)
      lemma-cop {c    } (pos (suc n)) _ = sym $ ℕ.+-zero c
      lemma-cop {zero } (negsuc n)    _ = refl
      lemma-cop {suc c} (negsuc n)    _ = cong suc $ sym $ ℕ.+-zero c

      reduced[] : reduced [ a / b₊ ]
      reduced[] .fst      = sign a ·ℤ pos c₁ , c₂₊
      reduced[] .snd .fst =
        subst (areCoprime ∘ (_, c₂)) (lemma-cop a (cong (c₁ ·ℕ_) (sym q) ∙ p₁)) tcac
      reduced[] .snd .snd = eq/ _ _ $
        sign a ·ℤ   +c₁ ·ℤ +b            ≡⟨ sym $ ℤ.·Assoc (sign a) _ _ ⟩
        sign a ·ℤ ( +c₁ ·ℤ +b)           ≡⟨ cong ((sign a ·ℤ_) ∘ pos) $
                     c₁ ·ℕ b             ≡⟨ sym $ cong (c₁ ·ℕ_) p₂ ⟩
                     c₁ ·ℕ (c₂ ·ℕ d )    ≡⟨ cong (c₁ ·ℕ_) (ℕ.·-comm c₂ d) ⟩
                     c₁ ·ℕ (d  ·ℕ c₂)    ≡⟨ ℕ.·-assoc c₁ d c₂ ⟩ cong (_·ℕ c₂) p₁ ⟩
        sign a ·ℤ  pos( ℤ.abs a ·ℕ c₂)   ≡⟨ ℤ.·Assoc (sign a) _ _ ⟩
        sign a ·ℤ  pos( ℤ.abs a ) ·ℤ +c₂ ≡⟨ cong (_·ℤ +c₂) (ℤ.sign·abs a) ⟩
        a ·ℤ +c₂                         ∎
    onFrac .ElimProp.prop = isPropReduced

reduce : ℚ → ℚ
reduce = [_] ∘ fst ∘ Reduce.reduceΣ

reduce≡ : ∀ x → reduce x ≡ x
reduce≡ = snd ∘ snd ∘ Reduce.reduceΣ

-- useful functions for defining operations on ℚ

record OnCommonDenom : Type₀ where
  no-eta-equality
  field
    fun : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    eql : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) → (a , b) ∼ (c , d)
        → ℕ₊₁→ℤ d ℤ.· (fun (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (fun (c , d) (e , f))
    eqr : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) → (c , d) ∼ (e , f)
        → (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d

  go : ℚ → ℚ → ℚ
  go = SetQuotient.Rec2.go r module GO where
    r : SetQuotient.Rec2 ℚ
    r .SetQuotient.Rec2.fun = λ x y → [ fun x y / (snd x) ·₊₁ (snd y) ]
    r .SetQuotient.Rec2.set = isSetℚ
    r .SetQuotient.Rec2.eql = eql' where abstract
      eql' : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → [ fun (a , b) (e , f) / b ·₊₁ f ] ≡ [ fun (c , d) (e , f) / d ·₊₁ f ]
      eql' (a , b) (c , d) (e , f) p =
        [ fun (a , b) (e , f) / b ·₊₁ f ]
          ≡⟨ sym (·CancelL d) ⟩
        [ ℕ₊₁→ℤ d ℤ.· (fun (a , b) (e , f)) / d ·₊₁ (b ·₊₁ f) ]
          ≡[ i ]⟨ [ ℕ₊₁→ℤ d ℤ.· (fun (a , b) (e , f)) / ·₊₁-assoc d b f i ] ⟩
        [ ℕ₊₁→ℤ d ℤ.· (fun (a , b) (e , f)) / (d ·₊₁ b) ·₊₁ f ]
          ≡[ i ]⟨ [ eql (a , b) (c , d) (e , f) p i / ·₊₁-comm d b i ·₊₁ f ] ⟩
        [ ℕ₊₁→ℤ b ℤ.· (fun (c , d) (e , f)) / (b ·₊₁ d) ·₊₁ f ]
          ≡[ i ]⟨ [ ℕ₊₁→ℤ b ℤ.· (fun (c , d) (e , f)) / ·₊₁-assoc b d f (~ i) ] ⟩
        [ ℕ₊₁→ℤ b ℤ.· (fun (c , d) (e , f)) / b ·₊₁ (d ·₊₁ f) ]
          ≡⟨ ·CancelL b ⟩
        [ fun (c , d) (e , f) / d ·₊₁ f ] ∎
    r .SetQuotient.Rec2.eqr = eqr' where abstract
      eqr' : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
           → [ fun (a , b) (c , d) / b ·₊₁ d ] ≡ [ fun (a , b) (e , f) / b ·₊₁ f ]
      eqr' (a , b) (c , d) (e , f) p =
        [ fun (a , b) (c , d) / b ·₊₁ d ]
          ≡⟨ sym (·CancelR f) ⟩
        [ (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / (b ·₊₁ d) ·₊₁ f ]
          ≡[ i ]⟨ [ (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / ·₊₁-assoc b d f (~ i) ] ⟩
        [ (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / b ·₊₁ (d ·₊₁ f) ]
          ≡[ i ]⟨ [ eqr (a , b) (c , d) (e , f) p i / b ·₊₁ ·₊₁-comm d f i ] ⟩
        [ (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / b ·₊₁ (f ·₊₁ d) ]
          ≡[ i ]⟨ [ (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / ·₊₁-assoc b f d i ] ⟩
        [ (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / (b ·₊₁ f) ·₊₁ d ]
          ≡⟨ ·CancelR d ⟩
        [ fun (a , b) (e , f) / b ·₊₁ f ] ∎

{-# DISPLAY OnCommonDenom.GO.r r = r #-}

record OnCommonDenomSym : Type₀ where
  no-eta-equality
  field
    fun  : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    comm : ∀ x y → fun x y ≡ fun y x
    eql  : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) → (a , b) ∼ (c , d)
         → ℕ₊₁→ℤ d ℤ.· (fun (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (fun (c , d) (e , f))

  go : ℚ → ℚ → ℚ
  go = OnCommonDenom.go r module GO where
    r : OnCommonDenom
    r .OnCommonDenom.fun = fun
    r .OnCommonDenom.eql = eql
    r .OnCommonDenom.eqr = eqr where abstract
      eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
          → (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d
      eqr (a , b) (c , d) (e , f) p =
        (fun (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f
          ≡[ i ]⟨ ℤ.·Comm (comm (a , b) (c , d) i) (ℕ₊₁→ℤ f) i ⟩
        ℕ₊₁→ℤ f ℤ.· (fun (c , d) (a , b))
          ≡⟨ eql (c , d) (e , f) (a , b) p ⟩
        ℕ₊₁→ℤ d ℤ.· (fun (e , f) (a , b))
          ≡[ i ]⟨ ℤ.·Comm (ℕ₊₁→ℤ d) (comm (e , f) (a , b) i) i ⟩
        (fun (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d ∎

  go-comm : ∀ x y → go x y ≡ go y x
  go-comm = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
    λ (a , b) (c , d) i → [ comm (a , b) (c , d) i / ·₊₁-comm b d i ]

{-# DISPLAY OnCommonDenomSym.GO.r r = r #-}


-- basic arithmetic operations on ℚ

infixl 6 _+_
infixl 7 _·_

private abstract
  lem₁ : ∀ a b c d e (p : a ℤ.· b ≡ c ℤ.· d) → b ℤ.· (a ℤ.· e) ≡ d ℤ.· (c ℤ.· e)
  lem₁ a b c d e p =   ℤ.·Assoc b a e
                     ∙ cong (ℤ._· e) (ℤ.·Comm b a ∙ p ∙ ℤ.·Comm c d)
                     ∙ sym (ℤ.·Assoc d c e)

  lem₂ : ∀ a b c → a ℤ.· (b ℤ.· c) ≡ c ℤ.· (b ℤ.· a)
  lem₂ a b c =   cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b
               ∙ cong (ℤ._· b) (ℤ.·Comm a c) ∙ sym (ℤ.·Assoc c a b)
               ∙ cong (c ℤ.·_) (ℤ.·Comm a b)

min : ℚ → ℚ → ℚ
min = OnCommonDenomSym.go onFrac module min where
  open OnCommonDenomSym
  onFrac : OnCommonDenomSym
  onFrac .fun  (a , b) (c , d) = ℤ.min (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
  onFrac .comm (a , b) (c , d) = ℤ.minComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
  onFrac .eql  = eq where abstract
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

max : ℚ → ℚ → ℚ
max = OnCommonDenomSym.go onFrac module max where
  open OnCommonDenomSym
  onFrac : OnCommonDenomSym
  onFrac .fun  (a , b) (c , d) = ℤ.max (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
  onFrac .comm (a , b) (c , d) = ℤ.maxComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
  onFrac .eql  = eq where abstract
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

minComm : ∀ x y → min x y ≡ min y x
minComm = OnCommonDenomSym.go-comm min.onFrac

maxComm : ∀ x y → max x y ≡ max y x
maxComm = OnCommonDenomSym.go-comm max.onFrac

minIdem : ∀ x → min x x ≡ x
minIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.minIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b))) }

maxIdem : ∀ x → max x x ≡ x
maxIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.maxIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b))) }

minAssoc : ∀ x y z → min x (min y z) ≡ min (min x y) z
minAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.min
               (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMin (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.min (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))))
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
               (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMax (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.max (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))))
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
                                 cong (a ℤ.·_) (cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.minAbsorbLMax (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
                 ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                    cong (a ℤ.·_) (cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
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
                                 cong (a ℤ.·_) (cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.maxAbsorbLMin (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
             ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                cong (a ℤ.·_) (cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

_+_ : ℚ → ℚ → ℚ
_+_ = OnCommonDenomSym.go onFrac module _+_ where
  open OnCommonDenomSym
  onFrac : OnCommonDenomSym
  onFrac .fun  (a , b) (c , d) = a ℤ.· (ℕ₊₁→ℤ d) ℤ.+ c ℤ.· (ℕ₊₁→ℤ b)
  onFrac .comm (a , b) (c , d) = ℤ.+Comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b))
  onFrac .eql  = eq where abstract
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

+Comm : ∀ x y → x + y ≡ y + x
+Comm = OnCommonDenomSym.go-comm _+_.onFrac

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
    → [ eq a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ f) i / ·₊₁-assoc b d f i ] })
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


_·_ : ℚ → ℚ → ℚ
_·_ = OnCommonDenomSym.go onFrac module _·_ where
  open OnCommonDenomSym
  onFrac : OnCommonDenomSym
  onFrac .fun  (a , _) (c , _) = a ℤ.· c
  onFrac .comm (a , _) (c , _) = ℤ.·Comm a c
  onFrac .eql  (a , b) (c , d) = lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) ∘ fst

·Comm : ∀ x y → x · y ≡ y · x
·Comm = OnCommonDenomSym.go-comm _·_.onFrac

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
          (λ i → [ lemℤ a c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) i ℤ.+ lemℤ a e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) i
                   / lemℕ₊₁ b d b f i ]) ∙
          (λ i → [ (sym (ℤ.·DistL+ (a ℤ.· (c ℤ.· ℕ₊₁→ℤ f)) (a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)) (ℕ₊₁→ℤ b))) i
                   / (b ·₊₁ (d ·₊₁ f)) ·₊₁ b ]) ∙
          ·CancelR {a ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ a ℤ.· (e ℤ.· ℕ₊₁→ℤ d)} {b ·₊₁ (d ·₊₁ f)} b ∙
          (λ i → [ (sym (ℤ.·DistR+ a (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d))) i
                   / b ·₊₁ (d ·₊₁ f) ])

·DistR+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
·DistR+ x y z = sym ((λ i → ·Comm x z i + ·Comm y z i) ∙ (sym (·DistL+ z x y)) ∙ ·Comm z (x + y))


-_ : ℚ → ℚ
- x = -1 · x

-Invol : ∀ x → - - x ≡ x
-Invol x = ·Assoc -1 -1 x ∙ ·IdL x

negateEquiv : ℚ ≃ ℚ
negateEquiv = isoToEquiv (iso -_ -_ -Invol -Invol)

negateEq : ℚ ≡ ℚ
negateEq = ua negateEquiv

+InvL : ∀ x → (- x) + x ≡ 0
+InvL x = (λ i → (-1 · x) + ·IdL x (~ i)) ∙ (sym (·DistR+ -1 1 x)) ∙ ·AnnihilL x

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)

+InvR : ∀ x → x - x ≡ 0
+InvR x = +Comm x (- x) ∙ +InvL x

+CancelL : ∀ x y z → x + y ≡ x + z → y ≡ z
+CancelL x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +Assoc (- x) x y ∙ cong (_+ y) (+InvL x) ∙ +IdL y

+CancelR : ∀ x y z → x + y ≡ z + y → x ≡ z
+CancelR x y z p = +CancelL y x z (+Comm y x ∙ p ∙ +Comm z y)

numerator0→0 : (u : ℤ × ℕ₊₁) → u .fst ≡ 0 → [ u ] ≡ 0
numerator0→0 (a , b) p = eq/ (a , b) (0 , 1) (ℤ.·IdR a ∙ p)

{-# DISPLAY min.onFrac = min #-}
{-# DISPLAY max.onFrac = max #-}
{-# DISPLAY _+_.onFrac = _+_ #-}
{-# DISPLAY _·_.onFrac = _·_ #-}
