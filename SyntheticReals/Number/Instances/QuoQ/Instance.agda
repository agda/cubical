{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Instances.QuoQ.Instance where


open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation renaming (elim to ∣∣-elim)

open import SyntheticReals.Utils using (!_; !!_)
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.MorePropAlgebra.Bundles
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.Number.Structures2
open import SyntheticReals.Number.Bundles2

open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁; ℕ₊₁→ℕ) renaming
  ( _*₊₁_         to _·₊₁_
  ; *₊₁-comm      to ·₊₁-comm
  ; *₊₁-assoc     to ·₊₁-assoc
  ; *₊₁-identityˡ to ·₊₁-identityˡ
  ; *₊₁-identityʳ to ·₊₁-identityʳ
  )
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Bool
open import SyntheticReals.Number.Prelude.Nat
open import SyntheticReals.Number.Prelude.QuoInt
open import Cubical.HITs.Ints.QuoInt using (HasFromNat)
open import SyntheticReals.Number.Instances.QuoQ.Definitions
open import Cubical.HITs.Rationals.QuoQ using
  ( ℚ
  ; HasFromNat
  ; isSetℚ
  ; onCommonDenom
  ; onCommonDenomSym
  ; eq/
  ; eq/⁻¹
  ; _//_
  ; _∼_
  ; [_/_]
  ) renaming
  ( [_] to [_]ᶠ
  ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
  ; _*_ to _·_
  ; *-comm to ·-comm
  ; *-assoc to ·-assoc
  )

{-# DISPLAY [_/_] (pos 1) (1+ 0) = 1 #-}
{-# DISPLAY [_/_] (pos 0) (1+ 0) = 0 #-}

private
  ·ᶻ-commʳ : ∀ a b c → (a ·ᶻ b) ·ᶻ c ≡ (a ·ᶻ c) ·ᶻ b
  ·ᶻ-commʳ a b c = (a ·ᶻ  b) ·ᶻ c  ≡⟨ sym $ ·ᶻ-assoc a b c ⟩
                    a ·ᶻ (b  ·ᶻ c) ≡⟨ (λ i → a ·ᶻ ·ᶻ-comm b c i) ⟩
                    a ·ᶻ (c  ·ᶻ b) ≡⟨ ·ᶻ-assoc a c b ⟩
                   (a ·ᶻ  c) ·ᶻ b  ∎

  ·ᶻ-commˡ : ∀ a b c → a ·ᶻ (b ·ᶻ c) ≡ b ·ᶻ (a ·ᶻ c)
  ·ᶻ-commˡ a b c = ·ᶻ-comm a (b ·ᶻ c) ∙ sym (·ᶻ-commʳ b a c) ∙ sym (·ᶻ-assoc b a c)

  is-0<ⁿᶻ : ∀{aⁿ} → [ 0 <ᶻ [1+ aⁿ ⁿ]ᶻ ]
  is-0<ⁿᶻ {aⁿ} = ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1

  is-0≤ⁿᶻ : ∀{aⁿ} → [ 0 ≤ᶻ [1+ aⁿ ⁿ]ᶻ ]
  is-0≤ⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

<-irrefl : ∀ a → [ ¬(a < a) ]
<-irrefl = SetQuotient.elimProp {R = _∼_} (λ a → isProp[] (¬(a < a))) γ where
  γ : (a : ℤ × ℕ₊₁) → [ ¬([ a ]ᶠ < [ a ]ᶠ) ]
  γ a@(aᶻ , aⁿ) = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    κ : [ ¬((aᶻ ·ᶻ aⁿᶻ) <ᶻ (aᶻ ·ᶻ aⁿᶻ)) ]
    κ = <ᶻ-irrefl (aᶻ ·ᶻ aⁿᶻ)


<-trans : (a b c : ℚ) → [ a < b ] → [ b < c ] → [ a < c ]
<-trans = SetQuotient.elimProp3 {R = _∼_} (λ a b c → isProp[] ((a < b) ⇒ (b < c) ⇒ (a < c))) γ where
  γ : (a b c : ℤ × ℕ₊₁) → [ [ a ]ᶠ < [ b ]ᶠ ] → [ [ b ]ᶠ < [ c ]ᶠ ] → [ [ a ]ᶠ < [ c ]ᶠ ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = κ where
    aⁿᶻ   = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ   = [1+ bⁿ ⁿ]ᶻ
    cⁿᶻ   = [1+ cⁿ ⁿ]ᶻ
    0<aⁿᶻ = [ 0 <ᶻ aⁿᶻ ] ∋ is-0<ⁿᶻ
    0<bⁿᶻ = [ 0 <ᶻ bⁿᶻ ] ∋ is-0<ⁿᶻ
    0<cⁿᶻ = [ 0 <ᶻ cⁿᶻ ] ∋ is-0<ⁿᶻ
    κ : [ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ) ] → [ (bᶻ ·ᶻ cⁿᶻ) <ᶻ (cᶻ ·ᶻ bⁿᶻ) ] → [ (aᶻ ·ᶻ cⁿᶻ) <ᶻ (cᶻ ·ᶻ aⁿᶻ) ]
    -- strategy: multiply with xⁿᶻ and then use <ᶻ-trans
    κ p₁ p₂ = ·ᶻ-reflects-<ᶻ (aᶻ ·ᶻ cⁿᶻ) (cᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0<bⁿᶻ φ₃ where
      φ₁ = ( aᶻ ·ᶻ bⁿᶻ        <ᶻ bᶻ ·ᶻ aⁿᶻ        ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) cⁿᶻ 0<cⁿᶻ ⟩
             aᶻ ·ᶻ bⁿᶻ ·ᶻ cⁿᶻ <ᶻ bᶻ ·ᶻ aⁿᶻ ·ᶻ cⁿᶻ ⇒ᵖ⟨ transport (λ i → [ ·ᶻ-commʳ aᶻ bⁿᶻ cⁿᶻ i <ᶻ ·ᶻ-commʳ bᶻ aⁿᶻ cⁿᶻ i ]) ⟩
             aᶻ ·ᶻ cⁿᶻ ·ᶻ bⁿᶻ <ᶻ bᶻ ·ᶻ cⁿᶻ ·ᶻ aⁿᶻ ◼ᵖ) .snd p₁
      φ₂ = ( bᶻ ·ᶻ cⁿᶻ        <ᶻ cᶻ ·ᶻ bⁿᶻ        ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ (bᶻ ·ᶻ cⁿᶻ) (cᶻ ·ᶻ bⁿᶻ) aⁿᶻ 0<aⁿᶻ ⟩
             bᶻ ·ᶻ cⁿᶻ ·ᶻ aⁿᶻ <ᶻ cᶻ ·ᶻ bⁿᶻ ·ᶻ aⁿᶻ ⇒ᵖ⟨ transport (λ i → [ (bᶻ ·ᶻ cⁿᶻ ·ᶻ aⁿᶻ) <ᶻ ·ᶻ-commʳ cᶻ bⁿᶻ aⁿᶻ i ]) ⟩
             bᶻ ·ᶻ cⁿᶻ ·ᶻ aⁿᶻ <ᶻ cᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ ◼ᵖ) .snd p₂
      φ₃ : [ aᶻ ·ᶻ cⁿᶻ ·ᶻ bⁿᶻ <ᶻ cᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ ]
      φ₃ = <ᶻ-trans (aᶻ ·ᶻ cⁿᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ cⁿᶻ ·ᶻ aⁿᶻ) (cᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ) φ₁ φ₂

<-asym : ∀ a b → [ a < b ] → [ ¬(b < a) ]
<-asym a b a<b b<a = <-irrefl a (<-trans a b a a<b b<a)

<-irrefl'' : ∀ a b → [ a < b ] ⊎ [ b < a ] → [ ¬(a ≡ₚ b) ]
<-irrefl'' a b (inl a<b) a≡b = <-irrefl b (substₚ (λ p → p < b) a≡b a<b)
<-irrefl'' a b (inr b<a) a≡b = <-irrefl b (substₚ (λ p → b < p) a≡b b<a)

<-tricho : (a b : ℚ) → ([ a < b ] ⊎ [ b < a ]) ⊎ [ a ≡ₚ b ] -- TODO: insert trichotomy definition here
<-tricho = SetQuotient.elimProp2 {R = _∼_} (λ a b → isProp[] ([ <-irrefl'' a b ] ([ <-asym a b ] (a < b) ⊎ᵖ (b < a)) ⊎ᵖ (a ≡ₚ b))) γ where
  γ : (a b : ℤ × ℕ₊₁) → ([ [ a ]ᶠ < [ b ]ᶠ ] ⊎ [ [ b ]ᶠ < [ a ]ᶠ ]) ⊎ [ [ a ]ᶠ ≡ₚ [ b ]ᶠ ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    κ : ([ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ) ] ⊎ [ (bᶻ ·ᶻ aⁿᶻ) <ᶻ (aᶻ ·ᶻ bⁿᶻ) ]) ⊎ [ [ aᶻ , aⁿ ]ᶠ ≡ₚ [ bᶻ , bⁿ ]ᶠ ]
    κ with <ᶻ-tricho (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)
    ... | inl p = inl p
    ... | inr p = inr ∣ eq/ {R = _∼_} a b p ∣

<-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = <-irrefl
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  = <-trans
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho = <-tricho

<-StrictPartialOrder : [ isStrictPartialOrder _<_ ]
<-StrictPartialOrder = strictlinearorder⇒strictpartialorder _<_ <-StrictLinearOrder

_#_ : hPropRel ℚ ℚ ℓ-zero
x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

#-ApartnessRel : [ isApartnessRel _#_ ]
#-ApartnessRel = #''-isApartnessRel <-StrictPartialOrder <-asym

open IsApartnessRel #-ApartnessRel public renaming
  ( is-irrefl  to #-irrefl
  ; is-sym     to #-sym
  ; is-cotrans to #-cotrans
  )

#-split' : ∀ z n → [ [ z , n ]ᶠ # 0 ] → [ z <ᶻ 0 ] ⊎ [ 0 <ᶻ z ]
#-split' (pos zero) _ p = p
#-split' (neg zero) _ p = p
#-split' (posneg i) _ p = p
#-split' (pos (suc n)) _ p = transport (λ i → [ suc (·ⁿ-identityʳ n i) <ⁿ 0 ] ⊎ [ 0 <ⁿ suc (·ⁿ-identityʳ n i) ]) p
#-split' (neg (suc n)) _ p = p

_⁻¹'  : (x : ℤ × ℕ₊₁) → [ [ x ]ᶠ # 0 ] → ℚ
(xᶻ , xⁿ) ⁻¹' = λ _ → [ signed (signᶻ xᶻ) (ℕ₊₁→ℕ xⁿ) , absᶻ⁺¹ xᶻ ]ᶠ

⁻¹'-respects-∼ : (a b : ℤ × ℕ₊₁) (p : a ∼ b)
                → PathP (λ i → [ eq/ a b p i # 0 ] → ℚ) (a ⁻¹') (b ⁻¹')
⁻¹'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p = κ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ; 0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]; 0<aⁿᶻ = is-0<ⁿᶻ -- ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ; 0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]; 0<bⁿᶻ = is-0<ⁿᶻ -- ℕ₊₁.n bⁿ , +ⁿ-comm (ℕ₊₁.n bⁿ) 1
  η : signᶻ aᶻ ≡ signᶻ bᶻ
  η i = sign (eq/ a b p i)
  s : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
  s = p
  r : [ [ aᶻ , aⁿ ]ᶠ # 0 ] → (signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) , absᶻ⁺¹ aᶻ) ∼ (signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) , absᶻ⁺¹ bᶻ)
  r q = φ where
    φ : signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) ·ᶻ [1+ absᶻ⁺¹ bᶻ ⁿ]ᶻ ≡ signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) ·ᶻ [1+ absᶻ⁺¹ aᶻ ⁿ]ᶻ
    φ with #-split' aᶻ aⁿ q
    -- proof for aᶻ < 0
    ... | inl aᶻ<0 =
      signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) ·ᶻ [1+ absᶻ⁺¹ bᶻ ⁿ]ᶻ ≡⟨ (λ i → signed (<ᶻ0-signᶻ aᶻ aᶻ<0 i) (ℕ₊₁→ℕ aⁿ) ·ᶻ absᶻ⁺¹-identity bᶻ (inl bᶻ<0) i) ⟩
      signed  sneg      (ℕ₊₁→ℕ aⁿ) ·ᶻ pos (absᶻ bᶻ)      ≡⟨ cong₂ signed (λ i → sneg ·ˢ q₁ i) q₂ ⟩
      signed  sneg      (ℕ₊₁→ℕ bⁿ) ·ᶻ pos (absᶻ aᶻ)      ≡⟨ (λ i → signed (<ᶻ0-signᶻ bᶻ bᶻ<0 (~ i)) (ℕ₊₁→ℕ bⁿ) ·ᶻ absᶻ⁺¹-identity aᶻ (inl aᶻ<0) (~ i)) ⟩
      signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) ·ᶻ [1+ absᶻ⁺¹ aᶻ ⁿ]ᶻ ∎ where
      bᶻ<0 : [ bᶻ <ᶻ 0 ]
      bᶻ<0 = ∼-preserves-<ᶻ aᶻ aⁿ bᶻ bⁿ p .fst aᶻ<0
      abstract
        c      = suc (<ᶻ-split-neg aᶻ aᶻ<0 .fst)
        d      = suc (<ᶻ-split-neg bᶻ bᶻ<0 .fst)
        aᶻ≡-c  : aᶻ ≡ neg c
        aᶻ≡-c  = <ᶻ-split-neg aᶻ aᶻ<0 .snd
        bᶻ≡-d  : bᶻ ≡ neg d
        bᶻ≡-d  = <ᶻ-split-neg bᶻ bᶻ<0 .snd
        absa≡c : absᶻ aᶻ ≡ c
        absa≡c i = absᶻ (aᶻ≡-c i)
        absb≡d : absᶻ bᶻ ≡ d
        absb≡d i = absᶻ (bᶻ≡-d i)
      q₁ : signᶻ (pos (absᶻ bᶻ)) ≡ signᶻ (pos (absᶻ aᶻ))
      q₁ = transport (λ i → signᶻ-pos (absᶻ bᶻ) (~ i) ≡ signᶻ-pos (absᶻ aᶻ) (~ i)) refl
      s' = bᶻ ·ᶻ aⁿᶻ    ≡ aᶻ ·ᶻ bⁿᶻ                       ≡⟨ (λ i → ·ᶻ-comm bᶻ aⁿᶻ i ≡ ·ᶻ-comm aᶻ bⁿᶻ i) ⟩
           aⁿᶻ ·ᶻ bᶻ    ≡ bⁿᶻ ·ᶻ aᶻ                       ≡⟨ (λ i → aⁿᶻ ·ᶻ bᶻ≡-d i ≡ bⁿᶻ ·ᶻ aᶻ≡-c i) ⟩
           aⁿᶻ ·ᶻ neg d ≡ bⁿᶻ ·ᶻ neg c                    ≡⟨ refl ⟩
             signed (signᶻ (neg d)) (suc (ℕ₊₁.n aⁿ) ·ⁿ d)
           ≡ signed (signᶻ (neg c)) (suc (ℕ₊₁.n bⁿ) ·ⁿ c) ∎
      q₂ = (suc (ℕ₊₁.n aⁿ) ·ⁿ       d ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ      c  ⇒⟨ transport (λ i → suc (ℕ₊₁.n aⁿ) ·ⁿ absb≡d (~ i) ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ absa≡c (~ i)) ⟩
            suc (ℕ₊₁.n aⁿ) ·ⁿ absᶻ bᶻ ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ absᶻ aᶻ ◼) (λ i → absᶻ (transport s' (sym s) i))
    -- proof for 0 < aᶻ
    ... | inr 0<aᶻ =
      signed (signᶻ aᶻ ⊕ spos) (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ bᶻ))) ≡⟨ (λ i → signed (0<ᶻ-signᶻ aᶻ 0<aᶻ i ⊕ spos) (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ bᶻ)))) ⟩
      signed             spos  (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ bᶻ))) ≡⟨ transport s' (sym s) ⟩
      signed             spos  (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ aᶻ))) ≡⟨ (λ i → signed (0<ᶻ-signᶻ bᶻ 0<bᶻ (~ i) ⊕ spos) (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ aᶻ)))) ⟩
      signed (signᶻ bᶻ ⊕ spos) (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ aᶻ))) ∎ where
      0<bᶻ : [ 0 <ᶻ bᶻ ]
      0<bᶻ = ∼-preserves-<ᶻ aᶻ aⁿ bᶻ bⁿ p .snd 0<aᶻ
      abstract
        c       = <ᶻ-split-pos aᶻ 0<aᶻ .fst
        d       = <ᶻ-split-pos bᶻ 0<bᶻ .fst
        aᶻ≡sc   : aᶻ ≡ pos (suc c)
        bᶻ≡sd   : bᶻ ≡ pos (suc d)
        absa≡sc : absᶻ aᶻ ≡ suc c
        absb≡sd : absᶻ bᶻ ≡ suc d
        aᶻ≡sc   = <ᶻ-split-pos aᶻ 0<aᶻ .snd
        bᶻ≡sd   = <ᶻ-split-pos bᶻ 0<bᶻ .snd
        absa≡sc i = absᶻ (aᶻ≡sc i)
        absb≡sd i = absᶻ (bᶻ≡sd i)
      s' = bᶻ  ·ᶻ aⁿᶻ         ≡ aᶻ  ·ᶻ bⁿᶻ         ≡⟨ (λ i → ·ᶻ-comm bᶻ aⁿᶻ i ≡ ·ᶻ-comm aᶻ bⁿᶻ i) ⟩
           aⁿᶻ ·ᶻ bᶻ          ≡ bⁿᶻ ·ᶻ aᶻ          ≡⟨ (λ i → aⁿᶻ ·ᶻ bᶻ≡sd i ≡ bⁿᶻ ·ᶻ aᶻ≡sc i) ⟩
           aⁿᶻ ·ᶻ pos (suc d) ≡ bⁿᶻ ·ᶻ pos (suc c) ≡⟨ refl ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ suc d)
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ suc c) ≡⟨ (λ i → pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absb≡sd (~ i)) ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absa≡sc (~ i))) ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absᶻ bᶻ)
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absᶻ aᶻ) ≡⟨ (λ i → pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absᶻ⁺¹-identityⁿ bᶻ (inr 0<bᶻ) (~ i)) ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absᶻ⁺¹-identityⁿ aᶻ (inr 0<aᶻ) (~ i))) ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ bᶻ)))
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ aᶻ))) ∎
  -- eq/ a b r : [ a ]ᶠ ≡ [ b ]ᶠ
  γ : [ [ a ]ᶠ # 0 ] ≡ [ [ b ]ᶠ # 0 ]
  γ i = [ eq/ a b p i # 0 ]
  κ : PathP _ (a ⁻¹') (b ⁻¹')
  κ i = λ(q : [ eq/ a b p i # 0 ]) → eq/ (signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) , absᶻ⁺¹ aᶻ) (signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) , absᶻ⁺¹ bᶻ) (r (ψ q)) i where
    ψ : [ eq/ a b p i # 0 ] → [ eq/ a b p i0 # 0 ]
    ψ p = transport (λ j → γ (i ∧ ~ j)) p

_⁻¹ : (x : ℚ) → {{ _ : [ x # 0 ]}} → ℚ
(x ⁻¹) {{p}} = SetQuotient.elim {R = _∼_} {B = λ x → [ x # 0 ] → ℚ} φ _⁻¹' ⁻¹'-respects-∼ x p where
  φ : ∀ x → isSet ([ x # 0 ] → ℚ)
  φ x = isSetΠ (λ _ → isSetℚ)
  -- φ' : ∀ x → isSet ({{_ : [ x # 0 ]}} → ℚ)
  -- φ' x = transport (λ i → ∀ x → isSet (instance≡ {A = [ x # 0 ]} {B = λ _ → ℚ} (~ i))) φ x

⊕-diagonal : ∀ s → s ⊕ s ≡ spos
⊕-diagonal spos = refl
⊕-diagonal sneg = refl

zeroᶠ : ∀ x → [ 0 / x ] ≡ 0
zeroᶠ x = eq/ (0 , x) (0 , 1) refl

#⇒#ᶻ : ∀ xᶻ xⁿ → [ [ xᶻ / xⁿ ] # 0 ] → [ xᶻ #ᶻ 0 ]
#⇒#ᶻ (pos zero)    xⁿ p = p
#⇒#ᶻ (neg zero)    xⁿ p = p
#⇒#ᶻ (posneg i)    xⁿ p = p
#⇒#ᶻ (pos (suc n)) xⁿ (inl p) = inl (transport (λ i → [ suc (·ⁿ-identityʳ n i) <ⁿ 0 ]) p)
#⇒#ᶻ (pos (suc n)) xⁿ (inr p) = inr (transport (λ i → [ 0 <ⁿ suc (·ⁿ-identityʳ n i) ]) p)
#⇒#ᶻ (neg (suc n)) xⁿ p = inl tt

#ᶻ⇒# : ∀ xᶻ xⁿ → [ xᶻ #ᶻ 0 ] → [ [ xᶻ / xⁿ ] # 0 ]
#ᶻ⇒# (pos zero) xⁿ p = p
#ᶻ⇒# (neg zero) xⁿ p = p
#ᶻ⇒# (posneg i) xⁿ p = p
#ᶻ⇒# (pos (suc n)) xⁿ (inl p) = inl (transport (λ i → [ suc (·ⁿ-identityʳ n (~ i)) <ⁿ 0 ]) p)
#ᶻ⇒# (pos (suc n)) xⁿ (inr p) = inr (transport (λ i → [ 0 <ⁿ suc (·ⁿ-identityʳ n (~ i)) ]) p)
#ᶻ⇒# (neg (suc n)) xⁿ p = inl tt

·-invʳ' : ∀ x → (p : [ [ x ]ᶠ # 0 ]) → [ x ]ᶠ · ([ x ]ᶠ ⁻¹) {{p}} ≡ 1
·-invʳ' x@(xᶻ , xⁿ) p = γ where
  aᶻ  : ℤ
  aⁿ  : ℕ₊₁
  aᶻ  = signed (signᶻ xᶻ ⊕ signᶻ xᶻ) (absᶻ xᶻ ·ⁿ suc (ℕ₊₁.n xⁿ))
  aⁿ  = 1+ (ℕ₊₁.n (absᶻ⁺¹ xᶻ) +ⁿ ℕ₊₁.n xⁿ ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ xᶻ)))
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  η = absᶻ xᶻ ·ⁿ suc (ℕ₊₁.n xⁿ) ≡⟨ ·ⁿ-comm (absᶻ xᶻ) (suc (ℕ₊₁.n xⁿ)) ⟩
      suc (ℕ₊₁.n xⁿ) ·ⁿ absᶻ xᶻ ≡⟨ (λ i → suc (ℕ₊₁.n xⁿ) ·ⁿ absᶻ⁺¹-identityⁿ xᶻ (#⇒#ᶻ xᶻ xⁿ p) (~ i)) ⟩
      suc (ℕ₊₁.n xⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ xᶻ)) ∎
  ψ : aᶻ ≡ aⁿᶻ
  ψ = signed (signᶻ xᶻ ⊕ signᶻ xᶻ) (absᶻ xᶻ ·ⁿ suc (ℕ₊₁.n xⁿ)) ≡⟨ cong₂ signed (⊕-diagonal (signᶻ xᶻ)) refl ⟩
      signed  spos                 (absᶻ xᶻ ·ⁿ suc (ℕ₊₁.n xⁿ)) ≡⟨ cong pos η ⟩
      pos (suc (ℕ₊₁.n xⁿ) ·ⁿ suc (ℕ₊₁.n (absᶻ⁺¹ xᶻ))) ∎
  φ : aᶻ ·ᶻ 1 ≡ 1 ·ᶻ aⁿᶻ
  φ = ·ᶻ-identity aᶻ .fst ∙ ψ ∙ sym (·ᶻ-identity aⁿᶻ .snd)
  κ : (aᶻ , aⁿ) ∼ (pos 1 , (1+ 0))
  κ = φ
  γ : [ aᶻ , aⁿ ]ᶠ ≡ 1
  γ = eq/ (aᶻ , aⁿ) (pos 1 , (1+ 0)) κ

·-invʳ : ∀ x → (p : [ x # 0 ]) → x · (x ⁻¹) {{p}} ≡ 1
·-invʳ = let P : ℚ → hProp ℓ-zero
             P x = ∀ᵖ[ p ∶ x # 0 ] ([ isSetℚ ] x · (x ⁻¹) {{p}} ≡ˢ 1)
         in  SetQuotient.elimProp {R = _∼_} (λ x → isProp[] (P x)) ·-invʳ'

·-invˡ : ∀ x → (p : [ x # 0 ]) → (x ⁻¹) {{p}} · x ≡ 1
·-invˡ x p = ·-comm _ x ∙ ·-invʳ x p

-- NOTE: we already have
--   ℚ-cancelˡ : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.* a / c *₊₁ b ] ≡ [ a / b ]
--   ℚ-cancelʳ : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.* ℕ₊₁→ℤ c / b *₊₁ c ] ≡ [ a / b ]

module _ (aᶻ : ℤ) (aⁿ bⁿ : ℕ₊₁) (let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ) (let bⁿᶻ = [1+ bⁿ ⁿ]ᶻ) where
  private
    lem : ∀ a b → signᶻ a ≡ signᶻ (signed (signᶻ a ⊕ spos) (absᶻ a ·ⁿ (ℕ₊₁→ℕ b)))
    lem (pos zero)    b j = signᶻ (posneg (i0 ∧ ~ j))
    lem (neg zero)    b j = signᶻ (posneg (i1 ∧ ~ j))
    lem (posneg i)    b j = signᶻ (posneg (i  ∧ ~ j))
    lem (pos (suc n)) b   = refl
    lem (neg (suc n)) b   = refl

    -- one could write this as a one-liner, even without mentioning cᶻ and cⁿ, but this reduces the overall proof-readability
    expand-fraction' : [ aᶻ / aⁿ ] ≡ [ aᶻ ·ᶻ bⁿᶻ / aⁿ ·₊₁ bⁿ ]
    expand-fraction' = eq/ _ _ $ (λ i → signed (lem aᶻ bⁿ i ⊕ spos) (((λ i → absᶻ aᶻ ·ⁿ ·ⁿ-comm (ℕ₊₁→ℕ aⁿ) (ℕ₊₁→ℕ bⁿ) i) ∙ ·ⁿ-assoc (absᶻ aᶻ) (ℕ₊₁→ℕ bⁿ) (ℕ₊₁→ℕ aⁿ)) i))

  expand-fraction : [ aᶻ / aⁿ ] ≡ [ aᶻ ·ᶻ bⁿᶻ / aⁿ ·₊₁ bⁿ ]
  expand-fraction = eq/ _ _ γ where
    cᶻ : ℤ
    cᶻ = signed (signᶻ aᶻ ⊕ spos) (absᶻ aᶻ ·ⁿ (ℕ₊₁→ℕ bⁿ))
    cⁿ : ℕ₊₁
    cⁿ = 1+ (ℕ₊₁.n bⁿ +ⁿ ℕ₊₁.n aⁿ ·ⁿ (ℕ₊₁→ℕ bⁿ))
    κ =  absᶻ aᶻ ·ⁿ ((ℕ₊₁→ℕ aⁿ)  ·ⁿ (ℕ₊₁→ℕ bⁿ)) ≡[ i ]⟨ absᶻ aᶻ ·ⁿ ·ⁿ-comm (ℕ₊₁→ℕ aⁿ) (ℕ₊₁→ℕ bⁿ) i ⟩
         absᶻ aᶻ ·ⁿ ((ℕ₊₁→ℕ bⁿ)  ·ⁿ (ℕ₊₁→ℕ aⁿ)) ≡⟨ ·ⁿ-assoc (absᶻ aᶻ) (ℕ₊₁→ℕ bⁿ) (ℕ₊₁→ℕ aⁿ) ⟩
        (absᶻ aᶻ ·ⁿ  (ℕ₊₁→ℕ bⁿ)) ·ⁿ (ℕ₊₁→ℕ aⁿ)  ∎
    γ : (aᶻ , aⁿ) ∼ (cᶻ , cⁿ)
    γ i = signed (lem aᶻ bⁿ i ⊕ spos) (κ i)

·-≡' : ∀ aᶻ aⁿ bᶻ bⁿ → [ aᶻ / aⁿ ] · [ bᶻ / bⁿ ] ≡ [ aᶻ ·ᶻ bᶻ / aⁿ ·₊₁ bⁿ ]
·-≡' aᶻ aⁿ bᶻ bⁿ = refl

∼⁻¹ : ∀ aᶻ aⁿ bᶻ bⁿ → [ aᶻ / aⁿ ] ≡ [ bᶻ / bⁿ ] → (aᶻ , aⁿ) ∼ (bᶻ , bⁿ)
∼⁻¹ aᶻ aⁿ bᶻ bⁿ p = eq/⁻¹ _ _ p

-- already have this in ᶻ
signᶻ-absᶻ-identity : ∀ a → signed (signᶻ a) (absᶻ a) ≡ a
signᶻ-absᶻ-identity (pos zero) j  = posneg (i0 ∧ j)
signᶻ-absᶻ-identity (neg zero) j  = posneg (i1 ∧ j)
signᶻ-absᶻ-identity (posneg i) j  = posneg (i  ∧ j)
signᶻ-absᶻ-identity (pos (suc n)) = refl
signᶻ-absᶻ-identity (neg (suc n)) = refl

-- already have this in ᶻ
absᶻ-preserves-·ᶻ : ∀ a b → absᶻ (a ·ᶻ b) ≡ absᶻ a ·ⁿ absᶻ b
absᶻ-preserves-·ᶻ a b = refl

-- already have this in ᶻ
signᶻ-absᶻ-≡ : ∀ a b → signᶻ a ≡ signᶻ b → absᶻ a ≡ absᶻ b → a ≡ b
signᶻ-absᶻ-≡ a b p q = transport (λ i → signᶻ-absᶻ-identity a i ≡ signᶻ-absᶻ-identity b i) λ i → signed (p i) (q i)

ℚ-reflects-nom : ∀ aᶻ bᶻ n → [ aᶻ / n ] ≡ [ bᶻ / n ] → aᶻ ≡ bᶻ
ℚ-reflects-nom aᶻ bᶻ n p = signᶻ-absᶻ-≡ aᶻ bᶻ φ η where
  n' = suc (ℕ₊₁.n n)
  0<n' : [ 0 <ⁿ n' ]
  0<n' = 0<ⁿsuc (ℕ₊₁.n n)
  s = signed (signᶻ aᶻ       ) (absᶻ aᶻ ·ⁿ n') ≡⟨ cong₂ signed (sym (⊕-identityʳ (signᶻ aᶻ))) refl ⟩
      signed (signᶻ aᶻ ⊕ spos) (absᶻ aᶻ ·ⁿ n') ≡⟨ eq/⁻¹ _ _ p ⟩
      signed (signᶻ bᶻ ⊕ spos) (absᶻ bᶻ ·ⁿ n') ≡⟨ cong₂ signed (⊕-identityʳ (signᶻ bᶻ)) refl ⟩
      signed (signᶻ bᶻ       ) (absᶻ bᶻ ·ⁿ n') ∎
  φ : signᶻ aᶻ ≡ signᶻ bᶻ
  φ i = sign (p i)
  κ : absᶻ aᶻ ·ⁿ n' ≡ absᶻ bᶻ ·ⁿ n'
  κ i = absᶻ (s i)
  η : absᶻ aᶻ ≡ absᶻ bᶻ
  η = ·ⁿ-reflects-≡ʳ (absᶻ aᶻ) (absᶻ bᶻ) n' 0<n' κ

ℕ₊₁→ℕ-reflects-≡ : ∀ a b → (ℕ₊₁→ℕ a) ≡ (ℕ₊₁→ℕ b) → a ≡ b
ℕ₊₁→ℕ-reflects-≡ (1+ a) (1+ b) p i = 1+ +ⁿ-preserves-≡ˡ {1} {a} {b} p i

ℚ-reflects-denom : ∀ z aⁿ bⁿ → [ z #ᶻ 0 ] → [ z / aⁿ ] ≡ [ z / bⁿ ] → aⁿ ≡ bⁿ
ℚ-reflects-denom z aⁿ bⁿ z#0 p = ℕ₊₁→ℕ-reflects-≡ aⁿ bⁿ (sym γ) where
  κ : absᶻ z ·ⁿ (ℕ₊₁→ℕ bⁿ) ≡ absᶻ z ·ⁿ (ℕ₊₁→ℕ aⁿ)
  κ i = absᶻ (eq/⁻¹ _ _ p i)
  φ : (z#0 : [ z #ᶻ 0 ]) → [ 0 <ⁿ absᶻ z ]
  φ (inl z<0) = let (n , z≡-sn) = <ᶻ-split-neg z z<0 in transport (λ i → [ 0 <ⁿ absᶻ (z≡-sn (~ i)) ]) (0<ⁿsuc n)
  φ (inr 0<z) = let (n , z≡+sn) = <ᶻ-split-pos z 0<z in transport (λ i → [ 0 <ⁿ absᶻ (z≡+sn (~ i)) ]) (0<ⁿsuc n)
  γ : ℕ₊₁→ℕ bⁿ ≡ ℕ₊₁→ℕ aⁿ
  γ = ·ⁿ-reflects-≡ˡ (ℕ₊₁→ℕ bⁿ) (ℕ₊₁→ℕ aⁿ) (absᶻ z) (φ z#0) κ

-- already have this in QuoInt
pos-reflects-≡ : ∀ a b → pos a ≡ pos b → a ≡ b
pos-reflects-≡ a b p i = absᶻ (p i)

snotz' : ∀ n → ¬ᵗ (suc n ≡ 0)
snotz' n p = let caseNat = λ{ 0 → ⊥⊥ ; (suc n) → ℕ } in subst caseNat p 0

¬0≡1ⁿ : ¬ᵗ _≡_ {A = ℕ} 0 1
¬0≡1ⁿ p = snotzⁿ {0} (sym p)

¬0≡1ᶻ : ¬ᵗ _≡_ {A = ℤ} 0 1
¬0≡1ᶻ p = ¬0≡1ⁿ $ pos-reflects-≡ 0 1 p

¬0≡1ᶠ : ¬ᵗ _≡_ {A = ℚ} 0 1
¬0≡1ᶠ p = ¬0≡1ᶻ $ ℚ-reflects-nom 0 1 1 p

-- already have this in ᶻ
signed0≡0 : ∀ s → signed s 0 ≡ 0
signed0≡0 spos   = refl
signed0≡0 sneg i = posneg (~ i)

·-nullifiesˡ' : ∀ bᶻ bⁿ → 0 · [ bᶻ / bⁿ ] ≡ 0
·-nullifiesˡ' bᶻ bⁿ =
  [ signed (signᶻ bᶻ) 0 / (1+ (ℕ₊₁.n bⁿ +ⁿ 0)) ] ≡⟨ cong₂ [_/_] (signed0≡0 (signᶻ bᶻ)) refl ⟩
  [                   0 / (1+ (ℕ₊₁.n bⁿ +ⁿ 0)) ] ≡⟨ zeroᶠ (1+ (ℕ₊₁.n bⁿ +ⁿ 0)) ⟩
  [                   0 / (1+ 0)               ] ∎

·-nullifiesʳ' : ∀ bᶻ bⁿ → [ bᶻ / bⁿ ] · 0 ≡ 0
·-nullifiesʳ' bᶻ bⁿ = ·-comm [ bᶻ / bⁿ ] 0 ∙ ·-nullifiesˡ' bᶻ bⁿ

·-inv-<ᶻ' : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) : ℤ × ℕ₊₁) → ([ a ]ᶠ · [ b ]ᶠ ≡ 1) → [ (0 <ᶻ aᶻ) ⊓ (0 <ᶻ bᶻ) ] ⊎ [ (aᶻ <ᶻ 0) ⊓ (bᶻ <ᶻ 0) ]
·-inv-<ᶻ' a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p = γ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  κ = ([ aᶻ /  aⁿ ] · [ bᶻ /   bⁿ ] ≡ [     1      /   (1+ 0)  ] ⇒⟨ transport (cong₂ _≡_ refl (transport (λ i → 1 ≡ [ ·ᶻ-identity aⁿᶻ .snd i / ·₊₁-identityˡ aⁿ i ]) (expand-fraction 1 1 aⁿ) ∙ expand-fraction aⁿᶻ aⁿ bⁿ)) ⟩
       [ aᶻ ·ᶻ bᶻ   /   aⁿ ·₊₁ bⁿ ] ≡ [ aⁿᶻ ·ᶻ bⁿᶻ / aⁿ ·₊₁ bⁿ ] ⇒⟨ ℚ-reflects-nom _ _ (aⁿ ·₊₁ bⁿ) ⟩
         aᶻ ·ᶻ bᶻ                   ≡   aⁿᶻ ·ᶻ bⁿᶻ               ◼) p
  φ₀ : [ 0 <ⁿ ((ℕ₊₁→ℕ aⁿ) ·ⁿ (ℕ₊₁→ℕ bⁿ)) ]
  φ₀ = 0<ⁿsuc _
  φ₁ : [ 0 <ᶻ aⁿᶻ ·ᶻ bⁿᶻ ]
  φ₁ = φ₀
  φ₂ : [ 0 <ᶻ aᶻ  ·ᶻ bᶻ  ]
  φ₂ = subst (λ p → [ 0 <ᶻ p ]) (sym κ) φ₁
  γ : [ (0 <ᶻ aᶻ) ⊓ (0 <ᶻ bᶻ) ] ⊎ [ (aᶻ <ᶻ 0) ⊓ (bᶻ <ᶻ 0) ]
  γ with <ᶻ-tricho 0 aᶻ
  ... | inl (inl 0<aᶻ) = inl (0<aᶻ , ·ᶻ-reflects-0<ᶻ aᶻ bᶻ φ₂ .fst .fst 0<aᶻ)
  ... | inl (inr aᶻ<0) = inr (aᶻ<0 , ·ᶻ-reflects-0<ᶻ aᶻ bᶻ φ₂ .snd .fst aᶻ<0)
  ... | inr      0≡aᶻ  = ⊥-elim {A = λ _ → [ (0 <ᶻ aᶻ) ⊓ (0 <ᶻ bᶻ) ] ⊎ [ (aᶻ <ᶻ 0) ⊓ (bᶻ <ᶻ 0) ]} (¬0≡1ᶠ η) where
    η =   0                      ≡⟨ sym $ zeroᶠ (aⁿ ·₊₁ bⁿ) ⟩
        [ 0        / aⁿ ·₊₁ bⁿ ] ≡⟨ (λ i → [ ·ᶻ-nullifiesˡ bᶻ (~ i) / aⁿ ·₊₁ bⁿ ]) ⟩
        [ 0  ·ᶻ bᶻ / aⁿ ·₊₁ bⁿ ] ≡⟨ (λ i → [ 0≡aᶻ i ·ᶻ bᶻ / aⁿ ·₊₁ bⁿ ]) ⟩
        [ aᶻ ·ᶻ bᶻ / aⁿ ·₊₁ bⁿ ] ≡⟨ p ⟩
          1                      ∎

private
  lem0<ᶻ : ∀ aᶻ → [ 0 <ᶻ aᶻ ] → aᶻ ≡ signed (signᶻ aᶻ ⊕ spos) (absᶻ aᶻ ·ⁿ 1)
  lem0<ᶻ aᶻ 0<aᶻ =
    aᶻ                                                            ≡⟨ γ ⟩
    pos (suc n)                                                   ≡⟨ (λ i → pos (suc (·ⁿ-identityʳ n (~ i)))) ⟩
    pos (suc (n ·ⁿ 1))                                            ≡⟨ refl ⟩
    signed (signᶻ (pos (suc n)) ⊕ spos) (absᶻ (pos (suc n)) ·ⁿ 1) ≡⟨ (λ i → signed (signᶻ (γ (~ i)) ⊕ spos) (absᶻ (γ (~ i)) ·ⁿ 1)) ⟩
    signed (signᶻ  aᶻ           ⊕ spos) (absᶻ  aᶻ           ·ⁿ 1) ∎ where
    abstract
      n = <ᶻ-split-pos aᶻ 0<aᶻ .fst
      γ : aᶻ ≡ pos (suc n)
      γ = <ᶻ-split-pos aᶻ 0<aᶻ .snd

  lem<ᶻ0 : ∀ aᶻ → [ aᶻ <ᶻ 0  ] → aᶻ ≡ signed (signᶻ aᶻ ⊕ spos) (absᶻ aᶻ ·ⁿ 1)
  lem<ᶻ0 aᶻ aᶻ<0 =
    aᶻ                                                            ≡⟨ γ ⟩
    neg (suc n)                                                   ≡⟨ (λ i → neg (suc (·ⁿ-identityʳ n (~ i)))) ⟩
    neg (suc (n ·ⁿ 1))                                            ≡⟨ refl ⟩
    signed (signᶻ (neg (suc n)) ⊕ spos) (absᶻ (neg (suc n)) ·ⁿ 1) ≡⟨ (λ i → signed (signᶻ (γ (~ i)) ⊕ spos) (absᶻ (γ (~ i)) ·ⁿ 1)) ⟩
    signed (signᶻ  aᶻ           ⊕ spos) (absᶻ  aᶻ           ·ⁿ 1) ∎ where
    abstract
      n = <ᶻ-split-neg aᶻ aᶻ<0 .fst
      γ : aᶻ ≡ neg (suc n)
      γ = <ᶻ-split-neg aᶻ aᶻ<0 .snd

·-inv#0' : (a b : ℤ × ℕ₊₁) → ([ a ]ᶠ · [ b ]ᶠ ≡ 1) → [ [ a ]ᶠ # 0 ⊓ [ b ]ᶠ # 0 ]
·-inv#0' a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p with ·-inv-<ᶻ' a b p
... | inl (0<aᶻ , 0<bᶻ) = inr (subst (λ p → [ 0 <ᶻ p ]) (lem0<ᶻ aᶻ 0<aᶻ) 0<aᶻ)
                        , inr (subst (λ p → [ 0 <ᶻ p ]) (lem0<ᶻ bᶻ 0<bᶻ) 0<bᶻ)
... | inr (aᶻ<0 , bᶻ<0) = inl (subst (λ p → [ p <ᶻ 0 ]) (lem<ᶻ0 aᶻ aᶻ<0) aᶻ<0)
                        , inl (subst (λ p → [ p <ᶻ 0 ]) (lem<ᶻ0 bᶻ bᶻ<0) bᶻ<0)

·-inv#0 : ∀ x y → x · y ≡ 1 → [(x # 0) ⊓ (y # 0)]
·-inv#0 = let P : ℚ → ℚ → hProp ℓ-zero
              P x y = ([ isSetℚ ] (x · y) ≡ˢ 1) ⇒ ((x # 0) ⊓ (y # 0))
          in  SetQuotient.elimProp2 {R = _∼_} {C = λ x y → [ P x y ]} (λ x y → isProp[] (P x y)) ·-inv#0'

·-inv#0ˡ' : (a b : ℤ × ℕ₊₁) → ([ a ]ᶠ · [ b ]ᶠ ≡ 1) → [ [ a ]ᶠ # 0 ]
·-inv#0ˡ' a b p = ·-inv#0' a b p .fst

·-inv#0ˡ : ∀ x y → x · y ≡ 1 → [ x # 0 ]
·-inv#0ˡ x y p = ·-inv#0 x y p .fst

-- ·-reflects-signʳ : ∀ a b c → [ 0 < c ] → a · b ≡ c → [ ((0 < b) ⇒ (0 < a)) ⊓ ((b < 0) ⇒ (a < 0)) ]
-- ·-reflects-signʳ a b c p q .fst 0<b = {!   !}
-- ·-reflects-signʳ a b c p q .snd b<0 = {!   !}
-- ⁻¹-preserves-sign : ∀ z z⁻¹ → [ 0f < z ] → z · z⁻¹ ≡ 1f → [ 0f < z⁻¹ ]
-- ⁻¹-preserves-sign z z⁻¹

-- -- TODO: this is a plain copy from `MorePropAlgebra.Properties.AlmostPartiallyOrderedField`
-- --       we might put it into `MorePropAlgebra.Consequences`
-- -- uniqueness of inverses from `·-assoc` + `·-comm` + `·-lid` + `·-rid`
-- ·-rinv-unique'' : (x y z : F) → [ x · y ≡ˢ 1f ] → [ x · z ≡ˢ 1f ] → [ y ≡ˢ z ]
-- ·-rinv-unique'' x y z x·y≡1 x·z≡1 =
--   (      x  · y  ≡ˢ     1f ⇒ᵖ⟨ (λ x·y≡1 i → z · x·y≡1 i) ⟩
--     z · (x  · y) ≡ˢ z · 1f ⇒ᵖ⟨ pathTo⇒ (λ i → ·-assoc z x y i ≡ˢ ·-rid z i) ⟩
--    (z ·  x) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → (·-comm z x i) · y  ≡ˢ z) ⟩
--    (x ·  z) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → x·z≡1 i · y  ≡ˢ z) ⟩
--       1f    · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → ·-lid y i ≡ˢ z) ⟩
--               y  ≡ˢ z      ◼ᵖ) .snd x·y≡1

·-inv'' : ∀ x → [ (∃[ y ] ([ isSetℚ ] (x · y) ≡ˢ 1)) ⇔ (x # 0) ]
·-inv'' x .fst p = ∣∣-elim (λ _ → φ') (λ{ (y , q) → γ y q } ) p where
  φ' = isProp[] (x # 0)
  γ : ∀ y → [ [ isSetℚ ] (x · y) ≡ˢ 1 ] → [ x # 0 ]
  γ y q = ·-inv#0ˡ x y q
·-inv'' x .snd p = ∣ (x ⁻¹) {{p}} , ·-invʳ x p ∣

-- -- note, that the following holds definitionally (TODO: put this at the definition of `min`)
-- _ =    min [ aᶻ , aⁿ ]ᶠ [ bᶻ , bⁿ ]ᶠ                 ≡⟨ refl ⟩
--     [ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ  ∎
-- -- and we also have definitionally
-- _ : [1+ aⁿ *₊₁ bⁿ ⁿ]ᶻ ≡ aⁿᶻ *ᶻ bⁿᶻ
-- _ = refl
-- -- therefore, we have for the LHS:
-- _ = ([ cᶻ , cⁿ ]ᶠ ≤ min [ aᶻ , aⁿ ]ᶠ [ bᶻ , bⁿ ]ᶠ)                      ≡⟨ refl ⟩
--     ([ cᶻ , cⁿ ]ᶠ ≤ [ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ)    ≡⟨ refl ⟩
--     (¬([ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ < [ cᶻ , cⁿ ]ᶠ)) ≡⟨ refl ⟩
--     ¬((minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ) <ᶻ (cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)))    ≡⟨ refl ⟩
--     ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ))     ∎
-- -- similar for the RHS:
-- _ =  ([ cᶻ , cⁿ ]ᶠ ≤ [ aᶻ , aⁿ ]ᶠ) ⊓  ([ cᶻ , cⁿ ]ᶠ ≤ [ bᶻ , bⁿ ]ᶠ) ≡⟨ refl ⟩
--     ¬([ aᶻ , aⁿ ]ᶠ < [ cᶻ , cⁿ ]ᶠ) ⊓ ¬([ bᶻ , bⁿ ]ᶠ < [ cᶻ , cⁿ ]ᶠ) ≡⟨ refl ⟩
--     ¬((aᶻ *ᶻ cⁿᶻ)  <ᶻ (cᶻ *ᶻ aⁿᶻ)) ⊓ ¬((bᶻ *ᶻ cⁿᶻ)  <ᶻ (cᶻ *ᶻ bⁿᶻ)) ≡⟨ refl ⟩
--      ((cᶻ *ᶻ aⁿᶻ)  ≤ᶻ (aᶻ *ᶻ cⁿᶻ)) ⊓  ((cᶻ *ᶻ bⁿᶻ)  ≤ᶻ (bᶻ *ᶻ cⁿᶻ)) ∎
-- -- therfore, only properties on ℤ remain
-- RHS = [ ((cᶻ *ᶻ aⁿᶻ)  ≤ᶻ (aᶻ *ᶻ cⁿᶻ)) ⊓  ((cᶻ *ᶻ bⁿᶻ)  ≤ᶻ (bᶻ *ᶻ cⁿᶻ)) ]
-- LHS = [ ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ)) ]
-- strategy: multiply everything with aⁿᶻ, bⁿᶻ, cⁿᶻ

is-min : (x y z : ℚ) → [ (z ≤ min x y) ⇔ (z ≤ x) ⊓ (z ≤ y) ]
is-min = SetQuotient.elimProp3  {R = _∼_} (λ x y z → isProp[] ((z ≤ min x y) ⇔ (z ≤ x) ⊓ (z ≤ y))) γ where
  γ : (a b c : ℤ × ℕ₊₁) → [ ([ c ]ᶠ ≤ min [ a ]ᶠ [ b ]ᶠ) ⇔ ([ c ]ᶠ ≤ [ a ]ᶠ) ⊓ ([ c ]ᶠ ≤ [ b ]ᶠ) ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = pathTo⇔ (sym κ) where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ; 0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]; 0≤aⁿᶻ = is-0≤ⁿᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ; 0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]; 0≤bⁿᶻ = is-0≤ⁿᶻ
    cⁿᶻ = [1+ cⁿ ⁿ]ᶻ; 0≤cⁿᶻ : [ 0 ≤ᶻ cⁿᶻ ]; 0≤cⁿᶻ = is-0≤ⁿᶻ
    κ = (
      ((cᶻ ·ᶻ aⁿᶻ)         ≤ᶻ (aᶻ ·ᶻ cⁿᶻ)        ) ⊓ ((cᶻ ·ᶻ bⁿᶻ)         ≤ᶻ (bᶻ ·ᶻ cⁿᶻ)        ) ≡⟨ ⊓≡⊓ (·ᶻ-creates-≤ᶻ-≡ (cᶻ ·ᶻ aⁿᶻ) (aᶻ ·ᶻ cⁿᶻ) bⁿᶻ 0≤bⁿᶻ) (·ᶻ-creates-≤ᶻ-≡ (cᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ cⁿᶻ) aⁿᶻ 0≤aⁿᶻ) ⟩
      ((cᶻ ·ᶻ aⁿᶻ) ·ᶻ bⁿᶻ  ≤ᶻ (aᶻ ·ᶻ cⁿᶻ) ·ᶻ bⁿᶻ ) ⊓ ((cᶻ ·ᶻ bⁿᶻ) ·ᶻ aⁿᶻ  ≤ᶻ (bᶻ ·ᶻ cⁿᶻ) ·ᶻ aⁿᶻ ) ≡⟨ ⊓≡⊓ (λ i → ·ᶻ-assoc cᶻ aⁿᶻ bⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc aᶻ cⁿᶻ bⁿᶻ (~ i)) (λ i → ·ᶻ-assoc cᶻ bⁿᶻ aⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc bᶻ cⁿᶻ aⁿᶻ (~ i)) ⟩
      ( cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ) ≤ᶻ  aᶻ ·ᶻ (cⁿᶻ ·ᶻ bⁿᶻ)) ⊓ ( cᶻ ·ᶻ (bⁿᶻ ·ᶻ aⁿᶻ) ≤ᶻ  bᶻ ·ᶻ (cⁿᶻ ·ᶻ aⁿᶻ)) ≡⟨ ⊓≡⊓ (λ i → cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ) ≤ᶻ  aᶻ ·ᶻ (·ᶻ-comm cⁿᶻ bⁿᶻ i)) (λ i → cᶻ ·ᶻ (·ᶻ-comm bⁿᶻ aⁿᶻ i) ≤ᶻ  bᶻ ·ᶻ (·ᶻ-comm cⁿᶻ aⁿᶻ i)) ⟩
      ( cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ) ≤ᶻ  aᶻ ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ)) ⊓ ( cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ) ≤ᶻ  bᶻ ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ)) ≡⟨ sym $ ⇔toPath' $ is-minᶻ (aᶻ ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ)) (bᶻ ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ)) (cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⟩
      ((cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≤ᶻ  minᶻ ( aᶻ ·ᶻ (bⁿᶻ  ·ᶻ cⁿᶻ)) (bᶻ ·ᶻ (aⁿᶻ  ·ᶻ cⁿᶻ)))                ≡⟨ (λ i → ((cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≤ᶻ minᶻ (·ᶻ-assoc aᶻ bⁿᶻ cⁿᶻ i) (·ᶻ-assoc bᶻ aⁿᶻ cⁿᶻ i))) ⟩
      ((cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≤ᶻ  minᶻ ((aᶻ ·ᶻ  bⁿᶻ) ·ᶻ cⁿᶻ) ((bᶻ ·ᶻ  aⁿᶻ) ·ᶻ cⁿᶻ))                 ≡⟨ (λ i → (cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≤ᶻ ·ᶻ-minᶻ-distribʳ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) cⁿᶻ 0≤cⁿᶻ (~ i)) ⟩
      ((cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≤ᶻ (minᶻ ( aᶻ ·ᶻ  bⁿᶻ)          (bᶻ ·ᶻ  aⁿᶻ)           ·ᶻ cⁿᶻ))       ∎)

is-max : (x y z : ℚ) → [ (max x y ≤ z) ⇔ (x ≤ z) ⊓ (y ≤ z) ]
is-max = SetQuotient.elimProp3  {R = _∼_} (λ x y z → isProp[] ((max x y ≤ z) ⇔ (x ≤ z) ⊓ (y ≤ z))) γ where
  γ : (a b c : ℤ × ℕ₊₁) → [ (max [ a ]ᶠ [ b ]ᶠ ≤ [ c ]ᶠ) ⇔ ([ a ]ᶠ ≤ [ c ]ᶠ) ⊓ ([ b ]ᶠ ≤ [ c ]ᶠ) ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = pathTo⇔ (sym κ) where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ; 0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]; 0≤aⁿᶻ = is-0≤ⁿᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ; 0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]; 0≤bⁿᶻ = is-0≤ⁿᶻ
    cⁿᶻ = [1+ cⁿ ⁿ]ᶻ; 0≤cⁿᶻ : [ 0 ≤ᶻ cⁿᶻ ]; 0≤cⁿᶻ = is-0≤ⁿᶻ
    κ = ( aᶻ ·ᶻ cⁿᶻ         ≤ᶻ  cᶻ ·ᶻ aⁿᶻ        ) ⊓ ( bᶻ ·ᶻ cⁿᶻ         ≤ᶻ  cᶻ ·ᶻ bⁿᶻ        ) ≡⟨ ⊓≡⊓ (·ᶻ-creates-≤ᶻ-≡ (aᶻ ·ᶻ cⁿᶻ) (cᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0≤bⁿᶻ) (·ᶻ-creates-≤ᶻ-≡ (bᶻ ·ᶻ cⁿᶻ) (cᶻ ·ᶻ bⁿᶻ) aⁿᶻ 0≤aⁿᶻ) ⟩
        ((aᶻ ·ᶻ cⁿᶻ) ·ᶻ bⁿᶻ ≤ᶻ (cᶻ ·ᶻ aⁿᶻ) ·ᶻ bⁿᶻ) ⊓ ((bᶻ ·ᶻ cⁿᶻ) ·ᶻ aⁿᶻ ≤ᶻ (cᶻ ·ᶻ bⁿᶻ) ·ᶻ aⁿᶻ) ≡⟨ ⊓≡⊓ (λ i → ·ᶻ-assoc aᶻ cⁿᶻ bⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc cᶻ aⁿᶻ bⁿᶻ (~ i)) (λ i → ·ᶻ-assoc bᶻ cⁿᶻ aⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc cᶻ bⁿᶻ aⁿᶻ (~ i)) ⟩
        (aᶻ ·ᶻ (cⁿᶻ ·ᶻ bⁿᶻ) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⊓ (bᶻ ·ᶻ (cⁿᶻ ·ᶻ aⁿᶻ) ≤ᶻ cᶻ ·ᶻ (bⁿᶻ ·ᶻ aⁿᶻ)) ≡⟨ ⊓≡⊓ (λ i → aᶻ ·ᶻ ·ᶻ-comm cⁿᶻ bⁿᶻ i ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) (λ i → bᶻ ·ᶻ ·ᶻ-comm cⁿᶻ aⁿᶻ i ≤ᶻ cᶻ ·ᶻ ·ᶻ-comm bⁿᶻ aⁿᶻ i) ⟩
        (aᶻ ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⊓ (bᶻ ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ≡⟨ sym $ ⇔toPath' $ is-maxᶻ (aᶻ ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ)) (bᶻ ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ)) (cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⟩
        maxᶻ (aᶻ ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ)) (bᶻ ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ)) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)                    ≡⟨ (λ i → maxᶻ (·ᶻ-assoc aᶻ bⁿᶻ cⁿᶻ i) (·ᶻ-assoc bᶻ aⁿᶻ cⁿᶻ i) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⟩
        maxᶻ ((aᶻ ·ᶻ bⁿᶻ) ·ᶻ cⁿᶻ) ((bᶻ ·ᶻ aⁿᶻ) ·ᶻ cⁿᶻ) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)                    ≡⟨ (λ i → ·ᶻ-maxᶻ-distribʳ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) cⁿᶻ 0≤cⁿᶻ (~ i) ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ)) ⟩
        maxᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) ·ᶻ cⁿᶻ ≤ᶻ cᶻ ·ᶻ (aⁿᶻ ·ᶻ bⁿᶻ) ∎

private
  lem2  : ∀ a b c d → (a ·ᶻ c) ·ᶻ (b ·ᶻ d) ≡ (a ·ᶻ b) ·ᶻ (c ·ᶻ d)
  lem2' : ∀ a b c d → (a ·ᶻ c) ·ᶻ (b ·ᶻ d) ≡ (a ·ᶻ b) ·ᶻ (d ·ᶻ c)
  lem3  : ∀ a b c d → (a ·ᶻ c) ·ᶻ (b ·ᶻ d) ≡ (a ·ᶻ d) ·ᶻ (c ·ᶻ b)
  lem3' : ∀ a b c d → (a ·ᶻ c) ·ᶻ (b ·ᶻ d) ≡ (a ·ᶻ d) ·ᶻ (b ·ᶻ c)

  lem2  a b c d = ·ᶻ-commʳ a c (b ·ᶻ d) ∙ (λ i → ·ᶻ-assoc a b d i ·ᶻ c) ∙ sym (·ᶻ-assoc (a ·ᶻ b) d c) ∙ (λ i → (a ·ᶻ b) ·ᶻ ·ᶻ-comm d c i)
  lem2' a b c d = lem2 a b c d ∙ λ i → (a ·ᶻ b) ·ᶻ ·ᶻ-comm c d i
  lem3  a b c d = (λ i → a ·ᶻ c ·ᶻ ·ᶻ-comm b d i) ∙ sym (·ᶻ-assoc a c (d ·ᶻ b)) ∙ (λ i → a ·ᶻ ·ᶻ-commˡ c d b i) ∙ ·ᶻ-assoc a d (c ·ᶻ b)
  lem3' a b c d = lem3 a b c d ∙ λ i → (a ·ᶻ d) ·ᶻ ·ᶻ-comm c b i

·-preserves-< : (x y z : ℚ) → [ 0 < z ] → [ x < y ] → [ x · z < y · z ]
·-preserves-< = SetQuotient.elimProp3 {R = _∼_} (λ x y z → isProp[] ((0 < z) ⇒ (x < y) ⇒ (x · z < y · z))) γ where
  γ : (a b c : ℤ × ℕ₊₁) → [ 0 < [ c ]ᶠ ] → [ [ a ]ᶠ < [ b ]ᶠ ] → [ [ a ]ᶠ · [ c ]ᶠ < [ b ]ᶠ · [ c ]ᶠ ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    cⁿᶻ = [1+ cⁿ ⁿ]ᶻ; 0<cⁿᶻ : [ 0 <ᶻ cⁿᶻ ]; 0<cⁿᶻ = is-0<ⁿᶻ
    κ : [ 0 ·ᶻ cⁿᶻ <ᶻ cᶻ ·ᶻ 1 ] → [ aᶻ ·ᶻ bⁿᶻ <ᶻ bᶻ ·ᶻ aⁿᶻ ] → [ (aᶻ ·ᶻ cᶻ) ·ᶻ (bⁿᶻ ·ᶻ cⁿᶻ) <ᶻ (bᶻ ·ᶻ cᶻ) ·ᶻ (aⁿᶻ ·ᶻ cⁿᶻ) ]
    κ p q = transport (λ i → [ lem2 aᶻ bⁿᶻ cᶻ cⁿᶻ (~ i) <ᶻ lem2 bᶻ aⁿᶻ cᶻ cⁿᶻ (~ i) ]) $ ·ᶻ-preserves-<ᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) (cᶻ ·ᶻ cⁿᶻ) 0<cᶻ·cⁿᶻ q where
      0<cᶻ : [ 0 <ᶻ cᶻ ]
      0<cᶻ = transport (λ i → [ ·ᶻ-nullifiesˡ cⁿᶻ i <ᶻ ·ᶻ-identity cᶻ .fst i ]) p
      0<cᶻ·cⁿᶻ : [ 0 <ᶻ (cᶻ ·ᶻ cⁿᶻ) ]
      0<cᶻ·cⁿᶻ = ·ᶻ-preserves-0<ᶻ cᶻ cⁿᶻ 0<cᶻ 0<cⁿᶻ

private
  -- continuing the pattern...
  elimProp4 : ∀{ℓ} {A : Type ℓ} → {R : A → A → Type ℓ}
            → {E : A SetQuotient./ R → A SetQuotient./ R → A SetQuotient./ R → A SetQuotient./ R → Type ℓ}
            → ((x y z w : A SetQuotient./ R ) → isProp (E x y z w))
            → ((a b c d : A) → E SetQuotient.[ a ] SetQuotient.[ b ] SetQuotient.[ c ] SetQuotient.[ d ])
            → (x y z w : A SetQuotient./ R)
            → E x y z w
  elimProp4 Eprop f = SetQuotient.elimProp (λ x → isPropΠ3 (λ y z w → Eprop x y z w))
                                           (λ x → SetQuotient.elimProp3 (λ y z w → Eprop SetQuotient.[ x ] y z w) (f x))

open import Cubical.HITs.Rationals.QuoQ using
  ( _+_
  ; -_
  ; +-assoc
  ; +-comm
  ; +-identityˡ
  ; +-identityʳ
  ; +-inverseˡ
  ; +-inverseʳ
  ) renaming
  ( *-identityˡ to ·-identityˡ
  ; *-identityʳ to ·-identityʳ
  ; *-distribˡ  to ·-distribˡ
  ; *-distribʳ  to ·-distribʳ
  )

-- the following hold definitionally:
--       [ aᶻ , aⁿ ]ᶠ · [ bᶻ , bⁿ ]ᶠ ≡ [ aᶻ · bᶻ , aⁿ ·₊₁ bⁿ ]ᶠ
--       [ aᶻ , aⁿ ]ᶠ < [ bᶻ , bⁿ ]ᶠ ≡ aᶻ ·ᶻ bⁿᶻ <ᶻ bᶻ ·ᶻ aⁿᶻ
--   min [ aᶻ , aⁿ ]ᶠ   [ bᶻ , bⁿ ]ᶠ ≡ [ (minᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) , aⁿ ·₊₁ bⁿ) ]ᶠ
--       [ aᶻ , aⁿ ]ᶠ + [ bᶻ , bⁿ ]ᶠ ≡ [ aᶻ ·ᶻ bⁿᶻ +ᶻ bᶻ ·ᶻ aⁿᶻ , aⁿ ·₊₁ bⁿ ]ᶠ

+-<-ext : (w x y z : ℚ) → [ w + x < y + z ] → [ (w < y) ⊔ (x < z) ]
+-<-ext = elimProp4 {R = _∼_} (λ w x y z → isProp[] ((w + x < y + z) ⇒ ((w < y) ⊔ (x < z)))) γ where
  γ : (w x y z : ℤ × ℕ₊₁) → [ [ w ]ᶠ + [ x ]ᶠ < [ y ]ᶠ + [ z ]ᶠ ] → [ ([ w ]ᶠ < [ y ]ᶠ) ⊔ ([ x ]ᶠ < [ z ]ᶠ) ]
  γ w@(wᶻ , wⁿ) x@(xᶻ , xⁿ) y@(yᶻ , yⁿ) z@(zᶻ , zⁿ) = κ where
    wⁿᶻ = [1+ wⁿ ⁿ]ᶻ; 0<wⁿᶻ : [ 0 <ᶻ wⁿᶻ ]; 0<wⁿᶻ = is-0<ⁿᶻ
    xⁿᶻ = [1+ xⁿ ⁿ]ᶻ; 0<xⁿᶻ : [ 0 <ᶻ xⁿᶻ ]; 0<xⁿᶻ = is-0<ⁿᶻ
    yⁿᶻ = [1+ yⁿ ⁿ]ᶻ; 0<yⁿᶻ : [ 0 <ᶻ yⁿᶻ ]; 0<yⁿᶻ = is-0<ⁿᶻ
    zⁿᶻ = [1+ zⁿ ⁿ]ᶻ; 0<zⁿᶻ : [ 0 <ᶻ zⁿᶻ ]; 0<zⁿᶻ = is-0<ⁿᶻ
    0<xzⁿᶻ : [ 0 <ᶻ xⁿᶻ ·ᶻ zⁿᶻ ]; 0<xzⁿᶻ = ·ᶻ-preserves-0<ᶻ xⁿᶻ zⁿᶻ 0<xⁿᶻ 0<zⁿᶻ
    0<wyⁿᶻ : [ 0 <ᶻ wⁿᶻ ·ᶻ yⁿᶻ ]; 0<wyⁿᶻ = ·ᶻ-preserves-0<ᶻ wⁿᶻ yⁿᶻ 0<wⁿᶻ 0<yⁿᶻ
    φ₁ = wᶻ ·ᶻ xⁿᶻ ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ) ≡⟨ lem2  wᶻ yⁿᶻ xⁿᶻ zⁿᶻ ⟩ wᶻ ·ᶻ yⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ) ∎
    φ₂ = xᶻ ·ᶻ wⁿᶻ ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ) ≡⟨ lem3  xᶻ yⁿᶻ wⁿᶻ zⁿᶻ ⟩ xᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ) ∎
    φ₃ = yᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) ≡⟨ lem2' yᶻ wⁿᶻ zⁿᶻ xⁿᶻ ⟩ yᶻ ·ᶻ wⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ) ∎
    φ₄ = zᶻ ·ᶻ yⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) ≡⟨ lem3' zᶻ wⁿᶻ yⁿᶻ xⁿᶻ ⟩ zᶻ ·ᶻ xⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ) ∎
    φ = (    (wᶻ ·ᶻ xⁿᶻ +ᶻ xᶻ ·ᶻ wⁿᶻ) ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ)
          <ᶻ (yᶻ ·ᶻ zⁿᶻ +ᶻ zᶻ ·ᶻ yⁿᶻ) ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) ⇒ᵖ⟨ transport (λ i → [ is-distᶻ (wᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ wⁿᶻ) (yⁿᶻ ·ᶻ zⁿᶻ) .snd i <ᶻ is-distᶻ (yᶻ ·ᶻ zⁿᶻ) (zᶻ ·ᶻ yⁿᶻ) (wⁿᶻ ·ᶻ xⁿᶻ) .snd i ]) ⟩
             wᶻ ·ᶻ xⁿᶻ ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ) +ᶻ xᶻ ·ᶻ wⁿᶻ ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ)
          <ᶻ yᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) +ᶻ zᶻ ·ᶻ yⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) ⇒ᵖ⟨ transport (λ i → [ φ₁ i +ᶻ φ₂ i <ᶻ φ₃ i +ᶻ φ₄ i ]) ⟩
             wᶻ ·ᶻ yⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ) +ᶻ xᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ)
          <ᶻ yᶻ ·ᶻ wⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ) +ᶻ zᶻ ·ᶻ xⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ) ◼ᵖ) .snd
    P₁ = wᶻ ·ᶻ yⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ) <ᶻ yᶻ ·ᶻ wⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ)
    P₂ = xᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ) <ᶻ zᶻ ·ᶻ xⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ)
    Q₁ = wᶻ ·ᶻ yⁿᶻ <ᶻ yᶻ ·ᶻ wⁿᶻ
    Q₂ = xᶻ ·ᶻ zⁿᶻ <ᶻ zᶻ ·ᶻ xⁿᶻ
    ψ = +ᶻ-<ᶻ-ext (wᶻ ·ᶻ yⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ)) (xᶻ ·ᶻ zⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ)) (yᶻ ·ᶻ wⁿᶻ ·ᶻ (xⁿᶻ ·ᶻ zⁿᶻ)) (zᶻ ·ᶻ xⁿᶻ ·ᶻ (wⁿᶻ ·ᶻ yⁿᶻ))
    κ : [ (wᶻ ·ᶻ xⁿᶻ +ᶻ xᶻ ·ᶻ wⁿᶻ) ·ᶻ (yⁿᶻ ·ᶻ zⁿᶻ) <ᶻ (yᶻ ·ᶻ zⁿᶻ +ᶻ zᶻ ·ᶻ yⁿᶻ) ·ᶻ (wⁿᶻ ·ᶻ xⁿᶻ) ]
      → [ Q₁ ⊔ Q₂ ]
    κ p =  case ψ (φ p) as P₁ ⊔ P₂ ⇒ (Q₁ ⊔ Q₂) of λ
      { (inl q) → inlᵖ (·ᶻ-reflects-<ᶻ (wᶻ ·ᶻ yⁿᶻ) (yᶻ ·ᶻ wⁿᶻ) (xⁿᶻ ·ᶻ zⁿᶻ) 0<xzⁿᶻ q)
      ; (inr q) → inrᵖ (·ᶻ-reflects-<ᶻ (xᶻ ·ᶻ zⁿᶻ) (zᶻ ·ᶻ xⁿᶻ) (wⁿᶻ ·ᶻ yⁿᶻ) 0<wyⁿᶻ q)
      }

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℚ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _·_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℚ
·-Semigroup .IsSemigroup.is-assoc = ·-assoc

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup  = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-identityʳ x , +-identityˡ x

·-Monoid : [ isMonoid 1 _·_ ]
·-Monoid .IsMonoid.is-Semigroup  = ·-Semigroup
·-Monoid .IsMonoid.is-identity x = ·-identityʳ x , ·-identityˡ x

is-Semiring : [ isSemiring 0 1 _+_ _·_ ]
is-Semiring .IsSemiring.+-Monoid = +-Monoid
is-Semiring .IsSemiring.·-Monoid = ·-Monoid
is-Semiring .IsSemiring.+-comm   = +-comm
is-Semiring .IsSemiring.is-dist x y z = sym (·-distribˡ x y z) , sym (·-distribʳ x y z)

is-CommSemiring : [ isCommSemiring 0 1 _+_ _·_ ]
is-CommSemiring .IsCommSemiring.is-Semiring = is-Semiring
is-CommSemiring .IsCommSemiring.·-comm      = ·-comm

≤-Lattice : [ isLattice _≤_ min max ]
≤-Lattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-Lattice .IsLattice.is-min         = is-min
≤-Lattice .IsLattice.is-max         = is-max

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _·_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-Lattice           = ≤-Lattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = +-<-ext
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = ·-preserves-<

+-inverse : (x : ℚ) → (x + (- x) ≡ 0) × ((- x) + x ≡ 0)
+-inverse x .fst = +-inverseʳ x
+-inverse x .snd = +-inverseˡ x

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _·_ -_ _<_ min max ]
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.+-inverse                      = +-inverse

is-LinearlyOrderedField : [ isLinearlyOrderedField 0 1 _+_ _·_ -_ _<_ min max ]
is-LinearlyOrderedField .IsLinearlyOrderedField.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing
is-LinearlyOrderedField .IsLinearlyOrderedField.·-inv''                    = ·-inv''

ℚbundle : LinearlyOrderedField {ℓ-zero} {ℓ-zero}
ℚbundle .LinearlyOrderedField.Carrier                  = ℚ
ℚbundle .LinearlyOrderedField.0f                       = 0
ℚbundle .LinearlyOrderedField.1f                       = 1
ℚbundle .LinearlyOrderedField._+_                      = _+_
ℚbundle .LinearlyOrderedField.-_                       = -_
ℚbundle .LinearlyOrderedField._·_                      = _·_
ℚbundle .LinearlyOrderedField.min                      = min
ℚbundle .LinearlyOrderedField.max                      = max
ℚbundle .LinearlyOrderedField._<_                      = _<_
ℚbundle .LinearlyOrderedField.is-LinearlyOrderedField  = is-LinearlyOrderedField
