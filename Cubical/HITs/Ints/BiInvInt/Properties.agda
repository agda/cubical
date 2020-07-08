{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Ints.BiInvInt.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat hiding (_+_; +-comm)
open import Cubical.Data.Int
open import Cubical.Data.Bool

open import Cubical.HITs.Ints.BiInvInt.Base

-- addition

_+ᴮ_ : BiInvInt → BiInvInt → BiInvInt
m +ᴮ zero          = m
m +ᴮ suc n         = suc (m +ᴮ n)
m +ᴮ predr n       = predr (m +ᴮ n)
m +ᴮ predl n       = predl (m +ᴮ n)
m +ᴮ suc-predr n i = suc-predr (m +ᴮ n) i
m +ᴮ predl-suc n i = predl-suc (m +ᴮ n) i

-- properties of addition

+ᴮ-assoc : ∀ l m n → (l +ᴮ m) +ᴮ n ≡ l +ᴮ (m +ᴮ n)
+ᴮ-assoc l m zero i            = l +ᴮ m
+ᴮ-assoc l m (suc n) i         = suc (+ᴮ-assoc l m n i)
+ᴮ-assoc l m (predr n) i       = predr (+ᴮ-assoc l m n i)
+ᴮ-assoc l m (predl n) i       = predl (+ᴮ-assoc l m n i)
+ᴮ-assoc l m (suc-predr n i) j = suc-predr (+ᴮ-assoc l m n j) i
+ᴮ-assoc l m (predl-suc n i) j = predl-suc (+ᴮ-assoc l m n j) i

+ᴮ-unitʳ : ∀ n → n +ᴮ zero ≡ n
+ᴮ-unitʳ n i = n

+ᴮ-unitˡ : ∀ n → zero +ᴮ n ≡ n
+ᴮ-unitˡ zero i            = zero
+ᴮ-unitˡ (suc n) i         = suc (+ᴮ-unitˡ n i)
+ᴮ-unitˡ (predr n) i       = predr (+ᴮ-unitˡ n i)
+ᴮ-unitˡ (predl n) i       = predl (+ᴮ-unitˡ n i)
+ᴮ-unitˡ (suc-predr n i) j = suc-predr (+ᴮ-unitˡ n j) i
+ᴮ-unitˡ (predl-suc n i) j = predl-suc (+ᴮ-unitˡ n j) i

-- TODO: a direct proof of commutatitivty
-- (for now, we use Data.Int)

fwd-+≡+ᴮ : ∀ m n → fwd (m + n) ≡ (fwd m) +ᴮ (fwd n)
fwd-+≡+ᴮ m (pos zero)       = refl
fwd-+≡+ᴮ m (pos (suc n))    = fwd-sucInt (m +pos n) ∙ cong suc (fwd-+≡+ᴮ m (pos n))
fwd-+≡+ᴮ m (negsuc zero)    = fwd-predInt m
fwd-+≡+ᴮ m (negsuc (suc n)) = fwd-predInt (m +negsuc n) ∙ cong pred (fwd-+≡+ᴮ m (negsuc n))

+ᴮ≡+ : ∀ m n → m +ᴮ n ≡ fwd ((bwd m) + (bwd n))
+ᴮ≡+ m n = sym (fwd-+≡+ᴮ (bwd m) (bwd n) ∙ (λ i → (fwd-bwd m i) +ᴮ (fwd-bwd n i)))

+ᴮ-comm : ∀ m n → m +ᴮ n ≡ n +ᴮ m
+ᴮ-comm m n = +ᴮ≡+ m n ∙ cong fwd (+-comm (bwd m) (bwd n)) ∙ sym (+ᴮ≡+ n m)

-- some of the lemmas needed for a direct proof +ᴮ-comm are corollaries of +ᴮ-comm

suc-+ᴮ : ∀ m n → (suc m) +ᴮ n ≡ suc (m +ᴮ n)
suc-+ᴮ m n = +ᴮ-comm (suc m) n ∙ (λ i → suc (+ᴮ-comm n m i))
-- suc-+ᴮ m zero i    = suc m
-- suc-+ᴮ m (suc n) i = suc (suc-+ᴮ m n i)
-- suc-+ᴮ m (predr n) = cong predr (suc-+ᴮ m n) ∙ predr-suc (m +ᴮ n) ∙ sym (suc-predr (m +ᴮ n))
-- suc-+ᴮ m (predl n) = cong predl (suc-+ᴮ m n) ∙ predl-suc (m +ᴮ n) ∙ sym (suc-predl (m +ᴮ n))
-- suc-+ᴮ m (suc-predr n i) j = {!!}
-- suc-+ᴮ m (predl-suc n i) j = {!!}

predr-+ᴮ : ∀ m n → (predr m) +ᴮ n ≡ predr (m +ᴮ n)
predr-+ᴮ m n = +ᴮ-comm (predr m) n ∙ (λ i → predr (+ᴮ-comm n m i))

predl-+ᴮ : ∀ m n → (predl m) +ᴮ n ≡ predl (m +ᴮ n)
predl-+ᴮ m n = +ᴮ-comm (predl m) n ∙ (λ i → predl (+ᴮ-comm n m i))

-- +ᴮ-comm : ∀ m n → n +ᴮ m ≡ m +ᴮ n
-- +ᴮ-comm m zero              = +ᴮ-unitˡ m
-- +ᴮ-comm m (suc n)           =   suc-+ᴮ n m ∙ cong suc   (+ᴮ-comm m n)
-- +ᴮ-comm m (predr n)         = predr-+ᴮ n m ∙ cong predr (+ᴮ-comm m n)
-- +ᴮ-comm m (predl n)         = predl-+ᴮ n m ∙ cong predl (+ᴮ-comm m n)
-- +ᴮ-comm m (suc-predr n i) j = {!!}
-- +ᴮ-comm m (predl-suc n i) j = {!!}


-- negation / subtraction

-ᴮ_ : BiInvInt → BiInvInt
-ᴮ zero          = zero
-ᴮ suc n         = predl (-ᴮ n)
-ᴮ predr n       = suc (-ᴮ n)
-ᴮ predl n       = suc (-ᴮ n)
-ᴮ suc-predr n i = predl-suc (-ᴮ n) i
-ᴮ predl-suc n i = suc-predl (-ᴮ n) i

_-ᴮ_ : BiInvInt → BiInvInt → BiInvInt
m -ᴮ n = m +ᴮ (-ᴮ n)

-- TODO: properties of negation

-- +ᴮ-invˡ : ∀ n → (-ᴮ n) +ᴮ n ≡ zero
-- +ᴮ-invˡ zero              = refl
-- +ᴮ-invˡ (suc n)           = (λ i → suc (predl-+ᴮ (-ᴮ n) n i)) ∙ (λ i → suc-pred (+ᴮ-invˡ n i) i)
-- +ᴮ-invˡ (predr n)         = (λ i → predr (suc-+ᴮ (-ᴮ n) n i)) ∙ (λ i → predr-suc (+ᴮ-invˡ n i) i)
-- +ᴮ-invˡ (predl n)         = (λ i → predl (suc-+ᴮ (-ᴮ n) n i)) ∙ (λ i → predl-suc (+ᴮ-invˡ n i) i)
-- +ᴮ-invˡ (suc-predr n i) j = {!!}
-- +ᴮ-invˡ (predl-suc n i) j = {!!}

-- +ᴮ-invʳ : ∀ n → n +ᴮ (-ᴮ n) ≡ zero
-- +ᴮ-invʳ n = {!!}


-- natural injections from ℕ

posᴮ : ℕ → BiInvInt
posᴮ zero = zero
posᴮ (suc n) = suc (posᴮ n)

negᴮ : ℕ → BiInvInt
negᴮ zero = zero
negᴮ (suc n) = pred (negᴮ n)

-- absolute value and sign
-- (Note that there doesn't appear to be any way around using
--  bwd here! Any direct proof ends up doing the same work...)

absᴮ : BiInvInt → ℕ
absᴮ n = abs (bwd n)

sgnᴮ : BiInvInt → Bool
sgnᴮ n = sgn (bwd n)


-- TODO: a direct definition of multiplication using +ᴮ-invˡ/ʳ
-- (for now we use abs and sgn, as in agda's stdlib)

_*ᴮ_ : BiInvInt → BiInvInt → BiInvInt
m *ᴮ n = (if sgnᴮ m and sgnᴮ n then posᴮ else negᴮ) (absᴮ m * absᴮ n)
-- m *ᴮ zero = zero
-- m *ᴮ suc n = (m *ᴮ n) +ᴮ m
-- m *ᴮ predr n = (m *ᴮ n) -ᴮ m
-- m *ᴮ predl n = (m *ᴮ n) -ᴮ m
-- m *ᴮ suc-predr n i = ( +ᴮ-assoc (m *ᴮ n) (-ᴮ m) m
--                      ∙ cong ((m *ᴮ n) +ᴮ_) (+ᴮ-invˡ m)
--                      ∙ +ᴮ-unitʳ (m *ᴮ n)) i
-- m *ᴮ predl-suc n i = ( +ᴮ-assoc (m *ᴮ n) m (-ᴮ m)
--                      ∙ cong ((m *ᴮ n) +ᴮ_) (+ᴮ-invʳ m)
--                      ∙ +ᴮ-unitʳ (m *ᴮ n)) i
