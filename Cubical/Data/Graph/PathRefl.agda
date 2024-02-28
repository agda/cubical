-- Paths in a graph
{-# OPTIONS --safe #-}

module Cubical.Data.Graph.PathRefl where

open import Cubical.Data.Graph.Base
open import Cubical.Data.List.Base hiding (_++_)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma.Base hiding (Path)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (Path)


module _ {ℓv ℓe : Level} where

  module _ (G : Graph ℓv ℓe) where
    data Path : (v w : Node G) → Type (ℓ-max ℓv ℓe) where
      pnil : ∀ {v} → Path v v
      pcons : ∀ {v w x} → Path v w → Edge G w x → Path v x
      pcons⁻ : ∀ {v w x} → Path v w → Edge G x w → Path v x
      pinvol : ∀ {v w x} → (p :  Path v w) → (q : Edge G w x) → pcons⁻ (pcons p q) q ≡ p
      pinvol⁻ : ∀ {v w x} → (p :  Path v w) → (q : Edge G x w) → pcons (pcons⁻ p q) q ≡ p

    -- Path concatenation
    ccat : ∀ {v w x} → Path v w → Path w x → Path v x
    ccat P pnil = P
    ccat P (pcons Q e) = pcons (ccat P Q) e
    ccat P (pcons⁻ Q e) = pcons⁻ (ccat P Q) e
    ccat P (pinvol Q e i) = pinvol (ccat P Q) e i
    ccat P (pinvol⁻ Q e i) = pinvol⁻ (ccat P Q) e i
  
    private
      _++_ = ccat
      infixr 20 _++_

    -- Some properties
    pnil++ : ∀ {v w} (P : Path v w) → pnil ++ P ≡ P
    pnil++ pnil = refl
    pnil++ (pcons P e) = cong (λ P → pcons P e) (pnil++ _)
    pnil++ (pcons⁻ P e) = cong (λ P → pcons⁻ P e) (pnil++ _)
    pnil++ (pinvol P e i) j = pinvol (pnil++ P j) e i
    pnil++ (pinvol⁻ P e i) j = pinvol⁻ (pnil++ P j) e i
  
    ++assoc : ∀ {v w x y}
        (P : Path v w) (Q : Path w x) (R : Path x y)
      → (P ++ Q) ++ R ≡ P ++ (Q ++ R)
    ++assoc P Q pnil = refl
    ++assoc P Q (pcons R e) = cong (λ P → pcons P e) (++assoc P Q R)
    ++assoc P Q (pcons⁻ R e) = cong (λ P → pcons⁻ P e) (++assoc P Q R)
    ++assoc P Q (pinvol R e i) j = pinvol (++assoc P Q R j) e i
    ++assoc P Q (pinvol⁻ R e i) j = pinvol⁻ (++assoc P Q R j) e i

    -- pNilInvol : ∀ {v w} → (e : Edge G v w) → (pcons pnil e ++ pcons⁻ pnil e) ≡ pnil
    -- pNilInvol e = pinvol pnil e

    invPath : ∀ {v w} → Path v w → Path w v
    invPath pnil = pnil
    invPath (pcons P e) = pcons⁻ pnil e ++ (invPath P) 
    invPath (pcons⁻ P e) = pcons pnil e ++ (invPath P)
    invPath (pinvol P e i) =
     (sym (++assoc (pcons pnil e) (pcons⁻ pnil e) (invPath P)) ∙∙
        cong (_++ invPath P) (pinvol pnil e) ∙∙ pnil++ (invPath P)) i 
    invPath (pinvol⁻ P e i) =
      (sym (++assoc (pcons⁻ pnil e) (pcons pnil e) (invPath P)) ∙∙
        cong (_++ invPath P) (pinvol⁻ pnil e) ∙∙ pnil++ (invPath P)) i 


    -- invPathL : ∀ {v w} → (P : Path v w) → (invPath P ++ P) ≡ pnil
    -- invPathL pnil = refl
    -- invPathL (pcons P x) = ++assoc (pcons⁻ pnil x) (invPath P) (pcons P x)
    --  ∙∙ cong (λ P → pcons⁻ pnil x ++ pcons P x) (invPathL P) ∙∙ pinvol⁻ pnil x
    -- invPathL (pcons⁻ P x) =
    --    ++assoc (pcons pnil x) (invPath P) (pcons⁻ P x)
    --  ∙∙ cong (λ P → pcons pnil x ++ pcons⁻ P x) (invPathL P) ∙∙ pinvol pnil x
    -- invPathL (pinvol P q i) = {!!}
    -- invPathL (pinvol⁻ P q i) = {!!}

--     invPathR : ∀ {v w} → (P : Path v w) → (P ++ invPath P) ≡ pnil
--     invPathR pnil = refl
--     invPathR (pcons P x) = sym (++assoc (pcons P x) (pcons⁻ pnil x) (invPath P))
--       ∙∙ cong (_++ (invPath P)) (pinvol P x) ∙∙ invPathR P
--     invPathR (pcons⁻ P x) = sym (++assoc (pcons⁻ P x) (pcons pnil x) (invPath P))
--       ∙∙ cong (_++ (invPath P)) (pinvol⁻ P x) ∙∙ invPathR P
--     invPathR (pinvol P q i) j =
--       hcomp (λ k →
--          λ { (i = i1) → invPathR P ( j ∧ k)
--            ; (j = i0) → {!!}
--            ; (j = i1) → {!!}
--            })
--             (hcomp (λ k →
--          λ { (i = i1) → {!!}
--            ; (j = i0) → {!!}
--            ; (j = i1) → invPathR P k
--            })
--             {!!})
--     invPathR (pinvol⁻ P q i) = {!!}
    
-- -- -- Paths as lists
--     -- pathToList : ∀ {v w} → Path v w
--     --     → List (Σ[ x ∈ Node G ] Σ[ y ∈ Node G ] Edge G x y)
--     -- pathToList pnil = []
--     -- pathToList (pcons P e) = (_ , _ , e) ∷ (pathToList P)

--     -- -- Path v w is a set
--     -- -- Lemma 4.2 of https://arxiv.org/abs/2112.06609
--     -- module _ (isSetNode : isSet (Node G))
--     --          (isSetEdge : ∀ v w → isSet (Edge G v w)) where

--     --   -- This is called ̂W (W-hat) in the paper
--     --   PathWithLen : ℕ → Node G → Node G → Type (ℓ-max ℓv ℓe)
--     --   PathWithLen 0 v w = Lift {j = ℓe} (v ≡ w)
--     --   PathWithLen (suc n) v w = Σ[ k ∈ Node G ] (PathWithLen n v k × Edge G k w)

--     --   isSetPathWithLen : ∀ n v w → isSet (PathWithLen n v w)
--     --   isSetPathWithLen 0 _ _ = isOfHLevelLift 2 (isProp→isSet (isSetNode _ _))
--     --   isSetPathWithLen (suc n) _ _ = isSetΣ isSetNode λ _ →
--     --       isSet× (isSetPathWithLen _ _ _) (isSetEdge _ _)

--     --   isSet-ΣnPathWithLen : ∀ {v w} → isSet (Σ[ n ∈ ℕ ] PathWithLen n v w)
--     --   isSet-ΣnPathWithLen = isSetΣ isSetℕ (λ _ → isSetPathWithLen _ _ _)

--     --   Path→PathWithLen : ∀ {v w} → Path v w → Σ[ n ∈ ℕ ] PathWithLen n v w
--     --   Path→PathWithLen pnil = 0 , lift refl
--     --   Path→PathWithLen (pcons P e) = suc (Path→PathWithLen P .fst) ,
--     --                                       _ , Path→PathWithLen P .snd , e

--     --   PathWithLen→Path : ∀ {v w} → Σ[ n ∈ ℕ ] PathWithLen n v w → Path v w
--     --   PathWithLen→Path (0 , q) = subst (Path _) (q .lower) pnil
--     --   PathWithLen→Path (suc n , _ , pwl , e) = pcons (PathWithLen→Path (n , pwl)) e

--     --   Path→PWL→Path : ∀ {v w} P → PathWithLen→Path {v} {w} (Path→PathWithLen P) ≡ P
--     --   Path→PWL→Path {v} pnil = substRefl {B = Path v} pnil
--     --   Path→PWL→Path (pcons P x) = cong₂ pcons (Path→PWL→Path _) refl

--     --   isSetPath : ∀ v w → isSet (Path v w)
--     --   isSetPath v w = isSetRetract Path→PathWithLen PathWithLen→Path
--     --                                Path→PWL→Path isSet-ΣnPathWithLen
