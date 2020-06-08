{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Structures.Group.Base

module GroupLemmas {ℓ : Level} (G : Group {ℓ}) where
  op = group-operation G
  _⨀_ = group-operation G
  id = group-id G
  inv = group-inv G
  abstract
    set : isSet ⟨ G ⟩
    set = group-is-set G

    lUnit : (a : ⟨ G ⟩) → a ≡ id ⨀ a
    lUnit a = sym (group-lid G a)
    
    rUnit : (a : ⟨ G ⟩) → a ≡ a ⨀ id
    rUnit a = sym (group-rid G a)

    lCancel : (a : ⟨ G ⟩) → inv a ⨀ a ≡ id
    lCancel = group-linv G

    rCancel : (a : ⟨ G ⟩) → a ⨀ inv a ≡ id
    rCancel = group-rinv G

    assoc : (a b c : ⟨ G ⟩) → a ⨀ (b ⨀ c) ≡ (a ⨀ b) ⨀ c
    assoc = group-assoc G

    simplL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a ⨀ b ≡ a ⨀ c → b ≡ c
    simplL a {b} {c} p =
      b
        ≡⟨ lUnit b ∙ cong (_⨀ b) (sym (lCancel a)) ∙ sym (assoc _ _ _) ⟩
      inv a ⨀ (a ⨀ b)
        ≡⟨ cong (inv a ⨀_) p ⟩
      inv a ⨀ (a ⨀ c)
        ≡⟨ assoc _ _ _ ∙ cong (_⨀ c) (lCancel a) ∙ sym (lUnit c) ⟩
      c ∎

    simplR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a ⨀ c ≡ b ⨀ c → a ≡ b
    simplR {a} {b} c p =
      a
        ≡⟨ rUnit a ∙ cong (a ⨀_) (sym (rCancel c)) ∙ assoc _ _ _ ⟩
      (a ⨀ c) ⨀ inv c
        ≡⟨ cong (_⨀ inv c) p ⟩
      (b ⨀ c) ⨀ inv c
        ≡⟨ sym (assoc _ _ _) ∙ cong (b ⨀_) (rCancel c) ∙ sym (rUnit b) ⟩
      b ∎

  invInvo : (a : ⟨ G ⟩) → inv (inv a) ≡ a
  invInvo a = simplL (inv a) (rCancel (inv a) ∙ sym (lCancel a))

  invId : inv id ≡ id
  invId = simplL id (rCancel id ∙ lUnit id)

  idUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e ⨀ x ≡ x → e ≡ id
  idUniqueL {e} x p = simplR x (p ∙ lUnit _)

  idUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x ⨀ e ≡ x → e ≡ id
  idUniqueR x {e} p = simplL x (p ∙ rUnit _)

  invUniqueL : {g h : ⟨ G ⟩} → g ⨀ h ≡ id → g ≡ inv h
  invUniqueL {g} {h} p = simplR h (p ∙ sym (lCancel h))

  invUniqueR : {g h : ⟨ G ⟩} → g ⨀ h ≡ id → h ≡ inv g
  invUniqueR {g} {h} p = simplL g (p ∙ sym (rCancel g))
