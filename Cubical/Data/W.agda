{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

module Cubical.Data.W where

open _≅_

private
  variable
    ℓX ℓS ℓP : Level

module _ {X : Type ℓX} (S : Type ℓS) (P : S → Type ℓP) (outX : S → X) (inX : ∀ s → P s → X) where
  data W : X → Type (ℓ-max ℓX (ℓ-max ℓS ℓP)) where
    node : (s : S) → (subtree : (p : P s) → W (inX s p)) → W (outX s)
    
  Subtree : S → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Subtree s = (p : P s) → W (inX s p)
  
module _ {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where
  getShape : ∀ {x} → W S P outX inX x → S
  getShape (node s subtree) = s

  getSubtree : ∀ {x} → (w : W S P outX inX x) → (p : P (getShape w)) → W S P outX inX (inX _ p)
  getSubtree (node s subtree) = subtree

  outShape : ∀ {x} → (w : W S P outX inX x) → (outX (getShape w) ≡ x)
  outShape (node s subtree) = refl

  fibShape : ∀ {x} → (w : W S P outX inX x) → fiber outX x
  fibShape w = getShape w , outShape w
  
  wExt : ∀ x x' → (px : x ≡ x') → (w : W S P outX inX x) → (w' : W S P outX inX x')
    → (psfib : PathP (λ i → fiber outX (px i)) (fibShape w) (fibShape w'))
    → PathP (λ i → Subtree S P outX inX (fst (psfib i))) (getSubtree w) (getSubtree w')
    → PathP (λ i → W S P outX inX (px i)) w w'
  wExt .(outX s) .(outX s') px (node s subtree) (node s' subtree') psfib psubtree i =
    transp (λ j → W S P outX inX (snd (psfib i) j)) (i ∨ ~ i) (node (fst (psfib i)) (psubtree i)) -- ppx j i

  wExtRefl : ∀ x → (w : W S P outX inX x) → wExt x x refl w w refl refl ≡ refl {x = w}
  wExtRefl x (node s subtree) =
    (λ i → transp (λ j → W S P outX inX (outX s)) (i ∨ ~ i) (node s subtree))
      ≡⟨ (λ k i → transp (λ j → W S P outX inX (outX s)) (i ∨ ~ i ∨ k) (node s subtree)) ⟩
    (λ i → node s subtree) ∎

module WPathType {X : Type ℓX} (S : Type ℓS) (P : S → Type ℓP) (outX : S → X) (inX : ∀ s → P s → X) where

  IndexCover : Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  IndexCover = Σ[ y ∈ X ] W S P outX inX y × W S P outX inX y

  ShapeCover : Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  ShapeCover = Σ[ s ∈ S ] ((p : P s) → W S P outX inX (inX s p)) × ((p : P s) → W S P outX inX (inX s p))

  ArityCover : ShapeCover → Type ℓP
  ArityCover = P ∘ fst

  outIndexCover : ShapeCover → IndexCover
  outIndexCover (s , subtree , subtree') = outX s , node s subtree , node s subtree'

  inIndexCover : ∀ scover → ArityCover scover → IndexCover
  inIndexCover (s , subtree , subtree') p = inX s p , subtree p , subtree' p

  Cover : ∀ {x} → (w w' : W S P outX inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  Cover {x} w w' = W {X = IndexCover} ShapeCover ArityCover outIndexCover inIndexCover (x , w , w')
  
  CoverFib : (x : X) → (w w' : W S P outX inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  CoverFib x w w' = fiber outIndexCover (x , w , w')
    
  SubtreeFib : (x : X) → (sfib : fiber outX x) → (w : W S P outX inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  SubtreeFib x (s , px) w = fiber
    {A = (p : P s) → W S P outX inX (inX s p)}
    (λ subtree → subst (W S P outX inX) px (node s subtree))
    w
      
  RepCoverFib : (x : X) → (w w' : W S P outX inX x) → Type (ℓ-max ℓX ℓS)
  --RepCoverFib x w w' = PathP (λ _ → fiber outX x) (fibShape w) (fibShape w')
  RepCoverFib x w w' = Σ[ sfib ∈ fiber outX x ] (fibShape w ≡ sfib) × (fibShape w' ≡ sfib)
  --RepCoverFib : (x : X) → (w w' : W S P outX inX x) → Type (ℓ-max (ℓ-max ℓX ℓS) ℓP)
  --RepCoverFib x w w' = Σ[ sfib ∈ fiber outX x ] SubtreeFib x sfib w × SubtreeFib x sfib w'

module WPath {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where
  -- inspired by https://github.com/jashug/IWTypes

  open WPathType S P outX inX

  reflCode : ∀ {x} → (w : W S P outX inX x) → Cover w w
  reflCode (node s subtree) = node (s , subtree , subtree) (λ p → reflCode (subtree p))

  encode : ∀ {x} → (w w' : W S P outX inX x) → w ≡ w' → Cover w w'
  encode w _ = J (λ w' pw → Cover w w') (reflCode w)

  encodeRefl : ∀ {x} → (w : W S P outX inX x) → encode w w refl ≡ reflCode w
  encodeRefl w = JRefl (λ w' pw → Cover w w') (reflCode w)

  decode : ∀ {x} → (w w' : W S P outX inX x) → Cover w w' → w ≡ w'
  decode .(node s subtree) .(node s subtree') (node (s , subtree , subtree') csubtree) i =
    node s λ p → decode (subtree p) (subtree' p) (csubtree p) i

  decodeRefl : ∀ {x} → (w : W S P outX inX x) → decode w w (reflCode w) ≡ refl
  decodeRefl (node s subtree) j i = node s λ p → decodeRefl (subtree p) j i

  decodeEncode : ∀ {x} → (w w' : W S P outX inX x) → (pw : w ≡ w') → decode w w' (encode w w' pw) ≡ pw
  decodeEncode w _ = J (λ w' pw → decode w w' (encode w w' pw) ≡ pw)
    (
      decode w w (encode w w refl)
        ≡⟨ cong (decode w w) (encodeRefl w) ⟩
      decode w w (reflCode w)
        ≡⟨ decodeRefl w ⟩
      refl ∎
    )

  encodeDecode : ∀ {x} → (w w' : W S P outX inX x) → (cw : Cover w w') → encode w w' (decode w w' cw) ≡ cw
  encodeDecode {x} w@(node s subtree) w'@(node s subtree') cw@(node (s , subtree , subtree') csubtree) j =
    transp (λ k → Cover w (pathOfLemmaRefl k j)) (j ∨ ~ j) (snd (lemma j))
    where
      psubtree : subtree ≡ subtree'
      psubtree = funExt (λ p → decode _ _ (csubtree p))
      pw : w ≡ w'
      pw i = node s (psubtree i)
      pcsubtree1 : ∀ (p : P s) → PathP (λ i → Cover (subtree p) (psubtree i p))
        (encode _ _ refl)
        (encode _ _ (decode _ _ (csubtree p)))
      pcsubtree1 p i = encode _ _ λ j → decode _ _ (csubtree p) (i ∧ j)
      pcsubtree : ∀ (p : P s) → PathP (λ i → Cover (subtree p) (psubtree i p))
        (reflCode _)
        (csubtree p)
      pcsubtree p = transp
        (λ j → PathP (λ i → Cover (subtree p) (psubtree i p))
          (encodeRefl (subtree p) j)
          (encodeDecode _ _ (csubtree p) j)
        )
        i0
        (pcsubtree1 p)
      lemma : PathP (λ _ → Σ[ v ∈ W S P outX inX x ] Cover w v)
        (w' , encode w w' (λ i → node s (λ p → decode (subtree p) (subtree' p) (csubtree p) i)))
        (w' , node (s , subtree , subtree') csubtree)
      lemma =
        w' , encode w w' (λ i → node s (λ p → decode (subtree p) (subtree' p) (csubtree p) i))
          ≡⟨ sym (λ j → pw j , encode w (pw j) (λ i → node s (λ p →
            decode (subtree p) (psubtree j p) (pcsubtree p j) i
          ))) ⟩
        w , encode w w  (λ i → node s (λ p → decode (subtree p) (subtree  p) (reflCode _) i))
          ≡⟨ (λ j → w , encode w w (λ i → node s (λ p → decodeRefl (subtree p) j i))) ⟩
        w , encode w w  (λ i → node s (λ p → subtree p))
          ≡⟨⟩
        w , encode w w refl
          ≡⟨ (λ j → w , encodeRefl w j) ⟩
        w , reflCode w
          ≡⟨⟩
        w , node (s , subtree , subtree) (λ p → reflCode (subtree p))
          ≡⟨ (λ j → pw j , node (s , subtree , psubtree j) (λ p → pcsubtree p j)) ⟩
        w' , node (s , subtree , subtree') csubtree ∎
      pathOfLemma : w' ≡ w'
      pathOfLemma = cong fst lemma
      pathOfLemmaRefl : pathOfLemma ≡ refl
      pathOfLemmaRefl = {!!} -- I don't know how to do this. It seems fst doesn't commute definitionally with _∙_

  encodeIso : ∀ {x} → (w w' : W S P outX inX x) → (w ≡ w') ≅ (Cover w w')
  fun (encodeIso w w') = encode w w'
  inv (encodeIso w w') = decode w w'
  rightInv (encodeIso w w') cw = encodeDecode w w' cw
  leftInv (encodeIso w w') pw = decodeEncode w w' pw

  encodeEquiv : ∀ {x} → (w w' : W S P outX inX x) → (w ≡ w') ≃ (Cover w w')
  encodeEquiv w w' = isoToEquiv (encodeIso w w')

  encodePath : ∀ {x} → (w w' : W S P outX inX x) → (w ≡ w') ≡ (Cover w w')
  encodePath w w' = ua (encodeEquiv w w')
  
  isoRepCoverFib : (x : X) → (w w' : W S P outX inX x) → CoverFib x w w' ≅ RepCoverFib x w w'
  fun (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww') = subst
    (λ (x , w , w') → RepCoverFib x w w')
    pxww'
    ((s , refl) , refl , refl)
  inv (isoRepCoverFib x w w') ((s , px) , psfib , psfib') = (s ,
      subst (Subtree S P outX inX) (cong fst psfib ) (getSubtree w ) ,
      subst (Subtree S P outX inX) (cong fst psfib') (getSubtree w')
    ) , cong₂ _,_ px (congP₂ (λ _ → _,_)
      (wExt _ _ px _ _
        (congP₂ (λ _ → _,_)
          (sym (cong fst psfib))
          (λ i → transp
            (λ j → outX (
              fst (psfib (~ i))) -- flat square composed above
              ≡
              cong snd psfib (~ i ∨ j) i -- one triangular half of (cong snd psfib) folded open and composed below
            )
            (i ∨ ~ i) -- the sides of the thing composed below, are reflexive
            λ j → cong snd psfib (~ i) (i ∧ j) -- the other triangular half of (cong snd psfib) folded open and put in the middle
          )
        )
        (symP (subst-filler (Subtree S P outX inX) (cong fst psfib ) (getSubtree w )))
      )
      (wExt _ _ px _ _
        (congP₂ (λ _ → _,_)
          (sym (cong fst psfib'))
          (λ i → transp
            (λ j → outX (
              fst (psfib' (~ i))) -- flat square composed above
              ≡
              cong snd psfib' (~ i ∨ j) i -- one triangular half of (cong snd psfib) folded open and composed below
            )
            (i ∨ ~ i) -- the sides of the thing composed below, are reflexive
            λ j → cong snd psfib' (~ i) (i ∧ j) -- the other triangular half of (cong snd psfib) folded open and put in the middle
          )
        )
        (symP (subst-filler (Subtree S P outX inX) (cong fst psfib') (getSubtree w')))
      )
    )
  rightInv (isoRepCoverFib x w w') = {!!}
  leftInv (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww') =
    J (λ (x , w , w') pxww' →
        inv (isoRepCoverFib x w w') (fun (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww'))
        ≡ ((s , subtree , subtree') , pxww')
      )
      (let x  = outX s
           w  = node s subtree
           w' = node s subtree'
       in  inv (isoRepCoverFib x w w') (fun (isoRepCoverFib x w w') ((s , subtree , subtree') , refl))
             ≡⟨ (λ i → (inv (isoRepCoverFib x w w'))
                   (substRefl {A = IndexCover} {B = λ (x , w , w') → RepCoverFib x w w'} {x = x , w , w'} ((s , refl) , refl , refl) i)
             ) ⟩
             --≡⟨ cong (inv (isoRepCoverFib x w w')) (substRefl {B = λ (x , w , w') → RepCoverFib x w w'} ((s , refl) , refl , refl)) ⟩
           inv (isoRepCoverFib x w w') ((s , refl) , refl , refl)
             ≡⟨ cong₂ _,_
                  (cong₂ _,_ refl (congP₂ (λ _ → _,_)
                    (substRefl {B = Subtree S P outX inX} subtree )
                    (substRefl {B = Subtree S P outX inX} subtree')
                  ))
                  {!flipSquare λ j → cong₂ _,_
                    refl
                    (congP₂ (λ _ → _,_)
                      (
                        wExt (outX s) (outX s) (λ _ → outX s)
                          (node s (subst (Subtree S P outX inX) (λ i → s) subtree))
                          (node s subtree)
                          (λ i → s , transp (λ j₁ → outX s ≡ outX s) (i ∨ ~ i) (λ j₁ → outX s))
                          (symP (subst-filler (Subtree S P outX inX) (λ _ → s) subtree))
                          j
                          ≡⟨⟩
                        wExt (outX s) (outX s) (λ _ → outX s)
                          (node s (subst (Subtree S P outX inX) (λ i → s) subtree))
                          (node s subtree)
                          (λ i → s , transp (λ j₁ → outX s ≡ outX s) (i ∨ ~ i) (λ j₁ → outX s))
                          (substRefl {B = Subtree S P outX inX} subtree)
                          j
                          ≡⟨ (λ k →
                            wExt (outX s) (outX s) (λ _ → outX s)
                              (node s (substRefl {B = Subtree S P outX inX} subtree k))
                              (node s subtree)
                              (λ i → s , transp (λ _ → outX s ≡ outX s) (i ∨ ~ i ∨ k) (λ _ → outX s))
                              (λ i → substRefl {B = Subtree S P outX inX} subtree (i ∨ k))
                              j
                          ) ⟩
                        wExt (outX s) (outX s) (λ _ → outX s)
                          (node s subtree)
                          (node s subtree)
                          (λ i → s , λ _ → outX s)
                          (λ i → subtree)
                          j
                          ≡⟨ (λ k → wExtRefl (outX s) (node s subtree) k j) ⟩
                        wExtRefl (outX s) (node s subtree) i1 j
                          ≡⟨ {!λ k → node s subtree!} ⟩
                        node s subtree ∎
                      )
                      {!!}
                    )
                  !}
             ⟩
           (s , subtree , subtree') , refl {x = outX s , node s subtree , node s subtree'} ∎
      )
      pxww'
{-
  fun (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww') =
    transport
      (λ j → PathP (λ i → fiber outX (fst (pxww' j)))
        (fibShape (fst (snd (pxww' j))))
        (fibShape (snd (snd (pxww' j))))
      )
      refl
  inv (isoRepCoverFib x w w'@(node s' subtree')) psfib =
    J (λ s' _ → (subtree' : Subtree S P outX inX s') → Σ[ (s* , subtree* , subtree*' ) ∈ ShapeCover ]
        (outX s* , node s* subtree* , node s* subtree*') ≡ (x , w , w'))
      (λ subtree' → (getShape w , getSubtree w , subtree') , cong₂ _,_ (outShape w)
        (congP₂ (λ _ → _,_)
          (wExt _ _ (outShape w) _ w (congP₂ (λ _ → _,_)
            refl
            λ j i → outShape w (i ∧ j)
          ) refl)
          (wExt _ _ (outShape w) _ w' (congP₂ (λ _ → _,_)
            (cong fst psfib)
            {!!}
          ) {!!})
        )
      )
        -- subst (Subtree S P outX inX) (sym (cong fst psfib)) subtree'
      (cong fst psfib) subtree'
    {-
    (getShape w' , subst (Subtree S P outX inX) (cong fst psfib) (getSubtree w) , getSubtree w') ,
    cong₂ _,_ (outShape w') (congP₂ (λ _ → _,_)
      (wExt _ _ (outShape w') _ w  (congP₂ (λ _ → _,_)
        (sym (cong fst psfib))
        {!!}
      ) {!!})
      (wExt _ _ (outShape w') _ w' (congP₂ (λ _ → _,_)
        refl
        (λ j i → outShape w' (i ∧ j))
      ) refl)
    )
    -}
  rightInv (isoRepCoverFib x w w') = {!!}
  leftInv (isoRepCoverFib x w w') = {!!}
  
{-
  isoRepCoverFib : (x : X) → (w w' : W S P outX inX x) → CoverFib x w w' ≅ RepCoverFib x w w'
  fun (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww') =
    (s , cong fst pxww') ,
    (subtree  , fromPathP (λ i → fst (snd (pxww' i)))) ,
    (subtree' , fromPathP (λ i → snd (snd (pxww' i))))
  inv (isoRepCoverFib x w w') ((s , px) , (subtree , pw) , (subtree' , pw')) =
    (s , subtree , subtree') , cong₂ _,_ px (congP₂ (λ i → _,_) (toPathP pw) (toPathP pw'))
  rightInv (isoRepCoverFib x w w') ((s , px) , (subtree , pw) , (subtree' , pw')) j =
    (s , px) ,
    (subtree  , PathPIsoPath (λ i → W S P outX inX (px i)) (node s subtree ) w  .rightInv pw  j) ,
    (subtree' , PathPIsoPath (λ i → W S P outX inX (px i)) (node s subtree') w' .rightInv pw' j)
    --cong ((s , px) ,_) (cong₂ _,_
    --  (cong (subtree  ,_) (PathPIsoPath (λ i → W S P outX inX (px i)) (node s subtree ) w  .rightInv pw ))
    --  (cong (subtree' ,_) (PathPIsoPath (λ i → W S P outX inX (px i)) (node s subtree') w' .rightInv pw'))
    --)
  leftInv (isoRepCoverFib x w w') ((s , subtree , subtree') , pxww') j =
    (s , subtree , subtree') , λ i →
      fst (pxww' i) ,
      PathPIsoPath (λ i → W S P outX inX (fst (pxww' i))) (node s subtree ) w  .leftInv (λ i → fst (snd (pxww' i))) j i ,
      PathPIsoPath (λ i → W S P outX inX (fst (pxww' i))) (node s subtree') w' .leftInv (λ i → snd (snd (pxww' i))) j i

  equivRepCoverFib : (x : X) → (w w' : W S P outX inX x) → CoverFib x w w' ≃ RepCoverFib x w w'
  equivRepCoverFib x w w' = isoToEquiv (isoRepCoverFib x w w')

  pathRepCoverFib : (x : X) → (w w' : W S P outX inX x) → CoverFib x w w' ≡ RepCoverFib x w w'
  pathRepCoverFib x w w' = ua (equivRepCoverFib x w w')
  
module _ {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} where

  isPropW : ∀ (isPropS : ∀ x → isProp (fiber outX x)) → ∀ x → isProp (W S P outX inX x)
  isPropW isPropS x w w'@(node s' subtree') = wExt x x refl w w'
    (isPropS x (fibShape w) (fibShape w'))
    (toPathP (funExt λ p → isPropW isPropS _ _ (subtree' p)))

open WPath

isOfHLevelSuc-W : ∀ {X : Type ℓX} {S : Type ℓS} {P : S → Type ℓP} {outX : S → X} {inX : ∀ s → P s → X} →
  ∀ (n : HLevel) (isHS : ∀ x → isOfHLevel (suc n) (fiber outX x))
  → ∀ x → isOfHLevel (suc n) (W S P outX inX x)
isOfHLevelSuc-W {ℓX = ℓX} {ℓS = ℓS} {ℓP = ℓP} {X = X} {S} {P} {outX} {inX} zero isHS x w w' = isPropW isHS x w w'
isOfHLevelSuc-W {ℓX = ℓX} {ℓS = ℓS} {ℓP = ℓP} {X = X} {S} {P} {outX} {inX} (suc n) isHS x w w' =
  subst (isOfHLevel (suc n)) (sym (encodePath w w')) (isOfHLevelSuc-W n isHCoverFib (x , w , w'))
  where
    open WPathType S P outX inX
    isHCoverFib : ((x , w , w') : Σ[ y ∈ X ] W S P outX inX y × W S P outX inX y) → isOfHLevel (suc n) (CoverFib x w w')
    isHCoverFib (x , w , w') = subst⁻ (isOfHLevel (suc n)) (pathRepCoverFib x w w')
      (isOfHLevelΣ (suc n) {!isHS x!} {!!})
-}
-}
