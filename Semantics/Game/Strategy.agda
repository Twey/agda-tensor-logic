{-# OPTIONS --copatterns #-}

module Semantics.Game.Strategy where

open import Semantics.Game

record Strategy  (g : Game) : Set
record Strategy′ (g : Game) : Set

record Strategy g where
  coinductive
  constructor strat
  field
    react : (m : move g) → Strategy′ (play g m)

record Strategy′ g where
  coinductive
  constructor strat′
  field
    response : move g
    followup : Strategy (play g response)

open Strategy  public
open Strategy′ public

open import Level
open import Relation.Binary

-- TODO this is misfiled
record _∼_ (A B : Game) : Set where
  constructor _,_
  field
    to   : Strategy A → Strategy B
    from : Strategy B → Strategy A

open import Function

∼-equiv : IsEquivalence _∼_
∼-equiv = record
  { refl  = id , id
  ; sym   = λ { (to , from) → from , to }
  ; trans = λ { (to , from) (to′ , from′) → (to′ ∘ to) , (from ∘ from′) }
  }

setoid : Setoid (suc zero) zero
setoid = record
  { Carrier       = Game
  ; _≈_           = _∼_
  ; isEquivalence = ∼-equiv
  }

