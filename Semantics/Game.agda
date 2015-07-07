{-# OPTIONS --copatterns #-}

module Semantics.Game where

record Game : Set₁ where
  coinductive
  constructor game
  field
    {move} : Set
    play   : move → Game

open Game public

import Data.Empty
import Data.Unit
open import Data.Sum using (_⊎_; inj₁; inj₂)

⊤ : Game
move ⊤ = Data.Empty.⊥
play ⊤ ()

infixr 5 ¬_
¬_ : Game → Game
move (¬ g) = Data.Unit.⊤
play (¬ g) Data.Unit.tt = g

infixr 4 _⊗_
_⊗_ : Game → Game → Game
move (A ⊗ B) = move A ⊎ move B
play (A ⊗ B) (inj₁ a) = game λ a′ → play (play A a) a′ ⊗ B
play (A ⊗ B) (inj₂ b) = game λ b′ → A ⊗ play (play B b) b′

⊥ : Game
⊥ = ¬ ⊤

infixr 3 _⊸_
_⊸_ : Game → Game → Game
A ⊸ B = ¬ (¬ A ⊗ B)
