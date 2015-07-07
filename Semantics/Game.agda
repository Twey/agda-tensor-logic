{-# OPTIONS --copatterns #-}

module Semantics.Game where

record Game : Set₁ where
  coinductive
  constructor game
  field
    {move} : Set
    play   : move → Game

open Game

open import Data.Sum using (_⊎_; inj₁; inj₂)

_⊗_ : Game → Game → Game
move (A ⊗ B) = move A ⊎ move B
play (A ⊗ B) (inj₁ a) = game λ a′ → play (play A a) a′ ⊗ B
play (A ⊗ B) (inj₂ b) = game λ b′ → A ⊗ play (play B b) b′
