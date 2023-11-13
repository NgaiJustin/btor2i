// use std::fmt::Display;
use thiserror::Error;

// Having the #[error(...)] for all variants derives the Display trait as well
#[derive(Error, Debug)]
pub enum InterpError {
  #[error("Expected `{0}` function arguments, found `{1}`")]
  BadNumFuncArgs(usize, usize), // (expected, actual)

  #[error("Expected `{0}` instruction arguments, found `{1}`")]
  BadNumArgs(usize, usize), // (expected, actual)

  #[error("Expected int args, found `{0}`")]
  BadFuncArgType(String), // (actual)
}

impl InterpError {
  // #[must_use]
  // pub fn add_pos(self, pos: Option<Position>) -> PositionalInterpError {
  //   // TODO: Support PositionalInterpError in the future
  // }
}
