use crate::bvec::BitVectorNew;
use btor2tools::Btor2Parser;
use btor2tools::Btor2SortContent;
use btor2tools::Btor2LineIterator;
use std::collections::HashMap;
use std::hash::Hash;

struct Environment {
  // Maps sid/nid to value
  // TODO: valid programs should not have the same identifier in both sets, but we don't currently check that
  // TODO: perhaps could opportunistically free mappings if we know they won't be used again
  env: Vec<Value>,
}

impl Environment {
  pub fn new(size: usize) -> Self {
    Self {
      // Allocate a larger stack size so the interpreter needs to allocate less often
      env: vec![Value::default(); size],
    }
  }

  pub fn get(&self, idx: usize) -> &Value {
    // A bril program is well formed when, dynamically, every variable is defined before its use.
    // If this is violated, this will return Value::Uninitialized and the whole interpreter will come crashing down.
    self.env.get(idx).unwrap()
  }

  pub fn set(&mut self, idx: usize, val: Value) {
    self.env[idx] = val;
  }
}

#[derive(Debug, Default, Clone)]
enum Value {
  BitVectorNew,
  // TODO: Add support for <STATE>
  #[default]
  Uninitialized,
}

fn interpret(prog_iterator: Btor2LineIterator, env: Environment) {
  // for now, we only deal with bitvec sorts
  // map will be from line number to size of sort
  let mut sorts_map = HashMap::<i64, u32>::new();

  prog_iterator.for_each(|line| {
    let id = line.id();
    let tag = line.tag();
    match tag {
        btor2tools::Btor2Tag::Sort => {
        let sort = line.sort();
        match sort.tag() {
          BitVector => {
            if let Btor2SortContent::Bitvec{width} = sort.content(){
              sorts_map.insert(id, width);
            }
          }
        }
      },
      

      _ => (),
    }
  })
}



// mapping from line #s to sorts
// make sort a union type

// Main loop interpreter signature
// Btor2 program description, inputs: name -> BitVec
// Add an interface element to convert a list of bools into a properly formatted bitvec map