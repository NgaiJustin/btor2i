use crate::error::InterpError;
use btor2tools::Btor2LineIterator;
use btor2tools::Btor2SortContent;
use btor2tools::Btor2SortTag;
use std::collections::HashMap;
use std::fmt::format;

// TODO: eventually remove pub and make a seperate pub function as a main entry point to the interpreter, for now this is main.rs
#[derive(Debug)]
pub struct Environment {
  // Maps sid/nid to value
  // TODO: valid programs should not have the same identifier in both sets, but we don't currently check that
  // TODO: perhaps could opportunistically free mappings if we know they won't be used again
  env: Vec<Value>,
  args: HashMap<String, usize>,
}

impl Environment {
  pub fn new(size: usize) -> Self {
    Self {
      // Allocate a larger stack size so the interpreter needs to allocate less often
      env: vec![Value::default(); size],
      args: HashMap::new(),
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

// TODO: eventually remove pub and make a seperate pub function as a main entry point to the interpreter, for now this is main.rs
#[derive(Debug, Default, Clone)]
pub enum Value {
  BitVector,
  // TODO: Add support for <STATE>
  #[default]
  Uninitialized,
}

fn interpret(prog_iterator: Btor2LineIterator, _env: Environment) -> Result<(), InterpError> {
  // HashMap<String, usize>
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
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = sort.content() {
              sorts_map.insert(id, width);
            }
          }
          Btor2SortTag::Array => {
            // if let Btor2SortContent::Array { index, element } = sort.content() {
            //   if let Btor2SortContent::Bitvec { width } = element.content() {
            //     sorts_map.insert(id, width);
            //   }
            // }
          }
        }
      }

      // core
      btor2tools::Btor2Tag::Const => Ok(()),
      btor2tools::Btor2Tag::Constd => Ok(()),
      btor2tools::Btor2Tag::Consth => Ok(()),
      btor2tools::Btor2Tag::Input => Ok(()),
      btor2tools::Btor2Tag::Output => Ok(()),
      // btor2tools::Btor2Tag::Sort => Ok(()),
      btor2tools::Btor2Tag::One => Ok(()),
      btor2tools::Btor2Tag::Ones => Ok(()),
      btor2tools::Btor2Tag::Zero => Ok(()),

      // indexed
      btor2tools::Btor2Tag::Sext => Ok(()),
      btor2tools::Btor2Tag::Uext => Ok(()),
      btor2tools::Btor2Tag::Slice => Ok(()),

      // unary
      btor2tools::Btor2Tag::Not => Ok(()),
      btor2tools::Btor2Tag::Inc => Ok(()),
      btor2tools::Btor2Tag::Dec => Ok(()),
      btor2tools::Btor2Tag::Neg => Ok(()),
      btor2tools::Btor2Tag::Redand => Ok(()),
      btor2tools::Btor2Tag::Redor => Ok(()),
      btor2tools::Btor2Tag::Redxor => Ok(()),

      // binary - boolean
      btor2tools::Btor2Tag::Iff => Ok(()),
      btor2tools::Btor2Tag::Implies => Ok(()),

      // binary - (dis)equality
      btor2tools::Btor2Tag::Eq => Ok(()),
      btor2tools::Btor2Tag::Neq => Ok(()),

      // binary - (un)signed inequality
      btor2tools::Btor2Tag::Sgt => Ok(()),
      btor2tools::Btor2Tag::Sgte => Ok(()),
      btor2tools::Btor2Tag::Slt => Ok(()),
      btor2tools::Btor2Tag::Slte => Ok(()),
      btor2tools::Btor2Tag::Ugt => Ok(()),
      btor2tools::Btor2Tag::Ugte => Ok(()),
      btor2tools::Btor2Tag::Ult => Ok(()),
      btor2tools::Btor2Tag::Ulte => Ok(()),

      // binary - bit-wise
      btor2tools::Btor2Tag::And => Ok(()),
      btor2tools::Btor2Tag::Nand => Ok(()),
      btor2tools::Btor2Tag::Nor => Ok(()),
      btor2tools::Btor2Tag::Or => Ok(()),
      btor2tools::Btor2Tag::Xnor => Ok(()),
      btor2tools::Btor2Tag::Xor => Ok(()),

      // binary - rotate, shift
      btor2tools::Btor2Tag::Rol => Ok(()),
      btor2tools::Btor2Tag::Ror => Ok(()),
      btor2tools::Btor2Tag::Sll => Ok(()),
      btor2tools::Btor2Tag::Sra => Ok(()),
      btor2tools::Btor2Tag::Srl => Ok(()),

      // binary - arithmetic
      btor2tools::Btor2Tag::Add => Ok(()),
      btor2tools::Btor2Tag::Mul => Ok(()),
      btor2tools::Btor2Tag::Sdiv => Ok(()),
      btor2tools::Btor2Tag::Udiv => Ok(()),
      btor2tools::Btor2Tag::Smod => Ok(()),
      btor2tools::Btor2Tag::Srem => Ok(()),
      btor2tools::Btor2Tag::Urem => Ok(()),
      btor2tools::Btor2Tag::Sub => Ok(()),

      // binary - overflow
      btor2tools::Btor2Tag::Saddo => Ok(()),
      btor2tools::Btor2Tag::Uaddo => Ok(()),
      btor2tools::Btor2Tag::Sdivo => Ok(()),
      // btor2tools::Btor2Tag::Udivo => Ok(()),    Unsigned division never overflows :D
      btor2tools::Btor2Tag::Smulo => Ok(()),
      btor2tools::Btor2Tag::Umulo => Ok(()),
      btor2tools::Btor2Tag::Ssubo => Ok(()),
      btor2tools::Btor2Tag::Usubo => Ok(()),

      // binary - concat
      btor2tools::Btor2Tag::Concat => Ok(()),

      // ternary - conditional
      btor2tools::Btor2Tag::Ite => Ok(()),

      // Unsupported: arrays, state, assertions
      btor2tools::Btor2Tag::Bad
      | btor2tools::Btor2Tag::Constraint
      | btor2tools::Btor2Tag::Fair
      | btor2tools::Btor2Tag::Init
      | btor2tools::Btor2Tag::Justice
      | btor2tools::Btor2Tag::Next
      | btor2tools::Btor2Tag::State
      | btor2tools::Btor2Tag::Read
      | btor2tools::Btor2Tag::Write => Err(InterpError::Unsupported(format!("{:?}", tag))),
    }
  });

  Ok(())
}

// TODO: eventually remove pub and make a seperate pub function as a main entry point to the interpreter, for now this is main.rs
pub fn parse_inputs(
  mut env: Environment,
  arg_names: &[String],
  inputs: &[String],
) -> Result<Environment, InterpError> {
  if arg_names.is_empty() && inputs.is_empty() {
    Ok(env)
  } else if inputs.len() != arg_names.len() {
    Err(InterpError::BadNumFuncArgs(arg_names.len(), inputs.len()))
  } else {
    inputs.iter().try_for_each(|input| {
      // arg in the form "x=1", extract variable name and value
      let mut split = input.split('=');
      let arg_name = split.next().unwrap();
      let arg_val = split.next().unwrap();

      // try to parse the input as a number
      let arg_as_num = arg_val
        .parse::<usize>()
        .map_err(|_| InterpError::BadFuncArgType((*arg_val).to_string()))?;

      env.args.insert(arg_name.to_string(), arg_as_num);

      Ok(())
    })?;
    Ok(env)
  }
}

// mapping from line #s to sorts
// make sort a union type

// Main loop interpreter signature
// Btor2 program description, inputs: name -> BitVec
// Add an interface element to convert a list of bools into a properly formatted bitvec map
