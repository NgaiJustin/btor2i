use crate::bvec::BitVector;
use crate::error;
use crate::error::InterpError;
use btor2tools::Btor2LineIterator;
use btor2tools::Btor2SortContent;
use btor2tools::Btor2SortTag;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt;

// TODO: eventually remove pub and make a seperate pub function as a main entry point to the interpreter, for now this is main.rs
#[derive(Debug)]
pub struct Environment {
  // Maps sid/nid to value
  // TODO: valid programs should not have the same identifier in both sets, but we don't currently check that
  // TODO: perhaps could opportunistically free mappings if we know they won't be used again
  env: Vec<Value>,
  args: HashMap<String, usize>,
  output: HashMap<String, Value>,
}

impl Environment {
  pub fn new(size: usize) -> Self {
    Self {
      // Allocate a larger stack size so the interpreter needs to allocate less often
      env: vec![Value::default(); size],
      args: HashMap::new(),
      output: HashMap::new(),
    }
  }

  pub fn get(&self, idx: usize) -> &Value {
    // A BTOR2 program is well formed when, dynamically, every variable is defined before its use.
    // If this is violated, this will return Value::Uninitialized and the whole interpreter will come crashing down.
    self.env.get(idx).unwrap()
  }

  pub fn set(&mut self, idx: usize, val: Value) {
    self.env[idx] = val;
  }

  pub fn get_output(&self) -> &HashMap<String, Value> {
    &self.output
  }
}

impl fmt::Display for Environment {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // iterate over self.args in order and print them

    writeln!(f, "Arguments:")?;
    let mut sorted_args = self.args.iter().collect::<Vec<_>>();
    sorted_args.sort_by(|(name1, _), (name2, _)| name1.cmp(name2));
    sorted_args.iter().try_for_each(|(name, val)| {
      writeln!(f, "{}: {}", name, val)?;
      Ok(())
    })?;

    write!(f, "\nEnvironment:\n")?;
    // don't print uninitialized values
    self.env.iter().enumerate().try_for_each(|(idx, val)| {
      writeln!(f, "{}: {}", idx, val)?;
      Ok(())
    })?;

    write!(f, "\nOutput:\n")?;
    self.output.iter().try_for_each(|(name, val)| {
      writeln!(f, "{}: {}", name, val)?;
      Ok(())
    })?;

    Ok(())
  }
}

// TODO: eventually remove pub and make a seperate pub function as a main entry point to the interpreter, for now this is main.rs
#[derive(Debug, Default, Clone)]
pub enum Value {
  BitVector(BitVector),
  // TODO: Add support for <STATE>
  // TODO: Add support for <ARRAY>
  #[default]
  Uninitialized,
}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::BitVector(bv) => write!(f, "{}", bv.to_usize()),
      Value::Uninitialized => write!(f, "_"),
    }
  }
}

pub fn interpret(
  mut prog_iterator: Btor2LineIterator,
  _env: &mut Environment,
) -> Result<(), InterpError> {
  // HashMap<String, usize>
  // for now, we only deal with bitvec sorts
  // map will be from line number to size of sort
  let mut sorts_map = HashMap::<i64, u32>::new();

  prog_iterator.try_for_each(|line| {
    let id = line.id();
    let tag = line.tag();
    match tag {
      // core
      btor2tools::Btor2Tag::Sort => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = sort.content() {
              sorts_map.insert(id, width);
            };
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", sort.tag()))),
        }
      }
      btor2tools::Btor2Tag::Const => {
        let constval = line.constant();
        match line.constant() {
          Some(cstr) => {
            match cstr.to_str() {
              Ok(str) => {
                let nstring = str.to_string();
                let boolvec: Vec<bool> = nstring.chars().map(|x| x != '0').collect();
                Ok(())
              }
              Err(E) => Err(error::InterpError::BadFuncArgType("Bad value in constant".to_string()))
            }
            
          }
          None => Err(error::InterpError::BadFuncArgType("No value in constant".to_string()))
        }
        
      },
      btor2tools::Btor2Tag::Constd => Ok(()),
      btor2tools::Btor2Tag::Consth => Ok(()),
      btor2tools::Btor2Tag::Input => {
        let input_name = line.symbol().unwrap().to_string_lossy().into_owned();

        // verify that input is of the correct sort
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = sort.content() {
              if let Some(expected_width) = sorts_map.get(&sort.id()) {
                if *expected_width != width {
                  return Err(error::InterpError::BadFuncArgWidth(
                    input_name,
                    *expected_width as usize,
                    width as usize,
                  ));
                } else {
                  // convert input to bitvector
                  let input_val = _env.args.get(&input_name).unwrap();
                  let input_bits = BitVector::from(*input_val);

                  _env.set(id.try_into().unwrap(), Value::BitVector(input_bits));
                }
              } else {
                // TODO: Replace this with a different error type
                return Err(error::InterpError::Unsupported(format!(
                  "Input {} has width {}, but no sort was found",
                  id, width
                )));
              }
            };
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", sort.tag()))),
        }
      }
      btor2tools::Btor2Tag::Output => {
        let output_name = line.symbol().unwrap().to_string_lossy().into_owned();
        let output_val = _env.get(line.args()[0] as usize);

        _env.output.insert(output_name, output_val.clone());

        Ok(())
      }
      // btor2tools::Btor2Tag::Sort => Ok(()),
      btor2tools::Btor2Tag::One => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = sort.content() {
              // bitvec with one bit set to 1
              let zero = BitVector::zeros(width as usize);
              let one = BitVector::inc(&zero);
              _env.set(id.try_into().unwrap(), Value::BitVector(one));
            };
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", sort.tag()))),
        }
      }
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
      btor2tools::Btor2Tag::Add => {
        assert_eq!(line.args().len(), 2);
        let arg1 = _env.get(line.args()[0] as usize);
        let arg2 = _env.get(line.args()[1] as usize);

        if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
          let result = BitVector::add(arg1, arg2);
          _env.set(id.try_into().unwrap(), Value::BitVector(result));
        } else {
          return Err(error::InterpError::Unsupported(format!(
            "Addition of {:?} and {:?}",
            arg1, arg2
          )));
        }

        Ok(())
      }
      btor2tools::Btor2Tag::Mul => {
        assert_eq!(line.args().len(), 2);
        let arg1 = _env.get(line.args()[0] as usize);
        let arg2 = _env.get(line.args()[1] as usize);
        if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
          let result = BitVector::mul(arg1, arg2);
          _env.set(id.try_into().unwrap(), Value::BitVector(result));
        } else {
          return Err(error::InterpError::Unsupported(format!(
            "Multiplication of {:?} and {:?}",
            arg1, arg2
          )));
        }
        Ok(())
      }
      btor2tools::Btor2Tag::Sdiv => Ok(()),
      btor2tools::Btor2Tag::Udiv => Ok(()),
      btor2tools::Btor2Tag::Smod => Ok(()),
      btor2tools::Btor2Tag::Srem => Ok(()),
      btor2tools::Btor2Tag::Urem => Ok(()),
      btor2tools::Btor2Tag::Sub => {
        assert_eq!(line.args().len(), 2);
        let arg1 = _env.get(line.args()[0] as usize);
        let arg2 = _env.get(line.args()[1] as usize);
        if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
          let result = BitVector::sub(arg1, arg2);
          _env.set(id.try_into().unwrap(), Value::BitVector(result));
        } else {
          return Err(error::InterpError::Unsupported(format!(
            "Subtraction of {:?} and {:?}",
            arg1, arg2
          )));
        }
        Ok(())
      }

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
      | btor2tools::Btor2Tag::Write => Err(error::InterpError::Unsupported(format!("{:?}", tag))),
    }
  })
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
