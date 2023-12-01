use crate::bvec::BitVector;
use crate::error;
use crate::error::InterpError;
use btor2tools::Btor2LineIterator;
use btor2tools::Btor2SortContent;
use btor2tools::Btor2SortTag;
use num_bigint::BigInt;
use num_traits::{Num, One, Zero};
use std::collections::HashMap;
use std::str::FromStr;
use std::vec;
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
  prog_iterator: Btor2LineIterator,
  _env: &mut Environment,
) -> Result<(), InterpError> {
  // HashMap<String, usize>
  // for now, we only deal with bitvec sorts
  // map will be from line number to size of sort
  let mut sorts_map = HashMap::<i64, u32>::new();

  for line in prog_iterator {
    let id = line.id();
    let tag = line.tag();
    // println!("{:?}", _env);
    println!("{:?}", line);
    let line_res: Result<(), String> = match tag {
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
                let intval: BigInt = BigInt::from_str_radix(&nstring, 2).unwrap();
                match line.sort().tag() {
                  Btor2SortTag::Bitvec => {
                    if let Btor2SortContent::Bitvec { width } = line.sort().content() {
                      let bv = BitVector::from_bigint(intval, width.try_into().unwrap());
                      _env.set(id.try_into().unwrap(), Value::BitVector(bv));
                    }
                    Ok(())
                  }
                  Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
                }
              }
              Err(E) => Err(error::InterpError::BadFuncArgType("Bad value in constant".to_string()))
            }
            
          }
          None => Err(error::InterpError::BadFuncArgType("No value in constant".to_string()))
        }
        
      },
      btor2tools::Btor2Tag::Constd => {let constval = line.constant();
        match line.constant() {
          Some(cstr) => {
            match cstr.to_str() {
              Ok(str) => {
                let nstring = str.to_string();
                let intval: BigInt = BigInt::from_str(&nstring).unwrap();
                match line.sort().tag() {
                  Btor2SortTag::Bitvec => {
                    if let Btor2SortContent::Bitvec { width } = line.sort().content() {
                      let bv = BitVector::from_bigint(intval, width.try_into().unwrap());
                      _env.set(id.try_into().unwrap(), Value::BitVector(bv));
                    }
                    Ok(())
                  }
                  Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
                }
              }
              Err(E) => Err(error::InterpError::BadFuncArgType("Bad value in constant".to_string()))
            }
            
          }
          None => Err(error::InterpError::BadFuncArgType("No value in constant".to_string()))
        }
      },
      btor2tools::Btor2Tag::Consth => {
        match line.constant() {
          Some(cstr) => {
            match cstr.to_str() {
              Ok(str) => {
                let nstring = str.to_string();
                let intval: BigInt = BigInt::from_str_radix(&nstring, 16).unwrap();
                match line.sort().tag() {
                  Btor2SortTag::Bitvec => {
                    if let Btor2SortContent::Bitvec { width } = line.sort().content() {
                      let bv = BitVector::from_bigint(intval, width.try_into().unwrap());
                      _env.set(id.try_into().unwrap(), Value::BitVector(bv));
                    }
                    Ok(())
                  }
                  Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
                }
              }
              Err(E) => Err(error::InterpError::BadFuncArgType("Bad value in constant".to_string()))
            }
            
          }
          None => Err(error::InterpError::BadFuncArgType("No value in constant".to_string()))
        }
      },
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

                  // justin what is going on here
                  let input_val = _env.args.get(&input_name).unwrap();

                  // is this a vector of length 1?
                  let input_bits = BitVector::from_bool(*input_val == 1);
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

      btor2tools::Btor2Tag::One => {
        let intval: BigInt = One::one();
        match line.sort().tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              let bv = BitVector::one(width.try_into().unwrap());
              _env.set(id.try_into().unwrap(), Value::BitVector(bv));
            }
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
        }
      },
      btor2tools::Btor2Tag::Ones => {
        match line.sort().tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              let bv = BitVector::ones(width.try_into().unwrap());
              _env.set(id.try_into().unwrap(), Value::BitVector(bv));
            }
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
        }
      },
      btor2tools::Btor2Tag::Zero => {
        match line.sort().tag() {
          Btor2SortTag::Bitvec => {
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              let bv = BitVector::zeros(width.try_into().unwrap());
              _env.set(id.try_into().unwrap(), Value::BitVector(bv));
            }
            Ok(())
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag()))),
        }
      },

      // indexed
      btor2tools::Btor2Tag::Sext => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let new_width = line.args()[1] as usize;
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if arg1.width() + new_width != width as usize {
                  return Err(error::InterpError::Unsupported(format!(
                    "Extension of {:?} is not supported",
                    arg1
                  )));
                }
                let bv2 = BitVector::sign_extend(arg1, new_width);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Extension of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Extension of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Uext => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let new_width = line.args()[1] as usize;
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if arg1.width() + new_width != width as usize {
                  return Err(error::InterpError::Unsupported(format!(
                    "Extension of {:?} is not supported",
                    arg1
                  )));
                }
                let bv2 = BitVector::zero_extend(arg1, new_width);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Extension of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Extension of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Slice => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 3);
            let arg1 = _env.get(line.args()[0] as usize);
            let u = line.args()[1] as usize;
            let l: usize = line.args()[2] as usize;
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if (u-l)+1 != width as usize {
                  return Err(error::InterpError::Unsupported(format!(
                    "Slicing of {:?} is not supported",
                    arg1
                  )));
                }
                let bv2 = BitVector::slice(arg1, l, u);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Slicing of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Slicing of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },

      // unary
    btor2tools::Btor2Tag::Not => {
      let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != arg1.width()){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), width.try_into().unwrap(), arg1.width()))
                }
                let bv2 = BitVector::not(arg1);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Not of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Not of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
    },
      btor2tools::Btor2Tag::Inc => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != arg1.width()){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), width.try_into().unwrap(), arg1.width()))
                }
                let bv2 = BitVector::inc(arg1);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Inc of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Inc of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Dec => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != arg1.width()){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), width.try_into().unwrap(), arg1.width()))
                }
                let bv2 = BitVector::dec(arg1);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Dec of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Dec of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Neg => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != arg1.width()){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), width.try_into().unwrap(), arg1.width()))
                }
                let bv2 = BitVector::neg(arg1);
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Neg of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Neg of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Redand => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != 1){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), 1, arg1.width()))
                }
                let bv2 = BitVector::from_bool(BitVector::redand(arg1));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Redand of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Redand of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Redor => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != 1){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), 1, arg1.width()))
                }
                let bv2 = BitVector::from_bool(BitVector::redor(arg1));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Redor of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Redor of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Redxor => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 1);
            let arg1 = _env.get(line.args()[0] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let Value::BitVector(arg1) = arg1 {
                if((width as usize) != 1){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), 1, arg1.width()))
                }
                let bv2 = BitVector::from_bool(BitVector::redxor(arg1));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Redxor of {:?} is not supported",
                  arg1
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Redxor of {:?} is not supported",
                arg1
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },

      // binary - boolean
      btor2tools::Btor2Tag::Iff => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let arg2 = _env.get(line.args()[1] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
                if((width as usize) != 1 || arg1.width() != 1 || arg2.width() != 1){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), 1, arg1.width()))
                }
                let bv2 = BitVector::from_bool(BitVector::iff(arg1, arg2));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Iff of {:?}, {:?} is not supported",
                  arg1, arg2
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Iff of {:?}, {:?} is not supported",
                arg1, arg2
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Implies => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let arg2 = _env.get(line.args()[1] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
                if((width as usize) != 1 || arg1.width() != 1 || arg2.width() != 1){
                  return Err(error::InterpError::BadFuncArgWidth("arg1".to_string(), 1, arg1.width()))
                }
                let bv2 = BitVector::from_bool(BitVector::implies(arg1, arg2));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Implies of {:?}, {:?} is not supported",
                  arg1, arg2
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Implies of {:?}, {:?} is not supported",
                arg1, arg2
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },

      // binary - (dis)equality
      btor2tools::Btor2Tag::Eq => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let arg2 = _env.get(line.args()[1] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if(width != 1){
                return Err(error::InterpError::BadFuncArgWidth("sid".to_string(), 1, width.try_into().unwrap()))
              }
              if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
                let bv2 = BitVector::from_bool(BitVector::equals(arg1, arg2));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Eq of {:?}, {:?} is not supported",
                  arg1, arg2
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Eq of {:?}, {:?} is not supported",
                arg1, arg2
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },
      btor2tools::Btor2Tag::Neq => {
        let sort = line.sort();
        match sort.tag() {
          Btor2SortTag::Bitvec => {
            assert_eq!(line.args().len(), 2);
            let arg1 = _env.get(line.args()[0] as usize);
            let arg2 = _env.get(line.args()[1] as usize);
            if let Btor2SortContent::Bitvec { width } = line.sort().content() {
              if(width != 1){
                return Err(error::InterpError::BadFuncArgWidth("sid".to_string(), 1, width.try_into().unwrap()))
              }
              if let (Value::BitVector(arg1), Value::BitVector(arg2)) = (arg1, arg2) {
                let bv2 = BitVector::from_bool(BitVector::neq(arg1, arg2));
                _env.set(id.try_into().unwrap(), Value::BitVector(bv2));
                Ok(())
              } else {
                Err(error::InterpError::Unsupported(format!(
                  "Neq of {:?}, {:?} is not supported",
                  arg1, arg2
                )))
              }
            } else {
              Err(error::InterpError::Unsupported(format!(
                "Neq of {:?}, {:?} is not supported",
                arg1, arg2
              )))
            }
          }
          Btor2SortTag::Array => Err(error::InterpError::Unsupported(format!("{:?}", line.sort().tag())))
        }
      },

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
            "Addition of {:?} and {:?} is not supported",
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
            "Multiplication of {:?} and {:?} is not supported",
            arg1, arg2
          )));
        }
        Ok(())
      },
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
            "Subtraction of {:?} and {:?} is not supported",
            arg1, arg2
          )));
        }
        Ok(())
      },

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
    .map_err(|e| (e.to_string()));
  }
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
