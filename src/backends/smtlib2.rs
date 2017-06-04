//! Module that contains SMTLib Backend Implementation.
//!
//! This backend outputs the constraints in standard smt-lib2 format. Hence,
//! any solver that supports this format maybe used to solve for constraints.

use std::process::Child;
use std::collections::HashMap;
use std::io::{Read, Write};
use regex::Regex;
use std::time::Duration;
use std::sync::mpsc;

use petgraph::graph::{Graph, NodeIndex};
use petgraph::EdgeDirection;
use petgraph::visit::EdgeRef;

use backends::backend::{Logic, SMTBackend, SMTError, SMTNode, SMTResult};

/// Trait that needs to be implemented in order to support a new solver. `SMTProc` is short for
/// "SMT Process".
///
/// To support a new solver that accepts input in the standard SMTLIB2 format, it is sufficient to
/// implement this trait for the struct. This trait describes method needed to spawn, and
/// communicate (read / write) with the solver.
///
/// `read` and `write` methods are implemented by deafult and needs to be changed only if the
/// mode of communication is different (other than process pipes), or if some custom functionality
/// is required for the specific solver.
pub trait SMTProc {
    /// Function to initialize the solver. This includes spawning a process and keeping the process
    /// pipe open for read and write. The function takes &mut self as an argument to allow
    /// configuration during initialization.
    fn init(&mut self);
    /// Return a mutable reference to the process pipe.
    fn pipe<'a>(&'a mut self) -> &'a mut Child;

    fn write<T: AsRef<str>>(&mut self, s: T) -> Result<(), String> {
        // TODO: Check for errors.
        if let Some(ref mut stdin) = self.pipe().stdin.as_mut() {
            stdin.write(s.as_ref().as_bytes()).expect("Write to stdin failed");
            stdin.flush().expect("Failed to flush stdin");
        }
        Ok(())
    }

    fn read(&mut self, timeout: Option<u64>) -> Result<String, SMTError> {
        // Important point to note here is that, if the data available to read
        // is exactly 2048 bytes, then this reading mechanism fails and will end up waiting to
        // read more data (when none is available) indefinitely.
        let mut bytes_read = [0; 2048];
        let mut s = String::new();
        let solver = self.pipe();

        let (send, recv) = mpsc::channel::<bool>();

        if let Some(ref mut stdout) = solver.stdout.as_mut() {
            let n = stdout.read(&mut bytes_read).unwrap();
            s = format!("{}{}",
                        s,
                        String::from_utf8(bytes_read[0..n].to_vec()).unwrap());
            // Sends a response on the channel, indicating that the output has been generated.
             let _ = send.send(true);
        }

        if timeout.is_some() {
            let result = recv.recv_timeout(Duration::from_millis(timeout.unwrap()));
            if result.is_ok() {
                Ok(s)
            } else {
                Err(SMTError::Timeout)
            }
        } else {
            let _ = recv.recv();
            Ok(s)
        }
    }
}

#[derive(Clone, Debug)]
pub enum EdgeData {
    EdgeOrder(usize),
}

#[derive(Clone, Debug)]
pub struct SMTLib2<T: Logic> {
    logic: Option<T>,
    gr: Graph<T::Fns, EdgeData>,
    var_index: usize,
    var_map: HashMap<String, (NodeIndex, T::Sorts)>,
    idx_map: HashMap<NodeIndex, String>,
}

impl<L: Logic> SMTLib2<L> {
    pub fn new(logic: Option<L>) -> SMTLib2<L> {
        let solver = SMTLib2 {
            logic: logic,
            gr: Graph::new(),
            var_index: 0,
            var_map: HashMap::new(),
            idx_map: HashMap::new(),
        };
        solver
    }

    // Recursive function that builds up the assertion string from the tree.
    pub fn expand_assertion(&self, ni: NodeIndex) -> String {
        let mut children = self.gr
                               .edges_directed(ni, EdgeDirection::Outgoing)
                               .map(|edge| {
                                   match *edge.weight() {
                                       EdgeData::EdgeOrder(ref i) => (edge.target(), *i),
                                   }
                               })
                               .collect::<Vec<_>>();
        children.sort_by(|x, y| (x.1).cmp(&y.1));

        let mut assertion = self.gr[ni].to_string();

        assertion = if self.gr[ni].is_fn() {
            format!("({}", assertion)
        } else {
            assertion
        };

        for node in &children {
            assertion = format!("{} {}", assertion, self.expand_assertion(node.0))
        }

        if self.gr[ni].is_fn() {
            format!("{})", assertion)
        } else {
            assertion
        }
    }

    pub fn new_const<T: Into<L::Fns>>(&mut self, cval: T) -> NodeIndex {
        self.gr.add_node(cval.into())
    }

    pub fn generate_asserts(&self) -> String {
        // Write out all variable definitions.
        let mut decls = Vec::new();
        for (name, val) in &self.var_map {
            let ni = &val.0;
            let ty = &val.1;
            if self.gr[*ni].is_var() {
                decls.push(format!("(declare-fun {} () {})\n", name, ty));
            }
        }
        // Identify root nodes and generate the assertion strings.
        let mut assertions = Vec::new();
        for idx in self.gr.node_indices() {
            if self.gr.edges_directed(idx, EdgeDirection::Incoming).collect::<Vec<_>>().is_empty() {
                if self.gr[idx].is_fn() && self.gr[idx].is_bool() {
                    assertions.push(format!("(assert {})\n", self.expand_assertion(idx)));
                }
            }
        }
        let mut result = String::new();
        for w in decls.iter().chain(assertions.iter()) {
            result = format!("{}{}", result, w)
        }
        result
    }

    pub fn check_sat_with_timeout<S: SMTProc>(&mut self, smt_proc: &mut S, timeout: u64) -> SMTResult<bool> {
        let _ = smt_proc.write(self.generate_asserts());
        let _ = smt_proc.write("(check-sat)\n".to_owned());

        let read_result = smt_proc.read(Some(timeout));

        if read_result.is_ok() {
            let read_string = read_result.unwrap();

            if read_string == "sat\n" {
                Ok(true)
            } else {
                Ok(false)
            }
        } else {
            Err(SMTError::Timeout)
        }
    }

    fn parse_solver_output(&mut self, output: String) -> HashMap<NodeIndex, u64> {
        let mut result: HashMap<NodeIndex, u64> = HashMap::new();
        let re = Regex::new(r"\s+\(define-fun (?P<var>[0-9a-zA-Z_]+) \(\) [(]?[ _a-zA-Z0-9]+[)]?\n\s+(?P<val>([0-9]+|#x[0-9a-f]+|#b[01]+))")
                     .unwrap();
        for caps in re.captures_iter(&output) {
            let val_str = caps.name("val").unwrap();
            let val = if val_str.len() > 2 && &val_str[0..2] == "#x" {
                          u64::from_str_radix(&val_str[2..], 16)
                      } else if val_str.len() > 2 && &val_str[0..2] == "#b" {
                          u64::from_str_radix(&val_str[2..], 2)
                      } else {
                          val_str.parse::<u64>()
                      }
                      .unwrap();
            let vname = caps.name("var").unwrap();
            result.insert(self.var_map[vname].0.clone(), val);
        }
        return result;
    }

    pub fn solve_with_timeout<S: SMTProc>(&mut self, smt_proc: &mut S, timeout: u64) -> SMTResult<HashMap<NodeIndex, u64>> {
        let sat_result = self.check_sat(smt_proc);
        if !sat_result {
            return Err(SMTError::Unsat)
        }

        let _ = smt_proc.write("(get-model)\n".to_owned());
        
        let _ = smt_proc.read(Some(timeout));
        let read_result = smt_proc.read(Some(timeout));

        if read_result.is_ok() {
            let read_string = read_result.unwrap();
            Ok(self.parse_solver_output(read_string))
        } else {
            Err(SMTError::Timeout)
        }
    }
}

impl<L: Logic> SMTBackend for SMTLib2<L> {
    type Idx = NodeIndex;
    type Logic = L;

    fn new_var<T, P>(&mut self, var_name: Option<T>, ty: P) -> Self::Idx
        where T: AsRef<str>,
              P: Into<<<Self as SMTBackend>::Logic as Logic>::Sorts>
    {
        let var_name = var_name.map(|s| s.as_ref().to_owned()).unwrap_or({
            self.var_index += 1;
            format!("X_{}", self.var_index)
        });
        let typ = ty.into();
        let idx = self.gr.add_node(Self::Logic::free_var(var_name.clone(), typ.clone()));
        self.var_map.insert(var_name.clone(), (idx, typ));
        self.idx_map.insert(idx, var_name);
        idx
    }

    fn set_logic<S: SMTProc>(&mut self, smt_proc: &mut S) {
        if self.logic.is_none() {
            return;
        }
        let logic = self.logic.unwrap().clone();
        let _ = smt_proc.write(format!("(set-logic {})\n", logic));
    }

    fn assert<T: Into<L::Fns>>(&mut self, assert: T, ops: &[Self::Idx]) -> Self::Idx {
        // TODO: Check correctness like operator arity.
        let assertion = self.gr.add_node(assert.into());
        for (i, op) in ops.iter().enumerate() {
            self.gr.add_edge(assertion, *op, EdgeData::EdgeOrder(i));
        }
        assertion
    }


    fn check_sat<S: SMTProc>(&mut self, smt_proc: &mut S) -> bool {
        let _ = smt_proc.write(self.generate_asserts());
        let _ = smt_proc.write("(check-sat)\n".to_owned());

        let read_result = smt_proc.read(None);

        // TODO: Need to implement an else case where the read() might fail.
        // This could be implemented in the next version of the API since 
        // the check_sat function is expected to return a bool instead of an
        // Result<>.
        if read_result.is_ok() {
            let read_string = read_result.unwrap();
            if read_string == "sat\n" {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    // TODO: Return type information along with the value.
    fn solve<S: SMTProc>(&mut self, smt_proc: &mut S) -> SMTResult<HashMap<Self::Idx, u64>> {
        let mut result = HashMap::new();

        let sat_result = self.check_sat(smt_proc);
        if !sat_result {
            return Err(SMTError::Unsat)
        }

        let _ = smt_proc.write("(get-model)\n".to_owned());
        // XXX: For some reason we need two reads here in order to get the result from
        // the SMT solver. Need to look into the reason for this. This might stop
        // working in the
        // future.
        let _ = smt_proc.read(None);
        let read_result = smt_proc.read(None);

        if read_result.is_ok() {
            let read_string = read_result.unwrap();
            // Example of result from the solver:
            // (model
            //  (define-fun y () Int
            //    9)
            //  (define-fun x () Int
            //    10)
            // )
            let re = Regex::new(r"\s+\(define-fun (?P<var>[0-9a-zA-Z_]+) \(\) [(]?[ _a-zA-Z0-9]+[)]?\n\s+(?P<val>([0-9]+|#x[0-9a-f]+|#b[01]+))")
                         .unwrap();
            for caps in re.captures_iter(&read_string) {
                // Here the caps.name("val") can be a hex value, or a binary value or a decimal
                // value. We need to parse the output to a u64 accordingly.
                let val_str = caps.name("val").unwrap();
                let val = if val_str.len() > 2 && &val_str[0..2] == "#x" {
                              u64::from_str_radix(&val_str[2..], 16)
                          } else if val_str.len() > 2 && &val_str[0..2] == "#b" {
                              u64::from_str_radix(&val_str[2..], 2)
                          } else {
                              val_str.parse::<u64>()
                          }
                          .unwrap();
                let vname = caps.name("var").unwrap();
                result.insert(self.var_map[vname].0.clone(), val);
            }
            Ok(result)
        } else {
            Err(SMTError::Undefined)
        }
    }
}
