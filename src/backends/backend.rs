//! Module that defines traits that need to be implemented, as a prerequisite to implement
//! `Context`, that provies it SMT solver capabilities.

use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt;

use theories::core;
use backends::smtlib2::SMTProc;

#[derive(Clone, Debug)]
pub enum SMTError {
    Timeout,
    Undefined,
    Unsat,
    AssertionError(String),
}

pub type SMTResult<T> = Result<T, SMTError>;

/// Trait a backend should implement to support SMT solving.
///
/// This is a minimalistic API and has to be expanded in the future to support more SMT operations
/// and to grow this into a full SMTLib Crate.
///
/// All functions names are analogous in meaning to their usage in the original SMT-LIB2 sense.
/// TODO:
///  - define_fun
///  - declare_sort
///  - define_sort
///  - get_proof
///  - get_unsat_core
///  - get_value
///  - get_assignment
///  - push
///  - pop
///  - get_option
///  - set_option
///  - get_info
///  - set_info
// Functions which do not really make sense for the solver currently:
// 1. exit - The solver instance 
pub trait SMTBackend {
    type Idx: Debug + Clone;
    type Logic: Logic;

    fn set_logic<S: SMTProc>(&mut self, &mut S);
    //fn declare_fun<T: AsRef<str>>(&mut self, Option<T>, Option<Vec<Type>>, Type) -> Self::Idx;

    fn new_var<T, P>(&mut self, Option<T>, P) -> Self::Idx
        where T: AsRef<str>,
              P: Into<<<Self as SMTBackend>::Logic as Logic>::Sorts>;

    fn assert<T: Into<<<Self as SMTBackend>::Logic as Logic>::Fns>>(&mut self, T, &[Self::Idx]) -> Self::Idx;
    // Adding a way to add a timeout to check_sat and solve methods.
    // If no value is provided it will default to indefinite wait.
    fn check_sat<S: SMTProc>(&mut self, &mut S, Option<u64>) -> SMTResult<bool>;
    fn solve<S: SMTProc>(&mut self, &mut S, Option<u64>) -> SMTResult<HashMap<Self::Idx, u64>>;

}

pub trait Logic: fmt::Display + Clone + Copy {
    type Fns: SMTNode + fmt::Display + Debug + Clone;
    type Sorts: fmt::Display + Debug + Clone;
    
    fn free_var<T: AsRef<str>>(T, Self::Sorts) -> Self::Fns;
}

pub trait SMTNode: fmt::Display {
    /// Returns true if the node is a symbolic variable
    fn is_var(&self) -> bool;
    /// Returns true if the node is a constant value
    fn is_const(&self) -> bool;
    /// Returns true if the node is a function
    fn is_fn(&self) -> bool {
        !self.is_var() && !self.is_const()
    }

    // FIXME
    fn is_bool(&self) -> bool {
        false
    }
}
