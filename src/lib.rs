//! This crate provides a type-erased values as replacement for `Box<dyn Any>`
//! that can store small values inline without heap allocation.
//!
//! `TAny` is a type-erased value that can store any value of any type that implements `Send`, `Sync` and is `'static`.
//! `LTAny` is relaxed version of `TAny` that doesn't require `Send`, `Sync` bounds.
//! 
//! ## Usage
//!
//! ```
//! use tany::TAny;
//!
//! // u32 fits inline storage, so no allocation is performed.
//! let mut a: TAny = TAny::new(42u32);
//!
//! // Get reference to the value.
//! let r: &u32 = a.downcast_ref::<u32>().unwrap();
//!
//! // Get reference to the value.
//! let r: &mut u32 = a.downcast_mut::<u32>().unwrap();
//!
//! // Take ownership of the value.
//! let Ok(a) = a.downcast::<u32>() else {
//!     panic!();
//! };
//!
//!
//! let already_boxed = Box::new([1u32; 10]);
//!
//!
//! // Construct TAny from already boxed value.
//! // If type doesn't fit into the storage, the box is used as is,
//! // otherwise value is unboxed.
//! let a: TAny = TAny::from_box(already_boxed);
//!
//! assert_eq!(a.downcast_ref::<[u32; 10]>().unwrap(), &[1u32; 10]);
//!
//! use core::any::Any;
//!
//! let any: Box<dyn Any + Send + Sync> = Box::new(42u32);
//!
//! // Construct TAny from existing Box<dyn Any>.
//! let a: TAny = TAny::from_any(any); // Or use `From<Box<dyn Any + Send + Sync>>` trait.
//!
//! assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
//! ```

#![no_std]

extern crate alloc;

mod storage;
mod tany;

pub use self::tany::{LTAny, TAny};

#[cfg(test)]
mod tests;
