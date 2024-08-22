# TAny is for Tiny Any

## Introduction

TAny is a library that provides container `TAny` as drop-in replacement for `Box<dyn Any>`.
It is designed to avoid allocations when value fits into the storage.
Currently size of the storage is 3 times `usize` and max alignment is 8 bytes.
If size or alignment of the value is greater than the storage, it is allocated on heap and boxed.

## Usage

```rust
use tany::TAny;

// u32 fits inline storage, so no allocation is performed.
let a: TAny = TAny::new(42u32);

// Get reference to the value.
let r: &u32 = a.downcast_ref::<u32>().unwrap();

// Get reference to the value.
let r: &mut u32 = a.downcast_mut::<u32>().unwrap();

// Take ownership of the value.
let a: u32 = a.downcast::<u32>().unwrap();


let already_boxed = Box::new([1u32; 10]);


// Construct TAny from already boxed value.
// If type doesn't fit into the storage, the box is used as is,
// otherwise value is unboxed.
let a: TAny = TAny::from_box(already_boxed);

assert_eq!(a.downcast_ref::<[u32; 10]>().unwrap(), &[1u32; 10]);


let any: Box<dyn Any + Send + Sync> = Box::new(42u32);

// Construct TAny from existing Box<dyn Any>.
let a: TAny = TAny::from_any(any); // Or use `From<Box<dyn Any + Send + Sync>>` trait.

assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
```


`TAny` requires types to implement `Send` and `Sync`.
And in turn, `TAny` is `Send` and `Sync` itself.

For non-`Send` and non-`Sync` types, `tany` crate provides `LTAny` type with all the same API as `TAny`,
except there's no `Send` and `Sync` bounds.

