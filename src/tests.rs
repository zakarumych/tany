use core::any::Any;

use alloc::boxed::Box;

use crate::{LTAny, TAny};

#[test]
fn test_small_primitive() {
    let mut tany = TAny::new(42u32);
    assert_eq!(tany.is::<u32>(), true);
    assert_eq!(tany.is::<u64>(), false);
    assert_eq!(tany.downcast_ref::<u32>(), Some(&42));
    assert_eq!(tany.downcast_ref::<u64>(), None);
    assert_eq!(tany.downcast_mut::<u32>(), Some(&mut 42));
    assert_eq!(tany.downcast_mut::<u64>(), None);

    drop(tany);
}

#[test]
fn test_large_primitive() {
    type Array = [u64; 4];
    let mut array = [1u64, 2, 3, 4];

    let mut tany = TAny::new(array);
    assert_eq!(tany.is::<Array>(), true);
    assert_eq!(tany.is::<u64>(), false);
    assert_eq!(tany.downcast_ref::<Array>(), Some(&array));
    assert_eq!(tany.downcast_ref::<u64>(), None);
    assert_eq!(tany.downcast_mut::<Array>(), Some(&mut array));
    assert_eq!(tany.downcast_mut::<u64>(), None);

    drop(tany);
}

#[test]
fn test_downcast_primitive() {
    let mut tany = TAny::new(42u32);

    tany = match tany.downcast::<u64>() {
        Ok(_) => panic!("expected downcast to fail"),
        Err(tany) => tany,
    };

    match tany.downcast::<u32>() {
        Ok(v) => assert_eq!(v, 42),
        Err(_) => panic!("expected downcast to succeed"),
    }
}

#[test]
fn test_downcast_large_primitive() {
    type Array = [u64; 4];
    let array = [1u64, 2, 3, 4];

    let mut tany = TAny::new(array);

    tany = match tany.downcast::<u64>() {
        Ok(_) => panic!("expected downcast to fail"),
        Err(tany) => tany,
    };

    match tany.downcast::<Array>() {
        Ok(v) => assert_eq!(v, array),
        Err(_) => panic!("expected downcast to succeed"),
    }
}

#[test]
fn test_send_sync() {
    fn is_send_sync<T: Send + Sync>(_: &T) {}

    let tany = TAny::new(42u32);
    is_send_sync(&tany);
}

#[test]
fn test_not_send_sync() {
    let rc = alloc::rc::Rc::new(42u32);
    let tany = LTAny::new(rc);

    drop(tany);
}


#[test]
fn test_from_any() {
    let any: Box<dyn Any + Send + Sync> = Box::new(42u32);
    let tany = TAny::from_any(any);

    assert_eq!(tany.downcast_ref::<u32>(), Some(&42));
}