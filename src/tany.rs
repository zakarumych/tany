use core::{
    any::{Any, TypeId},
    marker::PhantomData,
    mem::ManuallyDrop,
    ptr,
};

use alloc::boxed::Box;

use crate::storage::InlineStorage;

unsafe fn type_id_boxed_any(storage: &InlineStorage) -> TypeId {
    let r: &Box<dyn Any> = unsafe { storage.as_ref::<Box<dyn Any>>().assume_init_ref() };

    // Without enough dereferences, it will type-erase `&Box<dyn Any>` to `&dyn Any`, instead of taking inner `&dyn Any`.
    // One * gives `Box<dyn Any>`, two ** gives `dyn Any`. And then take ref to it.
    let r: &dyn Any = &**r;

    r.type_id()
}

unsafe fn drop_inlined<T>(storage: &mut InlineStorage) {
    // Safety: It was initialized as `T`.
    unsafe {
        storage.as_mut::<T>().assume_init_drop();
    }
}

unsafe fn drop_boxed<T: ?Sized>(storage: &mut InlineStorage) {
    // Safety: It was initialized as `Box<T>`.
    unsafe {
        storage.as_mut::<Box<T>>().assume_init_drop();
    }
}

unsafe fn drop_empty_inlined<T>(_storage: &mut InlineStorage) {
    // It was initialized as `T`, but value was taken out.
}

unsafe fn drop_empty_boxed<T: ?Sized>(storage: &mut InlineStorage) {
    // Safety: It was initialized as `Box<T>`, but value was taken out.
    // Thus it is safe to drop the box itself without dropping the value.
    unsafe {
        storage.as_mut::<Box<ManuallyDrop<T>>>().assume_init_drop();
    }
}

unsafe fn as_ptr_inlined<T>(storage: &InlineStorage) -> *const u8 {
    // Safety: It was initialized as `T`.
    let r: &T = unsafe { storage.as_ref::<T>().assume_init_ref() };
    ptr::from_ref(r).cast()
}

unsafe fn as_ptr_boxed<T: ?Sized>(storage: &InlineStorage) -> *const u8 {
    // Safety: It was initialized as `Box<T>`.
    let r: &T = &**unsafe { storage.as_ref::<Box<T>>().assume_init_ref() };
    ptr::from_ref(r).cast()
}

unsafe fn as_mut_inlined<T>(storage: &mut InlineStorage) -> *mut u8 {
    // Safety: It was initialized as `T`.
    let r: &mut T = unsafe { storage.as_mut::<T>().assume_init_mut() };
    ptr::from_mut(r).cast()
}

unsafe fn as_mut_boxed<T: ?Sized>(storage: &mut InlineStorage) -> *mut u8 {
    // Safety: It was initialized as `Box<T>`.
    let r: &mut T = &mut **unsafe { storage.as_mut::<Box<T>>().assume_init_mut() };
    ptr::from_mut(r).cast()
}

// Virtual table to operate on the storage.
struct VTable {
    type_id: unsafe fn(&InlineStorage) -> TypeId,
    drop: unsafe fn(&mut InlineStorage),
    drop_empty: unsafe fn(&mut InlineStorage),
    as_ptr: unsafe fn(&InlineStorage) -> *const u8,
    as_mut: unsafe fn(&mut InlineStorage) -> *mut u8,
}

/// `dyn Any` with fixed-size inlined storage.
/// Types that fit in the storage are stored without allocation.
/// Types that are too large are boxed.
/// Stored types may not implement `Send` and `Sync`.
/// For thread-safe version see [`TAny`].
pub struct LTAny {
    vtable: &'static VTable,
    storage: InlineStorage,
    unsend: PhantomData<*mut u8>,
}

impl Drop for LTAny {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            (self.vtable.drop)(&mut self.storage);
        }
    }
}

impl From<Box<dyn Any>> for LTAny {
    #[inline(always)]
    fn from(boxed: Box<dyn Any>) -> Self {
        LTAny::from_any(boxed)
    }
}

impl LTAny {
    /// Returns `true` if the type `T` fits and can be stored without allocation.
    /// If `true`, then `LTAny::new::<T>` is guaranteed to not allocate.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// if LTAny::fits::<u32>() {
    ///   // Guaranteed to not allocate.
    ///   LTAny::new(42u32);
    /// }
    /// ```
    pub const fn fits<T>() -> bool {
        InlineStorage::fits::<T>()
    }

    /// Construct new [`LTAny`] with the given value.
    ///
    /// If the type `T` fits in the storage, it is stored without allocation.
    /// Otherwise, it will be boxed.
    ///
    /// Type of value may not implement `Send` or `Sync`.
    /// But [`LTAny`] itself does not implement `Send` and `Sync`.
    /// For `Send` and `Sync` container see [`TAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let mut a: LTAny = LTAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn new<T>(value: T) -> Self
    where
        T: 'static,
    {
        let mut storage = InlineStorage::new();

        if InlineStorage::fits::<T>() {
            storage.as_mut::<T>().write(value);

            let vtable = &VTable {
                type_id: |_| TypeId::of::<T>(),
                drop: drop_inlined::<T>,
                drop_empty: drop_empty_inlined::<T>,
                as_ptr: as_ptr_inlined::<T>,
                as_mut: as_mut_inlined::<T>,
            };

            LTAny {
                vtable,
                storage,
                unsend: PhantomData,
            }
        } else {
            let boxed = Box::new(value);

            storage.as_mut().write(boxed);

            let vtable = &VTable {
                type_id: |_| TypeId::of::<T>(),
                drop: drop_boxed::<T>,
                drop_empty: drop_empty_boxed::<T>,
                as_ptr: as_ptr_boxed::<T>,
                as_mut: as_mut_boxed::<T>,
            };

            LTAny {
                vtable,
                storage,
                unsend: PhantomData,
            }
        }
    }

    /// Construct new [`LTAny`] from the given boxed value.
    ///
    /// If type fits in the storage, value will be unboxed.
    /// Otherwise it will be stored as boxed, but no allocation will be performed.
    ///
    /// Type of value may not implement `Send` or `Sync`.
    /// But [`LTAny`] itself does not implement `Send` and `Sync`.
    /// For `Send` and `Sync` container see [`TAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let boxed = Box::new([1u32; 42]);
    /// 
    /// // No additional allocation is performed.
    /// let a: LTAny = LTAny::from_box(boxed);
    /// 
    /// assert_eq!(a.downcast_ref::<[u32; 42]>().unwrap(), &[1u32; 42]);
    /// ```
    #[inline]
    pub fn from_box<T: 'static>(boxed: Box<T>) -> Self {
        let mut storage = InlineStorage::new();

        if InlineStorage::fits::<T>() {
            storage.as_mut::<T>().write(*boxed);

            let vtable = &VTable {
                type_id: |_| TypeId::of::<T>(),
                drop: drop_inlined::<T>,
                drop_empty: drop_empty_inlined::<T>,
                as_ptr: as_ptr_inlined::<T>,
                as_mut: as_mut_inlined::<T>,
            };

            LTAny {
                vtable,
                storage,
                unsend: PhantomData,
            }
        } else {
            storage.as_mut().write(boxed);

            let vtable = &VTable {
                type_id: |_| TypeId::of::<T>(),
                drop: drop_boxed::<T>,
                drop_empty: drop_empty_boxed::<T>,
                as_ptr: as_ptr_boxed::<T>,
                as_mut: as_mut_boxed::<T>,
            };

            LTAny {
                vtable,
                storage,
                unsend: PhantomData,
            }
        }
    }

    /// Construct new [`LTAny`] with the given boxed any.
    /// Since type is unknown, it will be stored as boxed.
    ///
    /// Allows `Any` without `Send` or `Sync`.
    /// But [`LTAny`] itself does not implement `Send` and `Sync`.
    /// For `Send` and `Sync` container see [`TAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// use core::any::Any;
    /// 
    /// let any: Box<dyn Any> = Box::new(42u32);
    /// 
    /// let a: LTAny = LTAny::from_any(any);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn from_any(boxed: Box<dyn Any>) -> Self {
        const {
            assert!(InlineStorage::fits::<Box<dyn Any>>());
        }

        let mut storage = InlineStorage::new();

        storage.as_mut::<Box<dyn Any>>().write(boxed);

        let vtable = &VTable {
            type_id: type_id_boxed_any,
            drop: drop_boxed::<dyn Any>,
            drop_empty: drop_empty_boxed::<dyn Any>,
            as_ptr: as_ptr_boxed::<dyn Any>,
            as_mut: as_mut_boxed::<dyn Any>,
        };

        LTAny {
            vtable,
            storage,
            unsend: PhantomData,
        }
    }

    /// Returns the type id of the stored value.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// use core::any::TypeId;
    /// 
    /// let a: LTAny = LTAny::new(42u32);
    /// 
    /// assert_eq!(a.type_id(), TypeId::of::<u32>());
    /// ```
    #[inline]
    pub fn type_id(&self) -> TypeId {
        unsafe { (self.vtable.type_id)(&self.storage) }
    }

    /// Returns `true` if the stored value is of type `T`.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let a: LTAny = LTAny::new(42u32);
    /// assert!(a.is::<u32>());
    /// ```
    #[inline]
    pub fn is<T>(&self) -> bool
    where
        T: 'static,
    {
        self.type_id() == TypeId::of::<T>()
    }

    /// Returns some reference to the stored value if it is of type `T`.
    /// Otherwise returns none.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let a: LTAny = LTAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn downcast_ref<T>(&self) -> Option<&T>
    where
        T: 'static,
    {
        if self.is::<T>() {
            Some(unsafe { self.downcast_ref_unchecked::<T>() })
        } else {
            None
        }
    }

    /// Returns some mutable reference to the stored value if it is of type `T`.
    /// Otherwise returns none.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let mut a: LTAny = LTAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_mut::<u32>().unwrap(), &mut 42);
    /// ```
    #[inline]
    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
    where
        T: 'static,
    {
        if self.is::<T>() {
            Some(unsafe { self.downcast_mut_unchecked::<T>() })
        } else {
            None
        }
    }

    /// Returns the stored value if it is of type `T`.
    /// Otherwise return self back.
    ///
    /// This will unbox the value if it was stored as boxed.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let a: LTAny = LTAny::new(42u32);
    /// 
    /// let Ok(a) = a.downcast::<u32>() else {
    ///    panic!();
    /// };
    /// ```
    #[inline]
    pub fn downcast<T>(self) -> Result<T, LTAny>
    where
        T: 'static,
    {
        if self.is::<T>() {
            Ok(unsafe { self.downcast_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Returns reference to the stored value without type checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let a: LTAny = LTAny::new(42u32);
    /// 
    /// unsafe {
    ///    assert_eq!(a.downcast_ref_unchecked::<u32>(), &42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_ref_unchecked<T>(&self) -> &T
    where
        T: 'static,
    {
        debug_assert!(self.is::<T>());
        let ptr = unsafe { (self.vtable.as_ptr)(&self.storage) };
        unsafe { &*ptr.cast() }
    }

    /// Returns mutable reference to the stored value without type checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let mut a: LTAny = LTAny::new(42u32);
    /// 
    /// unsafe {
    ///   assert_eq!(a.downcast_mut_unchecked::<u32>(), &mut 42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_mut_unchecked<T>(&mut self) -> &mut T
    where
        T: 'static,
    {
        debug_assert!(self.is::<T>());
        let ptr = unsafe { (self.vtable.as_mut)(&mut self.storage) };
        unsafe { &mut *ptr.cast() }
    }

    /// Returns the stored value without type checking.
    ///
    /// This will unbox the value if it was stored as boxed.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::LTAny;
    /// let a: LTAny = LTAny::new(42u32);
    /// 
    /// unsafe {
    ///  assert_eq!(a.downcast_unchecked::<u32>(), 42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_unchecked<T>(self) -> T
    where
        T: 'static,
    {
        debug_assert!(self.is::<T>());
        // Prevent dropping using `vtable.drop`.
        let mut me = ManuallyDrop::new(self);

        // Read value out.
        let ptr = unsafe { (me.vtable.as_ptr)(&me.storage) };
        let value = unsafe { ptr.cast::<T>().read() };

        // Drop emptied storage.
        unsafe {
            (me.vtable.drop_empty)(&mut me.storage);
        }

        value
    }
}

/// `dyn Any` with fixed-size inlined storage.
/// Types that fit in the storage are stored without allocation.
/// Types that are too large are boxed.
/// Requires `Send` or `Sync`.
/// For thread-local version see [`LTAny`].
pub struct TAny {
    inner: LTAny,
}

unsafe impl Send for TAny {}
unsafe impl Sync for TAny {}

impl From<Box<dyn Any + Send + Sync>> for TAny {
    #[inline(always)]
    fn from(boxed: Box<dyn Any + Send + Sync>) -> Self {
        TAny::from_any(boxed)
    }
}

impl From<TAny> for LTAny {
    #[inline(always)]
    fn from(value: TAny) -> Self {
        value.inner
    }
}

impl TAny {
    /// Returns `true` if the type `T` fits and can be stored without allocation.
    /// If `true`, then `TAny::new::<T>` is guaranteed to not allocate.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// if TAny::fits::<u32>() {
    ///   // Guaranteed to not allocate.
    ///   TAny::new(42u32);
    /// }
    /// ```
    pub const fn fits<T>() -> bool {
        InlineStorage::fits::<T>()
    }

    /// Construct new [`TAny`] with the given value.
    ///
    /// If the type `T` fits in the storage, it is stored without allocation.
    /// Otherwise, it will be boxed.
    ///
    /// Type of value must implement both `Send` and `Sync`.
    /// And [`TAny`] itself implement `Send` and `Sync`.
    /// For types that do not implement `Send` or `Sync`, use [`LTAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let mut a: TAny = TAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn new<T>(value: T) -> Self
    where
        T: Send + Sync + 'static,
    {
        TAny {
            inner: LTAny::new(value),
        }
    }

    /// Construct new [`TAny`] from the given boxed value.
    ///
    /// If type fits in the storage, value will be unboxed.
    /// Otherwise it will be stored as boxed, but no allocation will be performed.
    ///
    /// Type of value must implement both `Send` and `Sync`.
    /// And [`TAny`] itself implement `Send` and `Sync`.
    /// For types that do not implement `Send` or `Sync`, use [`LTAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let boxed = Box::new([1u32; 42]);
    /// 
    /// // No additional allocation is performed.
    /// let a: TAny = TAny::from_box(boxed);
    /// 
    /// assert_eq!(a.downcast_ref::<[u32; 42]>().unwrap(), &[1u32; 42]);
    /// ```
    #[inline]
    pub fn from_box<T>(boxed: Box<T>) -> Self
    where
        T: Send + Sync + 'static,
    {
        TAny {
            inner: LTAny::from_box(boxed),
        }
    }

    /// Construct new [`TAny`] with the given boxed any.
    /// Since type is unknown, it will be stored as boxed.
    ///
    /// Type of value must implement both `Send` and `Sync`.
    /// And [`TAny`] itself implement `Send` and `Sync`.
    /// For types that do not implement `Send` or `Sync`, use [`LTAny`].
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// use core::any::Any;
    /// 
    /// let any: Box<dyn Any + Send + Sync> = Box::new(42u32);
    /// 
    /// let a: TAny = TAny::from_any(any);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn from_any(boxed: Box<dyn Any + Send + Sync>) -> Self {
        TAny {
            inner: LTAny::from_any(boxed),
        }
    }

    /// Returns the type id of the stored value.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// use core::any::TypeId;
    /// 
    /// let a: TAny = TAny::new(42u32);
    /// 
    /// assert_eq!(a.type_id(), TypeId::of::<u32>());
    /// ```
    #[inline]
    pub fn type_id(&self) -> TypeId {
        self.inner.type_id()
    }

    /// Returns `true` if the stored value is of type `T`.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let a: TAny = TAny::new(42u32);
    /// assert!(a.is::<u32>());
    /// ```
    #[inline]
    pub fn is<T>(&self) -> bool
    where
        T: 'static,
    {
        self.inner.is::<T>()
    }

    /// Returns some reference to the stored value if it is of type `T`.
    /// Otherwise returns none.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let a: TAny = TAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_ref::<u32>().unwrap(), &42);
    /// ```
    #[inline]
    pub fn downcast_ref<T>(&self) -> Option<&T>
    where
        T: 'static,
    {
        self.inner.downcast_ref()
    }

    /// Returns some mutable reference to the stored value if it is of type `T`.
    /// Otherwise returns none.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let mut a: TAny = TAny::new(42u32);
    /// 
    /// assert_eq!(a.downcast_mut::<u32>().unwrap(), &mut 42);
    /// ```
    #[inline]
    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
    where
        T: 'static,
    {
        self.inner.downcast_mut()
    }

    /// Returns the stored value if it is of type `T`.
    /// Otherwise return self back.
    ///
    /// This will unbox the value if it was stored as boxed.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let a: TAny = TAny::new(42u32);
    /// 
    /// let Ok(a) = a.downcast::<u32>() else {
    ///    panic!();
    /// };
    /// ```
    #[inline]
    pub fn downcast<T>(self) -> Result<T, TAny>
    where
        T: 'static,
    {
        if self.is::<T>() {
            Ok(unsafe { self.inner.downcast_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Returns reference to the stored value without type checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let a: TAny = TAny::new(42u32);
    /// 
    /// unsafe {
    ///    assert_eq!(a.downcast_ref_unchecked::<u32>(), &42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_ref_unchecked<T>(&self) -> &T
    where
        T: 'static,
    {
        self.inner.downcast_ref_unchecked()
    }

    /// Returns mutable reference to the stored value without type checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let mut a: TAny = TAny::new(42u32);
    /// 
    /// unsafe {
    ///   assert_eq!(a.downcast_mut_unchecked::<u32>(), &mut 42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_mut_unchecked<T>(&mut self) -> &mut T
    where
        T: 'static,
    {
        self.inner.downcast_mut_unchecked()
    }

    /// Returns the stored value without type checking.
    ///
    /// This will unbox the value if it was stored as boxed.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the type is correct.
    /// 
    /// # Example
    /// 
    /// ```
    /// # use tany::TAny;
    /// let a: TAny = TAny::new(42u32);
    /// 
    /// unsafe {
    ///  assert_eq!(a.downcast_unchecked::<u32>(), 42);
    /// }
    /// ```
    #[inline]
    pub unsafe fn downcast_unchecked<T>(self) -> T
    where
        T: 'static,
    {
        self.inner.downcast_unchecked()
    }
}
