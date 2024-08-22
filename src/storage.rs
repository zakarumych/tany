use core::mem::{align_of, size_of, MaybeUninit};

const TANY_STORAGE_SIZE: usize = size_of::<[usize; 3]>();
const TANY_STORAGE_ALIGN: usize = 8;

/// Storage type that can hold any value of size `TANY_STORAGE_SIZE` and alignment `TANY_STORAGE_ALIGN`.
#[repr(C, align(8))] // alignment value is in synced with `TANY_STORAGE_ALIGN`
#[derive(Clone, Copy)]
pub(crate) struct InlineStorage {
    pub storage: MaybeUninit<[u8; TANY_STORAGE_SIZE]>,
}

impl InlineStorage {
    /// Construct new storage without initializing any value in it.
    pub fn new() -> Self {
        InlineStorage {
            storage: MaybeUninit::uninit(),
        }
    }

    /// Returns `true` if the type `T` fits into the storage.
    pub const fn fits<T>() -> bool {
        size_of::<T>() <= TANY_STORAGE_SIZE && align_of::<T>() <= TANY_STORAGE_ALIGN
    }

    /// Returns reference to the potentially uninitialized value.
    /// Type must be not larger than `TANY_STORAGE_SIZE` and not more aligned than `TANY_STORAGE_ALIGN`.
    ///
    /// The caller is responsible to ensure that the type is correct and the value is initialized before accessing it.
    pub fn as_ref<T>(&self) -> &MaybeUninit<T> {
        // This can't be const, because then it'll be checked in branches that are not taken.
        assert!(size_of::<T>() <= TANY_STORAGE_SIZE);
        assert!(align_of::<T>() <= TANY_STORAGE_ALIGN);

        // Safety: This cast is safe due to the size and alignment constraints.
        unsafe { &*self.storage.as_ptr().cast() }
    }

    /// Returns mutable reference to the potentially uninitialized value.
    /// Type must be not larger than `TANY_STORAGE_SIZE` and not more aligned than `TANY_STORAGE_ALIGN`.
    ///
    /// The caller is responsible to ensure that the type is correct and the value is initialized before accessing it.
    pub fn as_mut<T>(&mut self) -> &mut MaybeUninit<T> {
        // This can't be const, because then it'll be checked in branches that are not taken.
        assert!(size_of::<T>() <= TANY_STORAGE_SIZE);
        assert!(align_of::<T>() <= TANY_STORAGE_ALIGN);

        // Safety: This cast is safe due to the size and alignment constraints.
        unsafe { &mut *self.storage.as_mut_ptr().cast() }
    }
}
