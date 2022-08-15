use std::{any::TypeId, fmt::Debug};

use rustc_hash::FxHashMap;

use std::collections::hash_map;
use std::marker::PhantomData;

/// Stores an owned, type-erased pointer.
struct OwnedPtr {
    ptr: *mut u8,
    // function that drops this pointer's allocation.
    drop: fn(*mut u8),
}

impl OwnedPtr {
    fn new<T: 'static>(val: T) -> Self {
        Self {
            ptr: Box::into_raw(Box::new(val)) as *mut u8,
            drop: |ptr| {
                // SAFETY: `ptr` was originally obtained from calling `Box<T>::into_raw`.
                // This closure will only get called in the destructor of `OwnedPtr`, which only happens once.
                let boxed = unsafe { Box::from_raw(ptr as *mut T) };
                std::mem::drop(boxed);
            },
        }
    }

    unsafe fn downcast_unchecked<T: 'static>(self) -> T {
        // Make sure this instance doesn't get double dropped.
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: `self.ptr` was originally obtained from `Box::into_raw`, so we can call `from_raw`.
        let boxed = Box::from_raw(this.ptr as *mut T);
        *boxed
    }
    unsafe fn downcast_ref_unchecked<T: 'static>(&self) -> &T {
        &*(self.ptr as *mut T)
    }
    unsafe fn downcast_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        &mut *(self.ptr as *mut T)
    }
}

impl Drop for OwnedPtr {
    #[inline]
    fn drop(&mut self) {
        (self.drop)(self.ptr)
    }
}

impl Debug for OwnedPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("Any").finish_non_exhaustive()
    }
}

/// Prepared key-value pair
pub struct KvPair(TypeId, OwnedPtr);

impl KvPair {
    pub fn new<T: 'static>(value: T) -> Self {
        KvPair(TypeId::of::<T>(), OwnedPtr::new(value))
    }

    pub fn extract<T: 'static>(self) -> Result<T, Self> {
        let KvPair(key, value) = self;
        if key == TypeId::of::<T>() {
            // SAFETY: This type can only be constructed by the associated fn `new`,
            // which guarantees that `key` matches the type of `value`.
            Ok(unsafe { value.downcast_unchecked() })
        } else {
            Err(Self(key, value))
        }
    }
}

type InnerOccupiedEntry<'a> = hash_map::OccupiedEntry<'a, TypeId, OwnedPtr>;
type InnerVacantEntry<'a> = hash_map::VacantEntry<'a, TypeId, OwnedPtr>;
type InnerEntry<'a> = hash_map::Entry<'a, TypeId, OwnedPtr>;

/// A view into an occupied entry in a `TypeMap`.
#[derive(Debug)]
pub struct OccupiedEntry<'a, T> {
    data: InnerOccupiedEntry<'a>,
    marker: PhantomData<fn(T)>,
}

// SAFETY: In order for a type to be `Send`, it must not share mutable state with anything else.
// If the wrapped type is `Send`, then the entry can be too as the HashMap itself never shares mutability.
unsafe impl<'a, T: Send> Send for OccupiedEntry<'a, T> {}
// SAFETY: In order for a type to be `Sync`, it must not allow unsychronized interior mutability.
// If the wrapped type is `Sync`, then the entry can be too as the HashMap itself never allows interior mutability.
unsafe impl<'a, T: Sync> Sync for OccupiedEntry<'a, T> {}

impl<'a, T: 'static> OccupiedEntry<'a, T> {
    /// # Safety
    /// The key of the inner occupied entry must match `TypeId::of::<T>()`.
    /// Also, the value must have originally been constructed from a value of type `T`.
    unsafe fn new(data: InnerOccupiedEntry<'a>) -> Self {
        Self {
            data,
            marker: PhantomData,
        }
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &T {
        let val = self.data.get();
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { val.downcast_ref_unchecked() }
    }

    ///Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut T {
        let val = self.data.get_mut();
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { val.downcast_mut_unchecked() }
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    pub fn into_mut(self) -> &'a mut T {
        let val = self.data.into_mut();
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { val.downcast_mut_unchecked() }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, value: T) -> T {
        let old = self.data.insert(OwnedPtr::new(value));
        // SAFETY: `old` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { old.downcast_unchecked() }
    }

    /// Takes the value out of the entry, and returns it.    
    pub fn remove(self) -> T {
        let val = self.data.remove();
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { val.downcast_unchecked() }
    }
}

/// A view into a vacant entry in a `TypeMap`.
#[derive(Debug)]
pub struct VacantEntry<'a, T> {
    data: InnerVacantEntry<'a>,
    marker: PhantomData<fn(T)>,
}

impl<'a, T: 'static> VacantEntry<'a, T> {
    /// # Safety
    /// The key of the inner vacant entry must match `TypeId::of::<T>()`.
    unsafe fn new(data: InnerVacantEntry<'a>) -> Self {
        Self {
            data,
            marker: PhantomData,
        }
    }

    /// Sets the value of the entry with the key of the `VacantEntry`, and returns a mutable reference to it.
    pub fn insert(self, value: T) -> &'a mut T {
        let new = self.data.insert(OwnedPtr::new(value));
        // SAFETY: We just created `new` by boxing a value of type `T`, so we can safely downcast it back.
        unsafe { new.downcast_mut_unchecked() }
    }
}

// SAFETY: In order for a type to be `Send`, it must not share mutable state with anything else.
// If the wrapped type is `Send`, then the entry can be too as the HashMap itself never shares mutability.
unsafe impl<'a, T: Send> Send for VacantEntry<'a, T> {}
// SAFETY: In order for a type to be `Sync`, it must not allow unsychronized interior mutability.
// If the wrapped type is `Sync`, then the entry can be too as the HashMap itself never allows interior mutability.
unsafe impl<'a, T: Sync> Sync for VacantEntry<'a, T> {}

/// A view into a single entry in a map, which may either be vacant or occupied.
#[derive(Debug)]
pub enum Entry<'a, T> {
    Occupied(OccupiedEntry<'a, T>),
    Vacant(VacantEntry<'a, T>),
}

impl<'a, T: 'static> Entry<'a, T> {
    /// # Safety
    /// The key of the inner entry must match `TypeId::of::<T>()`.
    /// If the entry has a value (`Box<dyn Any>`), then it must have originally been constructed from a value of type `T`.
    unsafe fn new(inner: InnerEntry<'a>) -> Self {
        match inner {
            hash_map::Entry::Occupied(e) => Self::Occupied(OccupiedEntry::new(e)),
            hash_map::Entry::Vacant(e) => Self::Vacant(VacantEntry::new(e)),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(inner) => inner.into_mut(),
            Entry::Vacant(inner) => inner.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty, and returns
    /// a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(inner) => inner.into_mut(),
            Entry::Vacant(inner) => inner.insert(default()),
        }
    }
}

#[derive(Debug, Default)]
/// The typemap container
pub struct TypeMap {
    map: Option<FxHashMap<TypeId, OwnedPtr>>,
}

impl TypeMap {
    /// Create an empty `TypeMap`.
    #[inline]
    pub const fn new() -> Self {
        Self { map: None }
    }

    /// Insert a prepared `KvPair` into this `TypeMap`.
    ///
    /// If a value of this type already exists, it will be returned.
    pub fn insert_kv_pair(&mut self, KvPair(key, value): KvPair) -> Option<KvPair> {
        self.map
            .get_or_insert_with(FxHashMap::default)
            .insert(key, value)
            .map(|old_value| KvPair(key, old_value))
    }

    /// Insert a value into this `TypeMap`.
    ///
    /// If a value of this type already exists, it will be returned.
    pub fn insert<T: 'static>(&mut self, val: T) -> Option<T> {
        let old = self
            .map
            .get_or_insert_with(FxHashMap::default)
            .insert(TypeId::of::<T>(), OwnedPtr::new(val))?;
        // SAFETY: `old` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        unsafe { old.downcast_unchecked() }
    }

    /// Check if container contains value for type
    pub fn contains<T: 'static>(&self) -> bool {
        self.map.as_ref().and_then(|m| m.get(&TypeId::of::<T>())).is_some()
    }

    /// Get a reference to a value previously inserted on this `TypeMap`.
    pub fn get<T: 'static>(&self) -> Option<&T> {
        let val = self.map.as_ref()?.get(&TypeId::of::<T>())?;
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        Some(unsafe { val.downcast_ref_unchecked() })
    }

    /// Get a mutable reference to a value previously inserted on this `TypeMap`.
    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let val = self.map.as_mut()?.get_mut(&TypeId::of::<T>())?;
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        Some(unsafe { val.downcast_mut_unchecked() })
    }

    /// Remove a value from this `TypeMap`.
    ///
    /// If a value of this type exists, it will be returned.
    pub fn remove<T: 'static>(&mut self) -> Option<T> {
        let val = self.map.as_mut()?.remove(&TypeId::of::<T>())?;
        // SAFETY: `val` was keyed with the TypeId of `T`, thus it is guaranteed to be of type `T`.
        Some(unsafe { val.downcast_unchecked() })
    }

    /// Clear the `TypeMap` of all inserted values.
    #[inline]
    pub fn clear(&mut self) {
        self.map = None;
    }

    /// Get an entry in the `TypeMap` for in-place manipulation.
    pub fn entry<T: 'static>(&mut self) -> Entry<T> {
        let inner_entry = self
            .map
            .get_or_insert_with(FxHashMap::default)
            .entry(TypeId::of::<T>());
        // SAFETY: If the entry is occupied, then we know its value matches
        // as it was keyed with the TypeId of `T`.
        unsafe { Entry::new(inner_entry) }
    }
}

/// Provides the same `TypeMap` container, but with `Send` + `Sync` bounds on values
pub mod concurrent {
    /// Prepared key-value pair
    pub struct KvPair(super::KvPair);

    impl KvPair {
        pub fn new<T: 'static + Send + Sync>(value: T) -> Self {
            Self(super::KvPair::new(value))
        }

        pub fn extract<T: 'static + Send + Sync>(self) -> Result<T, Self> {
            self.0.extract().map_err(Self)
        }
    }

    // SAFETY: `KvPair` can only be constructed through the associated fn `new`,
    // which guarantees that the wrapped value must be `Send`.
    unsafe impl Send for KvPair {}
    // SAFETY: Same as `Send`.
    unsafe impl Sync for KvPair {}

    #[derive(Debug, Default)]
    /// The typemap container
    pub struct TypeMap(super::TypeMap);

    impl TypeMap {
        /// Create an empty `TypeMap`.
        #[inline]
        pub const fn new() -> Self {
            Self(super::TypeMap::new())
        }

        /// Insert a prepared `KvPair` into this `TypeMap`.
        ///
        /// If a value of this type already exists, it will be returned.
        pub fn insert_kv_pair(&mut self, KvPair(pair): KvPair) -> Option<KvPair> {
            self.0.insert_kv_pair(pair).map(KvPair)
        }

        /// Insert a value into this `TypeMap`.
        ///
        /// If a value of this type already exists, it will be returned.
        pub fn insert<T: 'static + Send + Sync>(&mut self, val: T) -> Option<T> {
            self.0.insert(val)
        }

        /// Check if container contains value for type
        pub fn contains<T: 'static>(&self) -> bool {
            self.0.contains::<T>()
        }

        /// Get a reference to a value previously inserted on this `TypeMap`.
        pub fn get<T: 'static>(&self) -> Option<&T> {
            self.0.get()
        }

        /// Get a mutable reference to a value previously inserted on this `TypeMap`.
        pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
            self.0.get_mut()
        }

        /// Remove a value from this `TypeMap`.
        ///
        /// If a value of this type exists, it will be returned.
        pub fn remove<T: 'static>(&mut self) -> Option<T> {
            self.0.remove()
        }

        /// Clear the `TypeMap` of all inserted values.
        #[inline]
        pub fn clear(&mut self) {
            self.0.clear()
        }

        /// Get an entry in the `TypeMap` for in-place manipulation.
        pub fn entry<T: 'static + Send + Sync>(&mut self) -> super::Entry<T> {
            self.0.entry()
        }
    }

    // SAFETY: The methods of `TypeMap` ensure that only `Send` types can be inserted.
    unsafe impl Send for TypeMap {}
    // SAFETY: Same as `Send`.
    unsafe impl Sync for TypeMap {}
}

#[test]
fn test_type_map() {
    #[derive(Debug, PartialEq)]
    struct MyType(i32);

    #[derive(Debug, PartialEq, Default)]
    struct MyType2(String);

    let mut map = TypeMap::new();

    map.insert(5i32);
    map.insert(MyType(10));

    assert_eq!(map.get(), Some(&5i32));
    assert_eq!(map.get_mut(), Some(&mut 5i32));

    assert_eq!(map.remove::<i32>(), Some(5i32));
    assert!(map.get::<i32>().is_none());

    assert_eq!(map.get::<bool>(), None);
    assert_eq!(map.get(), Some(&MyType(10)));

    let entry = map.entry::<MyType2>();

    let mut v = entry.or_insert_with(MyType2::default);

    v.0 = "Hello".into();

    assert_eq!(map.get(), Some(&MyType2("Hello".into())));
}
