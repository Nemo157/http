use std::collections::{hash_map, HashMap};
use std::convert::TryFrom;
use std::hash::Hash;
use std::iter::{self, FromIterator, FusedIterator};
use std::{fmt, ops, slice};
use std::marker::PhantomData;
use smallvec::{SmallVec, smallvec};

use crate::Error;

use super::HeaderValue;
use super::name::{HeaderName, InvalidHeaderName};

pub use self::as_header_name::AsHeaderName;
pub use self::into_header_name::IntoHeaderName;

/// A set of HTTP headers
///
/// `HeaderMap` is an multimap of [`HeaderName`] to values.
///
/// [`HeaderName`]: struct.HeaderName.html
///
/// # Examples
///
/// Basic usage
///
/// ```
/// # use http::HeaderMap;
/// # use http::header::{CONTENT_LENGTH, HOST, LOCATION};
/// let mut headers = HeaderMap::new();
///
/// headers.insert(HOST, "example.com".parse().unwrap());
/// headers.insert(CONTENT_LENGTH, "123".parse().unwrap());
///
/// assert!(headers.contains_key(HOST));
/// assert!(!headers.contains_key(LOCATION));
///
/// assert_eq!(headers[HOST], "example.com");
///
/// headers.remove(HOST);
///
/// assert!(!headers.contains_key(HOST));
/// ```
#[derive(Clone)]
pub struct HeaderMap<T = HeaderValue> {
    map: HashMap<HeaderName, SmallVec<[T; 1]>>,
}

/// `HeaderMap` entry iterator.
///
/// Yields `(&HeaderName, &value)` tuples. The same header name may be yielded
/// more than once if it has more than one associated value.
#[derive(Debug)]
pub struct Iter<'a, T> {
    inner: iter::FlatMap<hash_map::Iter<'a, HeaderName, SmallVec<[T; 1]>>, iter::Zip<iter::Repeat<&'a HeaderName>, slice::Iter<'a, T>>, fn((&'a HeaderName, &'a SmallVec<[T; 1]>)) -> iter::Zip<iter::Repeat<&'a HeaderName>, slice::Iter<'a, T>>>,
}

/// `HeaderMap` mutable entry iterator
///
/// Yields `(&HeaderName, &mut value)` tuples. The same header name may be
/// yielded more than once if it has more than one associated value.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    inner: iter::FlatMap<hash_map::IterMut<'a, HeaderName, SmallVec<[T; 1]>>, iter::Zip<iter::Repeat<&'a HeaderName>, slice::IterMut<'a, T>>, fn((&'a HeaderName, &'a mut SmallVec<[T; 1]>)) -> iter::Zip<iter::Repeat<&'a HeaderName>, slice::IterMut<'a, T>>>,
}

/// An owning iterator over the entries of a `HeaderMap`.
///
/// This struct is created by the `into_iter` method on `HeaderMap`.
#[derive(Debug)]
pub struct IntoIter<T> {
    inner: iter::FlatMap<hash_map::IntoIter<HeaderName, SmallVec<[T; 1]>>, iter::Zip<iter::Chain<iter::Once<Option<HeaderName>>, iter::Repeat<Option<HeaderName>>>, smallvec::IntoIter<[T; 1]>>, fn((HeaderName, SmallVec<[T; 1]>)) -> iter::Zip<iter::Chain<iter::Once<Option<HeaderName>>, iter::Repeat<Option<HeaderName>>>, smallvec::IntoIter<[T; 1]>>>,
}

/// An iterator over `HeaderMap` keys.
///
/// Each header name is yielded only once, even if it has more than one
/// associated value.
#[derive(Debug)]
pub struct Keys<'a, T> {
    inner: hash_map::Keys<'a, HeaderName, SmallVec<[T; 1]>>,
}

/// `HeaderMap` value iterator.
///
/// Each value contained in the `HeaderMap` will be yielded.
#[derive(Debug)]
pub struct Values<'a, T> {
    inner: iter::Flatten<hash_map::Values<'a, HeaderName, SmallVec<[T; 1]>>>,
}

/// `HeaderMap` mutable value iterator
#[derive(Debug)]
pub struct ValuesMut<'a, T> {
    inner: iter::Flatten<hash_map::ValuesMut<'a, HeaderName, SmallVec<[T; 1]>>>,
}

/// A drain iterator for `HeaderMap`.
#[derive(Debug)]
pub struct Drain<'a, T> {
    inner: iter::FlatMap<hash_map::Drain<'a, HeaderName, SmallVec<[T; 1]>>, iter::Zip<iter::Chain<iter::Once<Option<HeaderName>>, iter::Repeat<Option<HeaderName>>>, smallvec::IntoIter<[T; 1]>>, fn((HeaderName, SmallVec<[T; 1]>)) -> iter::Zip<iter::Chain<iter::Once<Option<HeaderName>>, iter::Repeat<Option<HeaderName>>>, smallvec::IntoIter<[T; 1]>>>,
}

/// A view to all values stored in a single entry.
///
/// This struct is returned by `HeaderMap::get_all`.
#[derive(Debug)]
pub struct GetAll<'a, T> {
    values: &'a [T],
}

/// A view into a single location in a `HeaderMap`, which may be vacant or occupied.
#[derive(Debug)]
pub enum Entry<'a, T: 'a> {
    /// An occupied entry
    Occupied(OccupiedEntry<'a, T>),

    /// A vacant entry
    Vacant(VacantEntry<'a, T>),
}

/// A view into a single empty location in a `HeaderMap`.
///
/// This struct is returned as part of the `Entry` enum.
#[derive(Debug)]
pub struct VacantEntry<'a, T> {
    inner: hash_map::VacantEntry<'a, HeaderName, SmallVec<[T; 1]>>,
}

/// A view into a single occupied location in a `HeaderMap`.
///
/// This struct is returned as part of the `Entry` enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, T> {
    inner: hash_map::OccupiedEntry<'a, HeaderName, SmallVec<[T; 1]>>,
    index: usize,
}

/// An iterator of all values associated with a single header name.
#[derive(Debug)]
pub struct ValueIter<'a, T> {
    inner: slice::Iter<'a, T>,
}

/// A mutable iterator of all values associated with a single header name.
#[derive(Debug)]
pub struct ValueIterMut<'a, T> {
    inner: slice::IterMut<'a, T>,
}

/// An drain iterator of all values associated with a single header name.
#[derive(Debug)]
pub struct ValueDrain<'a, T> {
    inner: smallvec::IntoIter<[T; 1]>,
    _marker: PhantomData<&'a mut HeaderMap>,
}

/// Type used for representing the size of a HeaderMap value.
///
/// 32,768 is more than enough entries for a single header map. Setting this
/// limit enables using `u16` to represent all offsets, which takes 2 bytes
/// instead of 8 on 64 bit processors.
///
/// Setting this limit is especially benificial for `indices`, making it more
/// cache friendly. More hash codes can fit in a cache line.
///
/// You may notice that `u16` may represent more than 32,768 values. This is
/// true, but 32,768 should be plenty and it allows us to reserve the top bit
/// for future usage.
type Size = usize;

/// This limit falls out from above.
const MAX_SIZE: usize = (1 << 15);

impl HeaderMap {
    /// Create an empty `HeaderMap`.
    ///
    /// The map will be created without any capacity. This function will not
    /// allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let map = HeaderMap::new();
    ///
    /// assert!(map.is_empty());
    /// assert_eq!(0, map.capacity());
    /// ```
    pub fn new() -> Self {
        HeaderMap::with_capacity(0)
    }
}

impl<T> HeaderMap<T> {
    /// Create an empty `HeaderMap` with the specified capacity.
    ///
    /// The returned map will allocate internal storage in order to hold about
    /// `capacity` elements without reallocating. However, this is a "best
    /// effort" as there are usage patterns that could cause additional
    /// allocations before `capacity` headers are stored in the map.
    ///
    /// More capacity than requested may be allocated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let map: HeaderMap<u32> = HeaderMap::with_capacity(10);
    ///
    /// assert!(map.is_empty());
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> HeaderMap<T> {
        HeaderMap { map: HashMap::with_capacity(capacity) }
    }

    /// Returns the number of headers stored in the map.
    ///
    /// This number represents the total number of **values** stored in the map.
    /// This number can be greater than or equal to the number of **keys**
    /// stored given that a single key may have more than one associated value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{ACCEPT, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// assert_eq!(0, map.len());
    ///
    /// map.insert(ACCEPT, "text/plain".parse().unwrap());
    /// map.insert(HOST, "localhost".parse().unwrap());
    ///
    /// assert_eq!(2, map.len());
    ///
    /// map.append(ACCEPT, "text/html".parse().unwrap());
    ///
    /// assert_eq!(3, map.len());
    /// ```
    pub fn len(&self) -> usize {
        self.map.iter().map(|(_, values)| values.len()).sum()
    }

    /// Returns the number of keys stored in the map.
    ///
    /// This number will be less than or equal to `len()` as each key may have
    /// more than one associated value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{ACCEPT, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// assert_eq!(0, map.keys_len());
    ///
    /// map.insert(ACCEPT, "text/plain".parse().unwrap());
    /// map.insert(HOST, "localhost".parse().unwrap());
    ///
    /// assert_eq!(2, map.keys_len());
    ///
    /// map.insert(ACCEPT, "text/html".parse().unwrap());
    ///
    /// assert_eq!(2, map.keys_len());
    /// ```
    pub fn keys_len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    ///
    /// assert!(map.is_empty());
    ///
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// assert!(map.capacity() > 0);
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns the number of headers the map can hold without reallocating.
    ///
    /// This number is an approximation as certain usage patterns could cause
    /// additional allocations before the returned capacity is filled.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    ///
    /// assert_eq!(0, map.capacity());
    ///
    /// map.insert(HOST, "hello.world".parse().unwrap());
    /// assert!(map.capacity() >= 1);
    /// ```
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Reserves capacity for at least `additional` more headers to be inserted
    /// into the `HeaderMap`.
    ///
    /// The header map may reserve more space to avoid frequent reallocations.
    /// Like with `with_capacity`, this will be a "best effort" to avoid
    /// allocations until `additional` more headers are inserted. Certain usage
    /// patterns could cause additional allocations before the number is
    /// reached.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// map.reserve(10);
    /// # map.insert(HOST, "bar".parse().unwrap());
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        // TODO: This can't overflow if done properly... since the max # of
        // elements is u16::MAX.
        let cap = self.map.len().checked_add(additional).expect("reserve overflow");

        if cap > self.map.capacity() {
            let cap = cap.next_power_of_two();
            assert!(cap < MAX_SIZE, "header map reserve over max capacity");
            self.map.reserve(additional)
        }
    }

    /// Returns a reference to the value associated with the key.
    ///
    /// If there are multiple values associated with the key, then the first one
    /// is returned. Use `get_all` to get all values associated with a given
    /// key. Returns `None` if there are no values associated with the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// assert!(map.get("host").is_none());
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// assert_eq!(map.get(HOST).unwrap(), &"hello");
    /// assert_eq!(map.get("host").unwrap(), &"hello");
    ///
    /// map.append(HOST, "world".parse().unwrap());
    /// assert_eq!(map.get("host").unwrap(), &"hello");
    /// ```
    pub fn get<K>(&self, key: K) -> Option<&T>
    where
        K: AsHeaderName,
    {
        key.with_header_name(|key| self.map.get(key).and_then(|values| values.first())).unwrap_or(None)
    }

    /// Returns a mutable reference to the value associated with the key.
    ///
    /// If there are multiple values associated with the key, then the first one
    /// is returned. Use `entry` to get all values associated with a given
    /// key. Returns `None` if there are no values associated with the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::default();
    /// map.insert(HOST, "hello".to_string());
    /// map.get_mut("host").unwrap().push_str("-world");
    ///
    /// assert_eq!(map.get(HOST).unwrap(), &"hello-world");
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut T>
    where
        K: AsHeaderName,
    {
        key.with_header_name(move |key| self.map.get_mut(key).and_then(|values| values.first_mut())).unwrap_or(None)
    }

    /// Returns a view of all values associated with a key.
    ///
    /// The returned view does not incur any allocations and allows iterating
    /// the values associated with the key.  See [`GetAll`] for more details.
    /// Returns `None` if there are no values associated with the key.
    ///
    /// [`GetAll`]: struct.GetAll.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// map.append(HOST, "goodbye".parse().unwrap());
    ///
    /// let view = map.get_all("host");
    ///
    /// let mut iter = view.iter();
    /// assert_eq!(&"hello", iter.next().unwrap());
    /// assert_eq!(&"goodbye", iter.next().unwrap());
    /// assert!(iter.next().is_none());
    /// ```
    pub fn get_all<K>(&self, key: K) -> GetAll<'_, T>
    where
        K: AsHeaderName,
    {
        key.with_header_name(|key| self.map.get(key).map(|values| GetAll { values })).ok().flatten().unwrap_or(GetAll { values: &[] })
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// assert!(!map.contains_key(HOST));
    ///
    /// map.insert(HOST, "world".parse().unwrap());
    /// assert!(map.contains_key("host"));
    /// ```
    pub fn contains_key<K>(&self, key: K) -> bool
    where
        K: AsHeaderName,
    {
        key.with_header_name(|key| self.map.contains_key(key)).unwrap_or(false)
    }

    /// An iterator visiting all key-value pairs.
    ///
    /// The iteration order is arbitrary, but consistent across platforms for
    /// the same crate version. Each key will be yielded once per associated
    /// value. So, if a key has 3 associated values, it will be yielded 3 times.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// map.append(HOST, "goodbye".parse().unwrap());
    /// map.insert(CONTENT_LENGTH, "123".parse().unwrap());
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{:?}: {:?}", key, value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.map.iter().flat_map(|(header, values)| iter::repeat(header).zip(values.iter())),
        }
    }

    /// An iterator visiting all key-value pairs, with mutable value references.
    ///
    /// The iterator order is arbitrary, but consistent across platforms for the
    /// same crate version. Each key will be yielded once per associated value,
    /// so if a key has 3 associated values, it will be yielded 3 times.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::default();
    ///
    /// map.insert(HOST, "hello".to_string());
    /// map.append(HOST, "goodbye".to_string());
    /// map.insert(CONTENT_LENGTH, "123".to_string());
    ///
    /// for (key, value) in map.iter_mut() {
    ///     value.push_str("-boop");
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner: self.map.iter_mut().flat_map(|(header, values)| iter::repeat(header).zip(values.iter_mut())),
        }
    }

    /// An iterator visiting all keys.
    ///
    /// The iteration order is arbitrary, but consistent across platforms for
    /// the same crate version. Each key will be yielded only once even if it
    /// has multiple associated values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// map.append(HOST, "goodbye".parse().unwrap());
    /// map.insert(CONTENT_LENGTH, "123".parse().unwrap());
    ///
    /// for key in map.keys() {
    ///     println!("{:?}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, T> {
        Keys {
            inner: self.map.keys(),
        }
    }

    /// An iterator visiting all values.
    ///
    /// The iteration order is arbitrary, but consistent across platforms for
    /// the same crate version.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// map.append(HOST, "goodbye".parse().unwrap());
    /// map.insert(CONTENT_LENGTH, "123".parse().unwrap());
    ///
    /// for value in map.values() {
    ///     println!("{:?}", value);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, T> {
        Values {
            inner: self.map.values().flatten()
        }
    }

    /// An iterator visiting all values mutably.
    ///
    /// The iteration order is arbitrary, but consistent across platforms for
    /// the same crate version.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::default();
    ///
    /// map.insert(HOST, "hello".to_string());
    /// map.append(HOST, "goodbye".to_string());
    /// map.insert(CONTENT_LENGTH, "123".to_string());
    ///
    /// for value in map.values_mut() {
    ///     value.push_str("-boop");
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, T> {
        ValuesMut {
            inner: self.map.values_mut().flatten()
        }
    }

    /// Clears the map, returning all entries as an iterator.
    ///
    /// The internal memory is kept for reuse.
    ///
    /// For each yielded item that has `None` provided for the `HeaderName`,
    /// then the associated header name is the same as that of the previously
    /// yielded item. The first yielded item will have `HeaderName` set.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::{CONTENT_LENGTH, HOST};
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(HOST, "hello".parse().unwrap());
    /// map.append(HOST, "goodbye".parse().unwrap());
    /// map.insert(CONTENT_LENGTH, "123".parse().unwrap());
    ///
    /// let mut drain = map.drain().peekable();
    ///
    /// while let Some((Some(header), _)) = drain.peek() {
    ///     match header {
    ///         &HOST => {
    ///             assert_eq!(drain.next(), Some((Some(HOST), "hello".parse().unwrap())));
    ///             assert_eq!(drain.next(), Some((None, "goodbye".parse().unwrap())));
    ///         }
    ///         &CONTENT_LENGTH => {
    ///             assert_eq!(drain.next(), Some((Some(CONTENT_LENGTH), "123".parse().unwrap())));
    ///         }
    ///         header => panic!("unexpected header {}", header),
    ///     }
    /// }
    /// ```
    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain {
            inner: self.map.drain().flat_map(|(header, values)| iter::once(Some(header)).chain(iter::repeat(None)).zip(values)),
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place
    /// manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let mut map: HeaderMap<u32> = HeaderMap::default();
    ///
    /// let headers = &[
    ///     "content-length",
    ///     "x-hello",
    ///     "Content-Length",
    ///     "x-world",
    /// ];
    ///
    /// for &header in headers {
    ///     let counter = map.entry(header).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(map["content-length"], 2);
    /// assert_eq!(map["x-hello"], 1);
    /// ```
    pub fn entry<K>(&mut self, key: K) -> Entry<'_, T>
    where
        K: IntoHeaderName,
    {
        match self.map.entry(key.into_header_name()) {
            hash_map::Entry::Vacant(inner) => Entry::Vacant(VacantEntry { inner }),
            hash_map::Entry::Occupied(inner) => Entry::Occupied(OccupiedEntry { inner, index: 0 }),
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place
    /// manipulation.
    ///
    /// # Errors
    ///
    /// This method differs from `entry` by allowing types that may not be
    /// valid `HeaderName`s to passed as the key (such as `String`). If they
    /// do not parse as a valid `HeaderName`, this returns an
    /// `InvalidHeaderName` error.
    pub fn try_entry<K>(&mut self, key: K) -> Result<Entry<'_, T>, InvalidHeaderName>
    where
        K: AsHeaderName,
    {
        key.with_header_name(move |key| self.entry(key))
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not previously have this key present, then `None` is
    /// returned.
    ///
    /// If the map did have this key present, the new value is associated with
    /// the key and all previous values are removed. **Note** that only a single
    /// one of the previous values is returned. If there are multiple values
    /// that have been previously associated with the key, then the first one is
    /// returned. See `insert_mult` on `OccupiedEntry` for an API that returns
    /// all values.
    ///
    /// The key is not updated, though; this matters for types that can be `==`
    /// without being identical.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// assert!(map.insert(HOST, "world".parse().unwrap()).is_none());
    /// assert!(!map.is_empty());
    ///
    /// let mut prev = map.insert(HOST, "earth".parse().unwrap()).unwrap();
    /// assert_eq!("world", prev);
    /// ```
    pub fn insert<K>(&mut self, key: K, val: T) -> Option<T>
    where
        K: IntoHeaderName,
    {
        self.map.insert(key.into_header_name(), smallvec![val]).and_then(|values| values.into_iter().next())
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not previously have this key present, then `false` is
    /// returned.
    ///
    /// If the map did have this key present, the new value is pushed to the end
    /// of the list of values currently associated with the key. The key is not
    /// updated, though; this matters for types that can be `==` without being
    /// identical.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// assert!(map.insert(HOST, "world".parse().unwrap()).is_none());
    /// assert!(!map.is_empty());
    ///
    /// map.append(HOST, "earth".parse().unwrap());
    ///
    /// let values = map.get_all("host");
    /// let mut i = values.iter();
    /// assert_eq!("world", *i.next().unwrap());
    /// assert_eq!("earth", *i.next().unwrap());
    /// ```
    pub fn append<K>(&mut self, key: K, value: T) -> bool
    where
        K: IntoHeaderName,
    {
        match self.map.entry(key.into_header_name()) {
            hash_map::Entry::Vacant(entry) => {
                entry.insert(smallvec![value]);
                false
            }
            hash_map::Entry::Occupied(entry) => {
                entry.into_mut().push(value);
                true
            }
        }
    }

    /// Removes a key from the map, returning the value associated with the key.
    ///
    /// Returns `None` if the map does not contain the key. If there are
    /// multiple values associated with the key, then the first one is returned.
    /// See `remove_entry_mult` on `OccupiedEntry` for an API that yields all
    /// values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// let prev = map.remove(HOST).unwrap();
    /// assert_eq!("hello.world", prev);
    ///
    /// assert!(map.remove(HOST).is_none());
    /// ```
    pub fn remove<K>(&mut self, key: K) -> Option<T>
    where
        K: AsHeaderName,
    {
        key.with_header_name(|key| self.map.remove(key).and_then(|values| values.into_iter().next())).unwrap_or(None)
    }
}

impl<'a, T> IntoIterator for &'a HeaderMap<T> {
    type Item = (&'a HeaderName, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut HeaderMap<T> {
    type Item = (&'a HeaderName, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T> IntoIterator for HeaderMap<T> {
    type Item = (Option<HeaderName>, T);
    type IntoIter = IntoIter<T>;

    /// Creates a consuming iterator, that is, one that moves keys and values
    /// out of the map in arbitrary order. The map cannot be used after calling
    /// this.
    ///
    /// For each yielded item that has `None` provided for the `HeaderName`,
    /// then the associated header name is the same as that of the previously
    /// yielded item. The first yielded item will have `HeaderName` set.
    ///
    /// # Examples
    ///
    /// Basic usage.
    ///
    /// ```
    /// # use http::header;
    /// # use http::header::*;
    /// let mut map = HeaderMap::new();
    /// map.insert(header::CONTENT_LENGTH, "123".parse().unwrap());
    /// map.insert(header::CONTENT_TYPE, "json".parse().unwrap());
    ///
    /// let mut iter = map.into_iter().peekable();
    ///
    /// while let Some((Some(header), _)) = iter.peek() {
    ///     match header {
    ///         &CONTENT_LENGTH => {
    ///             assert_eq!(iter.next(), Some((Some(header::CONTENT_LENGTH), "123".parse().unwrap())));
    ///         }
    ///         &CONTENT_TYPE => {
    ///             assert_eq!(iter.next(), Some((Some(CONTENT_TYPE), "json".parse().unwrap())));
    ///         }
    ///         header => panic!("unexpected header {}", header),
    ///     }
    /// }
    /// ```
    ///
    /// Multiple values per key.
    ///
    /// ```
    /// # use http::header;
    /// # use http::header::*;
    /// let mut map = HeaderMap::new();
    ///
    /// map.append(header::CONTENT_LENGTH, "123".parse().unwrap());
    /// map.append(header::CONTENT_LENGTH, "456".parse().unwrap());
    ///
    /// map.append(header::CONTENT_TYPE, "json".parse().unwrap());
    /// map.append(header::CONTENT_TYPE, "html".parse().unwrap());
    /// map.append(header::CONTENT_TYPE, "xml".parse().unwrap());
    ///
    /// let mut iter = map.into_iter().peekable();
    ///
    /// while let Some((Some(header), _)) = iter.peek() {
    ///     match header {
    ///         &CONTENT_LENGTH => {
    ///             assert_eq!(iter.next(), Some((Some(header::CONTENT_LENGTH), "123".parse().unwrap())));
    ///             assert_eq!(iter.next(), Some((None, "456".parse().unwrap())));
    ///         }
    ///         &CONTENT_TYPE => {
    ///             assert_eq!(iter.next(), Some((Some(header::CONTENT_TYPE), "json".parse().unwrap())));
    ///             assert_eq!(iter.next(), Some((None, "html".parse().unwrap())));
    ///             assert_eq!(iter.next(), Some((None, "xml".parse().unwrap())));
    ///         }
    ///         header => panic!("unexpected header {}", header),
    ///     }
    /// }
    /// ```
    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            inner: self.map.into_iter().flat_map(|(header, values)| iter::once(Some(header)).chain(iter::repeat(None)).zip(values)),
        }
    }
}

impl<T> FromIterator<(HeaderName, T)> for HeaderMap<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (HeaderName, T)>,
    {
        let mut map = HeaderMap::default();
        map.extend(iter);
        map
    }
}

/// Try to convert a `HashMap` into a `HeaderMap`.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
/// use std::convert::TryInto;
/// use http::HeaderMap;
///
/// let mut map = HashMap::new();
/// map.insert("X-Custom-Header".to_string(), "my value".to_string());
///
/// let headers: HeaderMap = (&map).try_into().expect("valid headers");
/// assert_eq!(headers["X-Custom-Header"], "my value");
/// ```
impl<'a, K, V, T> TryFrom<&'a HashMap<K, V>> for HeaderMap<T>
    where
        K: Eq + Hash,
        HeaderName: TryFrom<&'a K>,
        <HeaderName as TryFrom<&'a K>>::Error: Into<crate::Error>,
        T: TryFrom<&'a V>,
        T::Error: Into<crate::Error>,
{
    type Error = Error;

    fn try_from(c: &'a HashMap<K, V>) -> Result<Self, Self::Error> {
        c.into_iter()
            .map(|(k, v)| -> crate::Result<(HeaderName, T)> {
                let name = TryFrom::try_from(k).map_err(Into::into)?;
                let value = TryFrom::try_from(v).map_err(Into::into)?;
                Ok((name, value))
            })
            .collect()
    }
}

impl<T> Extend<(Option<HeaderName>, T)> for HeaderMap<T> {
    /// Extend a `HeaderMap` with the contents of another `HeaderMap`.
    ///
    /// This function expects the yielded items to follow the same structure as
    /// `IntoIter`.
    ///
    /// # Panics
    ///
    /// This panics if the first yielded item does not have a `HeaderName`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::*;
    /// let mut map = HeaderMap::new();
    ///
    /// map.insert(ACCEPT, "text/plain".parse().unwrap());
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// let mut extra = HeaderMap::new();
    ///
    /// extra.insert(HOST, "foo.bar".parse().unwrap());
    /// extra.insert(COOKIE, "hello".parse().unwrap());
    /// extra.append(COOKIE, "world".parse().unwrap());
    ///
    /// map.extend(extra);
    ///
    /// assert_eq!(map["host"], "foo.bar");
    /// assert_eq!(map["accept"], "text/plain");
    /// assert_eq!(map["cookie"], "hello");
    ///
    /// let v = map.get_all("host");
    /// assert_eq!(1, v.iter().count());
    ///
    /// let v = map.get_all("cookie");
    /// assert_eq!(2, v.iter().count());
    /// ```
    fn extend<I: IntoIterator<Item = (Option<HeaderName>, T)>>(&mut self, iter: I) {
        let mut iter = iter.into_iter();

        // The structure of this is a bit weird, but it is mostly to make the
        // borrow checker happy.
        let (mut key, mut val) = match iter.next() {
            Some((Some(key), val)) => (key, val),
            Some((None, _)) => panic!("expected a header name, but got None"),
            None => return,
        };

        'outer: loop {
            let values = match self.entry(key) {
                Entry::Occupied(mut e) => {
                    // Replace all previous values while maintaining a handle to
                    // the entry.
                    e.insert(val);
                    e.inner.into_mut()
                }
                Entry::Vacant(e) => e.inner.insert(smallvec![val]),
            };

            // As long as `HeaderName` is none, keep inserting the value into
            // the current entry
            loop {
                match iter.next() {
                    Some((Some(k), v)) => {
                        key = k;
                        val = v;
                        continue 'outer;
                    }
                    Some((None, v)) => {
                        values.push(v);
                    }
                    None => {
                        return;
                    }
                }
            }
        }
    }
}

impl<T> Extend<(HeaderName, T)> for HeaderMap<T> {
    fn extend<I: IntoIterator<Item = (HeaderName, T)>>(&mut self, iter: I) {
        // Keys may be already present or show multiple times in the iterator.
        // Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map
        // will only resize twice in the worst case.
        let iter = iter.into_iter();

        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };

        self.reserve(reserve);

        for (k, v) in iter {
            self.append(k, v);
        }
    }
}

impl<T: PartialEq> PartialEq for HeaderMap<T> {
    fn eq(&self, other: &HeaderMap<T>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.keys().all(|key| self.get_all(key) == other.get_all(key))
    }
}

impl<T: Eq> Eq for HeaderMap<T> {}

impl<T: fmt::Debug> fmt::Debug for HeaderMap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<T> Default for HeaderMap<T> {
    fn default() -> Self {
        HeaderMap::with_capacity(0)
    }
}

impl<'a, K, T> ops::Index<K> for HeaderMap<T>
where
    K: AsHeaderName,
{
    type Output = T;

    /// # Panics
    /// Using the index operator will cause a panic if the header you're querying isn't set.
    #[inline]
    fn index(&self, index: K) -> &T {
        match index.with_header_name(|name| self.get(name)).unwrap_or(None) {
            Some(val) => val,
            None => panic!("no entry found for key {:?}", index.as_str()),
        }
    }
}

// ===== impl Iter =====

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a HeaderName, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}

unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Send for Iter<'a, T> {}

// ===== impl IterMut =====

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (&'a HeaderName, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}
unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}

// ===== impl Keys =====

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = &'a HeaderName;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> ExactSizeIterator for Keys<'a, T> {}
impl<'a, T> FusedIterator for Keys<'a, T> {}

// ===== impl Values ====

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for Values<'a, T> {}

// ===== impl ValuesMut ====

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for ValuesMut<'a, T> {}

// ===== impl Drain =====

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (Option<HeaderName>, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for Drain<'a, T> {}

// ===== impl Entry =====

impl<'a, T> Entry<'a, T> {
    /// Ensures a value is in the entry by inserting the default if empty.
    ///
    /// Returns a mutable reference to the **first** value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let mut map: HeaderMap<u32> = HeaderMap::default();
    ///
    /// let headers = &[
    ///     "content-length",
    ///     "x-hello",
    ///     "Content-Length",
    ///     "x-world",
    /// ];
    ///
    /// for &header in headers {
    ///     let counter = map.entry(header)
    ///         .or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(map["content-length"], 2);
    /// assert_eq!(map["x-hello"], 1);
    /// ```
    pub fn or_insert(self, default: T) -> &'a mut T {
        use self::Entry::*;

        match self {
            Occupied(e) => e.into_mut(),
            Vacant(e) => e.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty.
    ///
    /// The default function is not called if the entry exists in the map.
    /// Returns a mutable reference to the **first** value in the entry.
    ///
    /// # Examples
    ///
    /// Basic usage.
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let mut map = HeaderMap::new();
    ///
    /// let res = map.entry("x-hello")
    ///     .or_insert_with(|| "world".parse().unwrap());
    ///
    /// assert_eq!(res, "world");
    /// ```
    ///
    /// The default function is not called if the entry exists in the map.
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    ///
    /// let res = map.entry("host")
    ///     .or_insert_with(|| unreachable!());
    ///
    ///
    /// assert_eq!(res, "world");
    /// ```
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        use self::Entry::*;

        match self {
            Occupied(e) => e.into_mut(),
            Vacant(e) => e.insert(default()),
        }
    }

    /// Returns a reference to the entry's key
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let mut map = HeaderMap::new();
    ///
    /// assert_eq!(map.entry("x-hello").key(), "x-hello");
    /// ```
    pub fn key(&self) -> &HeaderName {
        use self::Entry::*;

        match *self {
            Vacant(ref e) => e.key(),
            Occupied(ref e) => e.key(),
        }
    }
}

// ===== impl VacantEntry =====

impl<'a, T> VacantEntry<'a, T> {
    /// Returns a reference to the entry's key
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// let mut map = HeaderMap::new();
    ///
    /// assert_eq!(map.entry("x-hello").key().as_str(), "x-hello");
    /// ```
    pub fn key(&self) -> &HeaderName {
        self.inner.key()
    }

    /// Take ownership of the key
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry};
    /// let mut map = HeaderMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("x-hello") {
    ///     assert_eq!(v.into_key().as_str(), "x-hello");
    /// }
    /// ```
    pub fn into_key(self) -> HeaderName {
        self.inner.into_key()
    }

    /// Insert the value into the entry.
    ///
    /// The value will be associated with this entry's key. A mutable reference
    /// to the inserted value will be returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry};
    /// let mut map = HeaderMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("x-hello") {
    ///     v.insert("world".parse().unwrap());
    /// }
    ///
    /// assert_eq!(map["x-hello"], "world");
    /// ```
    pub fn insert(self, value: T) -> &'a mut T {
        self.inner.insert(smallvec![value]).first_mut().unwrap()
    }

    // /// Insert the value into the entry.
    // ///
    // /// The value will be associated with this entry's key. The new
    // /// `OccupiedEntry` is returned, allowing for further manipulation.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// # use http::header::*;
    // /// let mut map = HeaderMap::new();
    // ///
    // /// if let Entry::Vacant(v) = map.entry("x-hello") {
    // ///     let mut e = v.insert_entry("world".parse().unwrap());
    // ///     e.insert("world2".parse().unwrap());
    // /// }
    // ///
    // /// assert_eq!(map["x-hello"], "world2");
    // /// ```
    // pub fn insert_entry(self, value: T) -> OccupiedEntry<'a, T> {
    //     self.inner.insert_entry(smallvec![value]).map(|inner| OccupiedEntry { inner, index: 0 })
    // }
}

// ===== impl GetAll =====

impl<'a, T: 'a> GetAll<'a, T> {
    /// Returns an iterator visiting all values associated with the entry.
    ///
    /// Values are iterated in insertion order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::HeaderMap;
    /// # use http::header::HOST;
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "hello.world".parse().unwrap());
    /// map.append(HOST, "hello.earth".parse().unwrap());
    ///
    /// let values = map.get_all("host");
    /// let mut iter = values.iter();
    /// assert_eq!(&"hello.world", iter.next().unwrap());
    /// assert_eq!(&"hello.earth", iter.next().unwrap());
    /// assert!(iter.next().is_none());
    /// ```
    pub fn iter(&self) -> ValueIter<'a, T> {
        ValueIter { inner: self.values.iter() }
    }
}

impl<'a, T: PartialEq> PartialEq for GetAll<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.values.eq(other.values)
    }
}

impl<'a, T> IntoIterator for GetAll<'a, T> {
    type Item = &'a T;
    type IntoIter = ValueIter<'a, T>;

    fn into_iter(self) -> ValueIter<'a, T> {
        ValueIter { inner: self.values.iter() }
    }
}

impl<'a, 'b: 'a, T> IntoIterator for &'b GetAll<'a, T> {
    type Item = &'a T;
    type IntoIter = ValueIter<'a, T>;

    fn into_iter(self) -> ValueIter<'a, T> {
        ValueIter { inner: self.values.iter() }
    }
}

// ===== impl ValueIter =====

impl<'a, T: 'a> Iterator for ValueIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: 'a> DoubleEndedIterator for ValueIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, T> FusedIterator for ValueIter<'a, T> {}

// ===== impl ValueIterMut =====

impl<'a, T: 'a> Iterator for ValueIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, T: 'a> DoubleEndedIterator for ValueIterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, T> FusedIterator for ValueIterMut<'a, T> {}

// ===== impl IntoIter =====

impl<T> Iterator for IntoIter<T> {
    type Item = (Option<HeaderName>, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> FusedIterator for IntoIter<T> {}

// ===== impl OccupiedEntry =====

impl<'a, T> OccupiedEntry<'a, T> {
    /// Returns a reference to the entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    ///
    /// if let Entry::Occupied(e) = map.entry("host") {
    ///     assert_eq!("host", e.key());
    /// }
    /// ```
    pub fn key(&self) -> &HeaderName {
        self.inner.key()
    }

    /// Get a reference to the first value in the entry.
    ///
    /// Values are stored in insertion order.
    ///
    /// # Panics
    ///
    /// `get` panics if there are no values associated with the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     assert_eq!(e.get(), &"hello.world");
    ///
    ///     e.append("hello.earth".parse().unwrap());
    ///
    ///     assert_eq!(e.get(), &"hello.world");
    /// }
    /// ```
    pub fn get(&self) -> &T {
        self.inner.get().get(self.index).unwrap()
    }

    /// Get a mutable reference to the first value in the entry.
    ///
    /// Values are stored in insertion order.
    ///
    /// # Panics
    ///
    /// `get_mut` panics if there are no values associated with the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::default();
    /// map.insert(HOST, "hello.world".to_string());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     e.get_mut().push_str("-2");
    ///     assert_eq!(e.get(), &"hello.world-2");
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut().get_mut(self.index).unwrap()
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the **first**
    /// value.
    ///
    /// The lifetime of the returned reference is bound to the original map.
    ///
    /// # Panics
    ///
    /// `into_mut` panics if there are no values associated with the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::default();
    /// map.insert(HOST, "hello.world".to_string());
    /// map.append(HOST, "hello.earth".to_string());
    ///
    /// if let Entry::Occupied(e) = map.entry("host") {
    ///     e.into_mut().push_str("-2");
    /// }
    ///
    /// assert_eq!("hello.world-2", map["host"]);
    /// ```
    pub fn into_mut(self) -> &'a mut T {
        self.inner.into_mut().get_mut(self.index).unwrap()
    }

    /// Sets the value of the entry.
    ///
    /// All previous values associated with the entry are removed and the first
    /// one is returned. See `insert_mult` for an API that returns all values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "hello.world".parse().unwrap());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     let mut prev = e.insert("earth".parse().unwrap());
    ///     assert_eq!("hello.world", prev);
    /// }
    ///
    /// assert_eq!("earth", map["host"]);
    /// ```
    pub fn insert(&mut self, value: T) -> T {
        self.inner.insert(smallvec![value]).into_iter().next().unwrap()
    }

    /// Sets the value of the entry.
    ///
    /// This function does the same as `insert` except it returns an iterator
    /// that yields all values previously associated with the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    /// map.append(HOST, "world2".parse().unwrap());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     let mut prev = e.insert_mult("earth".parse().unwrap());
    ///     assert_eq!("world", prev.next().unwrap());
    ///     assert_eq!("world2", prev.next().unwrap());
    ///     assert!(prev.next().is_none());
    /// }
    ///
    /// assert_eq!("earth", map["host"]);
    /// ```
    pub fn insert_mult(&mut self, value: T) -> ValueDrain<'_, T> {
        ValueDrain { inner: self.inner.insert(smallvec![value]).into_iter(), _marker: PhantomData }
    }

    /// Insert the value into the entry.
    ///
    /// The new value is appended to the end of the entry's value list. All
    /// previous values associated with the entry are retained.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     e.append("earth".parse().unwrap());
    /// }
    ///
    /// let values = map.get_all("host");
    /// let mut i = values.iter();
    /// assert_eq!("world", *i.next().unwrap());
    /// assert_eq!("earth", *i.next().unwrap());
    /// ```
    pub fn append(&mut self, value: T) {
        self.inner.get_mut().push(value);
    }

    /// Remove the entry from the map.
    ///
    /// All values associated with the entry are removed and the first one is
    /// returned. See `remove_entry_mult` for an API that returns all values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    ///
    /// if let Entry::Occupied(e) = map.entry("host") {
    ///     let mut prev = e.remove();
    ///     assert_eq!("world", prev);
    /// }
    ///
    /// assert!(!map.contains_key("host"));
    /// ```
    pub fn remove(self) -> T {
        let (_, values) = self.inner.remove_entry();
        values.into_iter().next().unwrap()
    }

    /// Remove the entry from the map.
    ///
    /// The key and all values associated with the entry are removed and the
    /// first one is returned. See `remove_entry_mult` for an API that returns
    /// all values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    ///
    /// if let Entry::Occupied(e) = map.entry("host") {
    ///     let (key, mut prev) = e.remove_entry();
    ///     assert_eq!("host", key.as_str());
    ///     assert_eq!("world", prev);
    /// }
    ///
    /// assert!(!map.contains_key("host"));
    /// ```
    pub fn remove_entry(self) -> (HeaderName, T) {
        let (key, values) = self.inner.remove_entry();
        (key, values.into_iter().next().unwrap())
    }

    // /// Remove the entry from the map.
    // ///
    // /// The key and all values associated with the entry are removed and
    // /// returned.
    // pub fn remove_entry_mult(self) -> (HeaderName, ValueDrain<'a, T>) {
    //     let entry = self.map.remove_found(self.probe, self.index);
    //     let raw_links = self.map.raw_links();
    //     let extra_values = &mut self.map.extra_values as *mut _;
    //     let drain = ValueDrain {
    //         raw_links,
    //         extra_values,
    //         first: Some(entry.value),
    //         next: entry.links.map(|l| l.next),
    //         lt: PhantomData,
    //     };
    //     (entry.key, drain)
    // }

    /// Returns an iterator visiting all values associated with the entry.
    ///
    /// Values are iterated in insertion order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::new();
    /// map.insert(HOST, "world".parse().unwrap());
    /// map.append(HOST, "earth".parse().unwrap());
    ///
    /// if let Entry::Occupied(e) = map.entry("host") {
    ///     let mut iter = e.iter();
    ///     assert_eq!(&"world", iter.next().unwrap());
    ///     assert_eq!(&"earth", iter.next().unwrap());
    ///     assert!(iter.next().is_none());
    /// }
    /// ```
    pub fn iter(&self) -> ValueIter<'_, T> {
        self.into_iter()
    }

    /// Returns an iterator mutably visiting all values associated with the
    /// entry.
    ///
    /// Values are iterated in insertion order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use http::header::{HeaderMap, Entry, HOST};
    /// let mut map = HeaderMap::default();
    /// map.insert(HOST, "world".to_string());
    /// map.append(HOST, "earth".to_string());
    ///
    /// if let Entry::Occupied(mut e) = map.entry("host") {
    ///     for e in e.iter_mut() {
    ///         e.push_str("-boop");
    ///     }
    /// }
    ///
    /// let mut values = map.get_all("host");
    /// let mut i = values.iter();
    /// assert_eq!(&"world-boop", i.next().unwrap());
    /// assert_eq!(&"earth-boop", i.next().unwrap());
    /// ```
    pub fn iter_mut(&mut self) -> ValueIterMut<'_, T> {
        ValueIterMut { inner: self.inner.get_mut().iter_mut() }
    }
}

impl<'a, T> IntoIterator for OccupiedEntry<'a, T> {
    type Item = &'a mut T;
    type IntoIter = ValueIterMut<'a, T>;

    fn into_iter(self) -> ValueIterMut<'a, T> {
        ValueIterMut { inner: self.inner.into_mut().iter_mut() }
    }
}

impl<'a, 'b: 'a, T> IntoIterator for &'b OccupiedEntry<'a, T> {
    type Item = &'a T;
    type IntoIter = ValueIter<'a, T>;

    fn into_iter(self) -> ValueIter<'a, T> {
        ValueIter { inner: self.inner.get().iter() }
    }
}

impl<'a, 'b: 'a, T> IntoIterator for &'b mut OccupiedEntry<'a, T> {
    type Item = &'a mut T;
    type IntoIter = ValueIterMut<'a, T>;

    fn into_iter(self) -> ValueIterMut<'a, T> {
        self.iter_mut()
    }
}

// ===== impl ValueDrain =====

impl<'a, T> Iterator for ValueDrain<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> FusedIterator for ValueDrain<'a, T> {}

/*
 *
 * ===== impl IntoHeaderName / AsHeaderName =====
 *
 */

mod into_header_name {
    use super::HeaderName;

    /// A marker trait used to identify values that can be used as insert keys
    /// to a `HeaderMap`.
    pub trait IntoHeaderName: Sealed {}

    // All methods are on this pub(super) trait, instead of `IntoHeaderName`,
    // so that they aren't publicly exposed to the world.
    //
    // Being on the `IntoHeaderName` trait would mean users could call
    // `"host".insert(&mut map, "localhost")`.
    //
    // Ultimately, this allows us to adjust the signatures of these methods
    // without breaking any external crate.
    pub trait Sealed {
        #[doc(hidden)]
        fn into_header_name(self) -> HeaderName;
    }

    // ==== impls ====

    impl Sealed for HeaderName {
        #[doc(hidden)]
        #[inline]
        fn into_header_name(self) -> HeaderName {
            self
        }
    }

    impl IntoHeaderName for HeaderName {}

    impl<'a> Sealed for &'a HeaderName {
        #[doc(hidden)]
        #[inline]
        fn into_header_name(self) -> HeaderName {
            self.clone()
        }
    }

    impl<'a> IntoHeaderName for &'a HeaderName {}

    impl Sealed for &'static str {
        #[doc(hidden)]
        #[inline]
        fn into_header_name(self) -> HeaderName {
            HeaderName::from_bytes(self.as_bytes()).unwrap()
        }
    }

    impl IntoHeaderName for &'static str {}
}

mod as_header_name {
    use super::{HeaderName, InvalidHeaderName};

    /// A marker trait used to identify values that can be used as search keys
    /// to a `HeaderMap`.
    pub trait AsHeaderName: Sealed {}

    // All methods are on this pub(super) trait, instead of `AsHeaderName`,
    // so that they aren't publicly exposed to the world.
    //
    // Being on the `AsHeaderName` trait would mean users could call
    // `"host".find(&map)`.
    //
    // Ultimately, this allows us to adjust the signatures of these methods
    // without breaking any external crate.
    pub trait Sealed {
        #[doc(hidden)]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName>;

        #[doc(hidden)]
        fn as_str(&self) -> &str;
    }

    // ==== impls ====

    impl Sealed for HeaderName {
        #[doc(hidden)]
        #[inline]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName> {
            Ok(f(self))
        }

        #[doc(hidden)]
        fn as_str(&self) -> &str {
            <HeaderName>::as_str(self)
        }
    }

    impl AsHeaderName for HeaderName {}

    impl<'a> Sealed for &'a HeaderName {
        #[doc(hidden)]
        #[inline]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName> {
            Ok(f(*self))
        }

        #[doc(hidden)]
        fn as_str(&self) -> &str {
            <HeaderName>::as_str(*self)
        }
    }

    impl<'a> AsHeaderName for &'a HeaderName {}

    impl<'a> Sealed for &'a str {
        #[doc(hidden)]
        #[inline]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName> {
            HeaderName::from_bytes(self.as_bytes()).map(move |hdr| f(&hdr))
        }

        #[doc(hidden)]
        fn as_str(&self) -> &str {
            self
        }
    }

    impl<'a> AsHeaderName for &'a str {}

    impl Sealed for String {
        #[doc(hidden)]
        #[inline]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName> {
            self.as_str().with_header_name(f)
        }

        #[doc(hidden)]
        fn as_str(&self) -> &str {
            self
        }
    }

    impl AsHeaderName for String {}

    impl<'a> Sealed for &'a String {
        #[doc(hidden)]
        #[inline]
        fn with_header_name<T>(&self, f: impl FnOnce(&HeaderName) -> T) -> Result<T, InvalidHeaderName> {
            self.as_str().with_header_name(f)
        }

        #[doc(hidden)]
        fn as_str(&self) -> &str {
            *self
        }
    }

    impl<'a> AsHeaderName for &'a String {}
}

#[test]
fn test_bounds() {
    fn check_bounds<T: Send + Send>() {}

    check_bounds::<HeaderMap<()>>();
    check_bounds::<Iter<'static, ()>>();
    check_bounds::<IterMut<'static, ()>>();
    check_bounds::<Keys<'static, ()>>();
    check_bounds::<Values<'static, ()>>();
    check_bounds::<ValuesMut<'static, ()>>();
    check_bounds::<Drain<'static, ()>>();
    check_bounds::<GetAll<'static, ()>>();
    check_bounds::<Entry<'static, ()>>();
    check_bounds::<VacantEntry<'static, ()>>();
    check_bounds::<OccupiedEntry<'static, ()>>();
    check_bounds::<ValueIter<'static, ()>>();
    check_bounds::<ValueIterMut<'static, ()>>();
    check_bounds::<ValueDrain<'static, ()>>();
}

#[test]
fn skip_duplicates_during_key_iteration() {
    let mut map = HeaderMap::new();
    map.append("a", HeaderValue::from_static("a"));
    map.append("a", HeaderValue::from_static("b"));
    assert_eq!(map.keys().count(), map.keys_len());
}
