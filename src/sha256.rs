use anyhow::{self, Error, Result};
use sha2::compress256;
use sha2::digest::generic_array::GenericArray;

pub const DEFAULT_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// The internal state representation of a sha256 state.
#[derive(Clone)]
pub struct State {
    inner: [u32; 8],
}

impl State {
    pub fn new() -> Self {
        State {
            inner: DEFAULT_STATE,
        }
    }

    pub fn inner(&self) -> [u32; 8] {
        self.inner
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl From<&State> for [u8; 32] {
    fn from(val: &State) -> Self {
        let mut state = val.inner;
        for h in state.iter_mut() {
            *h = h.to_be();
        }
        unsafe { *(state.as_ptr() as *const [u8; 32]) }
    }
}

impl From<State> for [u8; 32] {
    fn from(val: State) -> Self {
        let mut state = val.inner;
        for h in state.iter_mut() {
            *h = h.to_be();
        }
        unsafe { *(state.as_ptr() as *const [u8; 32]) }
    }
}

impl From<[u8; 32]> for State {
    fn from(data: [u8; 32]) -> Self {
        let mut inner = [0u32; 8];

        // Split in chunks of [u8; 4] and create the state slice containing u32
        // values.
        data.chunks(4).enumerate().for_each(|(i, c)| {
            inner[i] = u32::from_be_bytes(unsafe { *(c.as_ptr() as *const [u8; 4]) })
        });
        State { inner }
    }
}

impl TryFrom<&[u8]> for State {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let data: [u8; 32] = value.try_into()?;
        Ok(State::from(data))
    }
}

impl From<State> for Vec<u8> {
    fn from(val: State) -> Self {
        let data: [u8; 32] = val.into();
        data.to_vec()
    }
}

impl From<&State> for String {
    fn from(val: &State) -> Self {
        let state: [u8; 32] = val.into();
        hex::encode(state)
    }
}

impl ToString for State {
    fn to_string(&self) -> String {
        let state: [u8; 32] = self.into();
        hex::encode(state)
    }
}

impl std::cmp::PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl std::cmp::Eq for State {}

#[derive(Clone)]
pub struct Compressor {
    state: State,
    len: u64,
}

impl Compressor {
    pub fn new() -> Self {
        Self::from_state(DEFAULT_STATE, 0)
    }

    pub fn from_state(state: [u32; 8], len: u64) -> Self {
        Compressor {
            state: State { inner: state },
            len,
        }
    }

    pub fn from_bytes(data: [u8; 32], len: u64) -> Self {
        Compressor {
            state: State::from(data),
            len,
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        self.len += data.len() as u64;
        data.chunks(64)
            .for_each(|c| compress256(&mut self.state.inner, &[GenericArray::clone_from_slice(c)]));
    }

    /// Returns the state of this [`Compressor`].
    pub fn state(&self) -> State {
        self.state.clone()
    }

    /// Returns the size of this [`Compressor`].
    pub fn size(&self) -> usize {
        self.len as usize
    }
}

impl Default for Compressor {
    fn default() -> Self {
        Self::new()
    }
}

impl std::cmp::PartialEq for Compressor {
    fn eq(&self, other: &Self) -> bool {
        self.state.eq(&other.state) && self.len == other.len
    }
}

impl std::cmp::Eq for Compressor {}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_sha256() {
        // Check that state conversion into [u8; 32] and from [u8; 32] works as
        // expected;
        let data: [u8; 32] = State::default().into();
        assert_eq!(
            data,
            [
                106, 9, 230, 103, 187, 103, 174, 133, 60, 110, 243, 114, 165, 79, 245, 58, 81, 14,
                82, 127, 155, 5, 104, 140, 31, 131, 217, 171, 91, 224, 205, 25
            ]
        );

        let state_bytes = TryInto::try_into(data).unwrap();
        let compressor = Compressor::from_bytes(state_bytes, 0);
        assert_eq!(compressor.state().inner(), DEFAULT_STATE);
    }
}
