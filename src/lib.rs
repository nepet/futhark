use std::{collections::HashMap, io::Read, str::FromStr};

use anyhow::{self, Result};
use base64::Engine;
use thiserror::Error;

mod sha256;

#[derive(Error, Debug, PartialEq)]
pub enum RuneError {
    #[error("unknown: `{0}`")]
    Unknown(String),
    #[error("invalid condition: {0}")]
    InvalidCondition(String),
    #[error("invalid field: {0}")]
    InvalidField(String),
    #[error("{0}")]
    ValueError(String),
    #[error("{0} does not contain any operator")]
    NoOperator(String),
    #[error("unauthorized")]
    Unauthorized,
    #[error("fewer restrictions than master")]
    LessRestrictions,
    #[error("does not match master rune")]
    DoesNotMatch,
}

/// Conditions are the heart of a [`Rune`]. They are to be met and build
/// [`Alternatives`] and [`Restrictions`].
#[derive(Debug, PartialEq, Clone)]
pub enum Condition {
    /// Pass if field is missing (value ignored)
    Missing,
    /// Pass if exists and exactly equals
    Equal,
    /// Pass if exists and is not exactly equal
    NotEqual,
    /// Pass if exists and begins with
    BeginsWith,
    /// Pass if exists and ends with
    EndsWith,
    /// Pass if exists and contains
    Contains,
    /// Pass if exists, is a valid integer (may be signed), and numerically less than
    IntLT,
    /// Pass if exists, is a valid integer (may be signed), and numerically greater than
    IntGT,
    /// Pass if exists and lexicographically less than (or shorter)
    LexLT,
    /// Pass if exists and lexicographically greater than (or longer)
    LexGT,
    /// Always pass: no condition, this is a comment
    Comment,
}

impl Condition {
    fn symbol(&self) -> &str {
        match self {
            Condition::Missing => "!",
            Condition::Equal => "=",
            Condition::NotEqual => "/",
            Condition::BeginsWith => "^",
            Condition::EndsWith => "$",
            Condition::Contains => "~",
            Condition::IntLT => "<",
            Condition::IntGT => ">",
            Condition::LexLT => "{",
            Condition::LexGT => "}",
            Condition::Comment => "#",
        }
    }
}

impl TryFrom<char> for Condition {
    type Error = RuneError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        let cond = match value {
            '!' => Condition::Missing,
            '=' => Condition::Equal,
            '/' => Condition::NotEqual,
            '^' => Condition::BeginsWith,
            '$' => Condition::EndsWith,
            '~' => Condition::Contains,
            '<' => Condition::IntLT,
            '>' => Condition::IntGT,
            '{' => Condition::LexLT,
            '}' => Condition::LexGT,
            '#' => Condition::Comment,
            _ => return Err(RuneError::InvalidCondition(value.to_string())),
        };

        Ok(cond)
    }
}

impl TryFrom<&str> for Condition {
    type Error = RuneError;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        if value.len() > 1 {
            return Err(RuneError::InvalidCondition(
                "condition from multiple chars".to_string(),
            ));
        }

        match value.chars().next() {
            Some(c) => c.try_into(),
            None => Err(RuneError::InvalidCondition(
                "condition from empty &str".to_string(),
            )),
        }
    }
}

impl std::fmt::Display for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = self.symbol();
        write!(f, "{}", symbol)
    }
}

fn why(cond: bool, field: &str, xpl: String) -> Result<(), RuneError> {
    if !cond {
        return Err(RuneError::ValueError(format!("{}: {}", field, xpl)));
    }
    Ok(())
}

/// A trait that defines how an alternative is tested.
pub trait Tester {
    /// Returns `None` if the test is met and a reason `String` if the
    /// test conditions are not met.
    ///
    /// # Arguments
    ///
    /// * `alt` - The alternative to check against the `Tester`.
    fn test(&self, alt: &Alternative) -> Result<(), RuneError>;
}

/// A `Tester` trait implementation that checks for matching conditions. The
/// `ConditionTester` compares the String `value` against the condition of the
/// `Alternative`.
pub struct ConditionTester {
    pub value: String,
}

impl Tester for ConditionTester {
    fn test(&self, alt: &Alternative) -> Result<(), RuneError> {
        match alt.cond {
            Condition::Missing => why(false, &alt.field, "is present".to_string()),
            Condition::Equal => why(
                self.value == alt.value,
                &alt.field,
                format!("!= {}", alt.value),
            ),
            Condition::NotEqual => why(
                self.value != alt.value,
                &alt.field,
                format!("= {}", alt.value),
            ),
            Condition::BeginsWith => why(
                self.value.starts_with(&alt.value),
                &alt.field,
                format!("does not start with {}", alt.value),
            ),
            Condition::EndsWith => why(
                self.value.ends_with(&alt.value),
                &alt.field,
                format!("does not end with {}", alt.value),
            ),
            Condition::Contains => why(
                self.value.contains(&alt.value),
                &alt.field,
                format!("does not contain {}", alt.value),
            ),
            Condition::IntLT => {
                let actual_int = match self.value.parse::<i64>() {
                    Ok(n) => n,
                    Err(_) => return why(false, &alt.field, "not an integer field".to_string()),
                };

                let restriction_int = match alt.value.parse::<i64>() {
                    Ok(n) => n,
                    Err(_) => return why(false, &alt.field, "not a valid integer".to_string()),
                };

                return why(
                    actual_int < restriction_int,
                    &alt.field,
                    format!(">= {}", restriction_int),
                );
            }
            Condition::IntGT => {
                let actual_int = match self.value.parse::<i64>() {
                    Ok(n) => n,
                    Err(_) => return why(false, &alt.field, "not an integer field".to_string()),
                };

                let restriction_int = match alt.value.parse::<i64>() {
                    Ok(n) => n,
                    Err(_) => return why(false, &alt.field, "not a valid integer".to_string()),
                };

                return why(
                    actual_int > restriction_int,
                    &alt.field,
                    format!("<= {}", restriction_int),
                );
            }
            Condition::LexLT => why(
                self.value.cmp(&alt.value).is_lt(),
                &alt.field,
                format!("is the same or ordered after {}", alt.value),
            ),
            Condition::LexGT => why(
                self.value.cmp(&alt.value).is_gt(),
                &alt.field,
                format!("is the same or ordered before {}", alt.value),
            ),
            Condition::Comment => Ok(()),
        }
    }
}

/// An [`Alternative`] is the smallest component of a rune. It consists of a single
/// combination of a field name, a condition and a value that can be checked.
///
/// # Example
/// An alternative that requires the field with the name `f1` to be missing.
/// ```
/// use futhark::{Alternative, Condition};
/// use std::collections::HashMap;
///
/// let alt = Alternative::new("f1".to_string(), Condition::Missing, "".to_string(), false).unwrap();
/// assert!(alt.test(&HashMap::new()).is_ok());
/// ```
#[derive(Debug, Clone)]
pub struct Alternative {
    field: String,
    cond: Condition,
    value: String,
}

impl Alternative {
    /// Returns an Alternative for a field with condition and value.
    ///
    /// # Arguments
    ///
    /// * `field` - A String that represents the name of the field
    /// * `cond` - The [`Condition`] that is checked on
    /// * `value` - A String that is to be met with the [`Condition`]
    /// * `allow_idfield` - If set, the [`Alternative`] allows for an empty field name
    ///
    /// # Errors
    ///
    /// This function will return a [`RuneError::InvalidField`] if the field name contains
    /// [`PUNCTUATION`] or if the field is empty without allowing idfield.
    /// It returns a [`RuneError::InvalidCondition`] if field is an idfield but
    /// the condition is not [`Condition::Equal`].
    pub fn new(
        field: String,
        cond: Condition,
        value: String,
        allow_idfield: bool,
    ) -> Result<Self, RuneError> {
        if contains_punctuation(&field) {
            // A field must not contain any punctuation (C's ispunct()).
            return Err(RuneError::InvalidField(format!(
                "{}: has punctuation",
                field
            )));
        }
        if field.is_empty() {
            // An empty field indicates an unique_id field that is only allowed if
            // allow_idfield is set and the '' field has `Condition::Equal`.
            if !allow_idfield {
                return Err(RuneError::InvalidField(
                    "unique_id field not valid".to_string(),
                ));
            }
            if cond != Condition::Equal {
                return Err(RuneError::InvalidCondition(format!(
                    "'{}': unique_id condition must be '='",
                    cond
                )));
            }
        }
        Ok(Alternative { field, cond, value })
    }

    /// Returns the field name of the `Alternative`.
    pub fn get_field(&self) -> String {
        self.field.clone()
    }

    /// Returns the condition of the `Alternative`.
    pub fn get_condition(&self) -> Condition {
        self.cond.clone()
    }

    /// Returns the value of the `Alternative`.
    pub fn get_value(&self) -> String {
        self.value.clone()
    }

    fn is_unique_id(&self) -> bool {
        self.field.is_empty()
    }

    /// Test the alternative against a set of values. Returns `None` if the test
    /// succeeds and a `String` with an explanation why the test failed
    /// otherwise.
    ///
    /// # Arguments
    ///
    /// * `values` A map of type `<String, Tester>` that represent the field names and the tests that have to be performed on the field.
    pub fn test(&self, values: &HashMap<String, Box<dyn Tester>>) -> Result<(), RuneError> {
        // Wrapper to return an explanation if the condition is not met.

        // Check if condition is a comment, this is always true. We can skip any
        // further checks.
        if self.cond == Condition::Comment {
            return Ok(());
        }

        // The field is missing.
        if !values.contains_key(&self.field) {
            // Default to ignoring id field as long as no version is set. A
            // version is separated by a `-`, e.g `-[version]`.
            if self.is_unique_id() {
                return why(
                    !self.value.contains('-'),
                    &self.field,
                    format!("unknown version {}", self.value),
                );
            }
            // This can only be true if the condition for this test is
            // `Condition::Missing`.
            return why(
                self.cond == Condition::Missing,
                &self.field,
                "is missing".to_string(),
            );
        }

        let tester = values.get(&self.field).unwrap();
        tester.test(self)
    }

    /// Returns an encoded String of the alternative. A string will be encoded
    /// in `[field][condition][value]`
    pub fn encode(&self) -> String {
        format!(
            "{}{}{}",
            self.field,
            self.cond,
            self.value
                .replace('\\', "\\\\")
                .replace('|', "\\|")
                .replace('&', "\\&")
        )
    }

    /// Tries to read the first alternative from the buffer and to decode this
    /// alternative into an [`Alternative`].
    /// Returns a tuple `([Alternative], &str)`.
    ///
    /// # Arguments
    ///
    /// * `data` A reference to a str containing the alternative.
    /// * `allow_idfield` If set an empty field for a unique id is allowed.
    ///
    pub fn decode(data: &str, allow_idfield: bool) -> Result<(Self, &str), RuneError> {
        let mut field = String::new();
        let mut cond: Option<Condition> = None;
        let mut value = String::new();

        let mut chars = data.chars();
        // Extract field name and condition.
        for c in chars.by_ref() {
            if is_separator(c) {
                cond = c.try_into().ok();
                break;
            }
            field.push(c);
        }

        if cond.is_none() {
            return Err(RuneError::NoOperator(field));
        }

        // Extract value.
        let mut extra_chars = 0;
        while let Some(c) = chars.next() {
            match c {
                '|' => break,
                '&' => {
                    extra_chars += 1;
                    break;
                }
                '\\' => {
                    // Escape char: skip a beat.
                    if let Some(c) = chars.next() {
                        value.push(c);
                    } else {
                        break;
                    }
                }
                _ => value.push(c),
            }
        }

        let alt = Alternative::new(field, cond.unwrap(), value, allow_idfield)?;
        let rest = &data[(data.len() - (chars.count() + extra_chars))..];
        Ok((alt, rest))
    }
}

impl std::fmt::Display for Alternative {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.encode())
    }
}

impl std::cmp::PartialEq for Alternative {
    fn eq(&self, other: &Self) -> bool {
        self.field == other.field && self.cond == other.cond && self.value == other.value
    }
}

impl std::cmp::Eq for Alternative {}

#[derive(Debug, Clone)]
pub struct Restriction {
    pub alternatives: Vec<Alternative>,
}

impl Restriction {
    /// Constructor for a new restriction.
    pub fn new(alternatives: Vec<Alternative>) -> Result<Self, RuneError> {
        // An empty restriction would be pretty useless.
        if alternatives.is_empty() {
            return Err(RuneError::Unknown(
                "restriction must have some alternatives".to_string(),
            ));
        }

        // Unique ids have to be a sole alternative.
        if alternatives.len() > 1 && alternatives[0].is_unique_id() {
            return Err(RuneError::Unknown(
                "unique_id field cannot have alternatives".to_string(),
            ));
        }

        Ok(Restriction { alternatives })
    }

    pub fn unique_id(unique_id: String, version: Option<String>) -> Result<Self, RuneError> {
        if unique_id.contains('-') {
            return Err(RuneError::ValueError(
                "hyphen not allowed in id".to_string(),
            ));
        }

        let mut id_str = unique_id;

        if let Some(v) = version {
            id_str = format!("{}-{}", id_str, v);
        }

        let alt = Alternative::new("".to_string(), Condition::Equal, id_str, true)?;
        Ok(Restriction {
            alternatives: vec![alt],
        })
    }

    /// Test a set of values against a restriction. Returns `None` on success
    /// and a `String` with all explanations otherwise.
    pub fn test(&self, values: &HashMap<String, Box<dyn Tester>>) -> Result<(), RuneError> {
        // Iterate and test all alternatives and collect results.
        let (oks, errs): (Vec<_>, Vec<_>) = self
            .alternatives
            .clone()
            .into_iter()
            .map(|alt| alt.test(values))
            .partition(Result::is_ok);
        if !oks.is_empty() {
            // We got AT LEAST ONE OK so at least one `Alternative` was
            // successfully checked to be valid.
            return Ok(());
        }
        // We got no OK so NO `Alternative` fulfilled the requirements. We
        // collect the reasons from the errors and return them in a single Err.
        let msg = errs
            .into_iter()
            .map(|e| e.unwrap_err().to_string())
            .collect::<Vec<String>>()
            .join(" AND ");
        Err(RuneError::ValueError(msg))
    }

    pub fn encode(&self) -> String {
        self.alternatives
            .iter()
            .map(|alt| alt.encode())
            .collect::<Vec<String>>()
            .join("|")
    }

    pub fn decode(data: &str, allow_idfield: bool) -> Result<(Self, &str), RuneError> {
        let mut local_data = data;
        let mut alts = vec![];

        while !local_data.is_empty() {
            if local_data.as_bytes()[0] as char == '&' {
                // Found new restriction strip and break;
                local_data = &local_data[1..];
                break;
            }
            let (alt, rest) = Alternative::decode(local_data, allow_idfield)?;
            alts.push(alt);
            local_data = rest;
        }

        let res = Restriction::new(alts)?;
        Ok((res, local_data))
    }
}

impl std::cmp::PartialEq for Restriction {
    fn eq(&self, other: &Self) -> bool {
        if self.alternatives.len() != other.alternatives.len() {
            return false;
        }

        if self
            .alternatives
            .iter()
            .zip(other.alternatives.iter())
            .any(|(mr, or)| mr.ne(or))
        {
            return false;
        };

        return true;
    }
}

impl std::cmp::Eq for Restriction {}

#[derive(Clone)]
pub struct Rune {
    restrictions: Vec<Restriction>,
    compressor: sha256::Compressor,
    authcode: [u8; 32],
}

impl Rune {
    /// Creates a [`Rune`] from an `auth_base` that is used as the base sha
    /// state with the given `restrictions`.
    ///
    /// # Arguments
    ///
    /// * `authcode` A sha256 base state that this rune is derived from.
    /// * `restrictions` A set of restrictions that this rune requires.
    pub fn new(authcode: [u8; 32], restrictions: Vec<Restriction>) -> Self {
        // An auth_base is always len 64 as it is the secret from which we derive
        // the rune.
        let compressor = sha256::Compressor::from_bytes(authcode, 64);

        let mut rune = Self {
            restrictions: vec![],
            compressor,
            authcode,
        };

        // Append other restrictions
        for r in restrictions {
            rune.add_restriction(r)
        }

        rune
    }

    /// What the server calls to create a [`Rune`] that is derived from a
    /// secret seed. One should also use set a unique id typically derived from
    /// a server side counter. This allows to revoke a rune without changing the
    /// secret seed. A version might also be set to ensure future compatibility.
    ///
    /// # Arguments
    ///
    /// * `seedsecret` The secret that the rune is derived from. This is usually
    /// * `restrictions` A set of restrictions that this rune requires.
    /// * `unique_id` An optional unique id, usually derived by a counter on the server.
    /// * `version` An optional version.
    ///
    /// # Errors
    ///
    /// * `RuneError::ValueError` If the `seedsecret` is larger than one sha block.
    /// * `RuneError::ValueError` If the `seedsecret` can not be converted to a sha state.
    pub fn new_master_rune(
        seedsecret: &[u8],
        restrictions: Vec<Restriction>,
        unique_id: Option<String>,
        version: Option<String>,
    ) -> Result<Self, RuneError> {
        if seedsecret.len() + 1 + 8 > 64 {
            return Err(RuneError::ValueError(
                "seedsecret is expected to be less than 55 byte".to_string(),
            ));
        }

        // generate authcode
        let mut compressor = sha256::Compressor::default();
        let mut base = seedsecret.to_vec();
        add_padding(seedsecret.len(), &mut base);
        compressor.update(&base);

        let mut restrictions = restrictions;

        // Add unique id if it is set. It has to be the first element;
        if let Some(id) = unique_id {
            let uid = Restriction::unique_id(id, version)?;
            restrictions.reverse();
            restrictions.push(uid);
            restrictions.reverse();
        }

        Ok(Self::new(compressor.state().into(), restrictions))
    }

    /// Returns a [`Rune`] that uses the `authcode` as a base state for the sha
    /// to derive from.
    ///
    /// # Arguments
    ///
    /// * `authcode` An array representing a base state for the sha compressor.
    /// * `restrictions` An vector containing the runes [`Restriction`]s.
    pub fn from_authcode(authcode: [u8; 32], restrictions: Vec<Restriction>) -> Self {
        // Receive the sha state from the authcode;
        let state = sha256::State::from(authcode);

        // Calculate the total sha state size.
        let mut len = 64;
        for r in restrictions.clone() {
            len += r.encode().len();
            len += pad_len(len);
        }

        // Hydrate the compressor with the state and the total size.
        let compressor = sha256::Compressor::from_state(state.inner(), len as u64);
        Self {
            restrictions,
            compressor,
            authcode,
        }
    }

    /// Returns the current authcode of the rune, which is the SHA256 state.
    pub fn authcode(&self) -> [u8; 32] {
        self.compressor.state().into()
    }

    /// Creates a [`Rune`] from a base64 url encoded string. The base64 string
    /// can be created by exporting a rune with the `to_base64` command.
    ///
    /// # Arguments
    /// * `s` The rune base64 url safe encoded.
    ///
    /// # Errors
    /// * `RuneError::Unknown` If the decoding fails.
    /// * `RuneError::ValueError` If the rune size is shorter that the expected authcode lenght.
    pub fn from_base64(s: &str) -> Result<Self, RuneError> {
        let engine = base64::engine::general_purpose::GeneralPurpose::new(
            &base64::alphabet::URL_SAFE,
            base64::engine::general_purpose::PAD,
        );
        let rune_byte = engine
            .decode(s)
            .map_err(|e| RuneError::Unknown(format!("{}", e)))?;
        if rune_byte.len() < 32 {
            return Err(RuneError::ValueError(
                "expected decoded len to be contain 32byte authcode".to_string(),
            ));
        }
        let auth_str = hex::encode(&rune_byte[..32]);
        let rest_str = String::from_utf8(rune_byte[32..].to_vec())
            .map_err(|e| RuneError::Unknown(format!("{}", e)))?;
        Self::from_str(&format!("{}:{}", auth_str, rest_str))
    }

    pub fn add_restriction(&mut self, res: Restriction) {
        self.restrictions.push(res.clone());
        let mut data = res.encode().as_bytes().to_vec();
        add_padding(self.compressor.size() + data.len(), &mut data);
        self.compressor.update(&data);
    }

    /// Returns None if met, Reason otherwise.
    pub fn are_restrictions_met(
        &self,
        values: &HashMap<String, Box<dyn Tester>>,
    ) -> Result<(), RuneError> {
        self.restrictions
            .iter()
            .try_for_each(|res| res.test(values))
    }

    pub fn is_authorized(&self, other: Rune) -> bool {
        let mut compressor = sha256::Compressor::from_bytes(self.authcode, 64);
        for r in other.restrictions {
            let mut data = r.encode().as_bytes().to_vec();
            add_padding(compressor.size() + data.len(), &mut data);
            compressor.update(&data);
        }
        compressor.state().inner() == other.compressor.state().inner()
    }

    pub fn check_with_reason(
        &self,
        b64str: &str,
        values: &HashMap<String, Box<dyn Tester>>,
    ) -> Result<(), RuneError> {
        let rune = Rune::from_base64(b64str)?;
        if !self.is_authorized(rune) {
            return Err(RuneError::Unauthorized);
        }
        self.are_restrictions_met(values)
    }

    pub fn to_base64(&self) -> String {
        let rest_str = self
            .restrictions
            .iter()
            .map(|r| r.encode())
            .collect::<Vec<String>>()
            .join("&");
        let mut data: Vec<u8> = self.compressor.state().into();
        data.append(&mut rest_str.as_bytes().to_vec());
        let engine = base64::engine::general_purpose::GeneralPurpose::new(
            &base64::alphabet::URL_SAFE,
            base64::engine::general_purpose::PAD,
        );
        engine.encode(data)
    }
}

impl ToString for Rune {
    fn to_string(&self) -> String {
        let rest_str = self
            .restrictions
            .iter()
            .map(|r| r.encode())
            .collect::<Vec<String>>()
            .join("&");
        format!("{}:{}", self.compressor.state().to_string(), rest_str)
    }
}

impl FromStr for Rune {
    type Err = RuneError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() < 64 || s.as_bytes()[64] as char != ':' {
            return Err(RuneError::ValueError(
                "rune strings must start with 64 hex digits followed by ':'".to_string(),
            ));
        }

        let auth_str = hex::decode(&s[..64]).map_err(|e| RuneError::Unknown(format!("{}", e)))?;
        let mut res_str = &s[65..];

        let mut restrictions = vec![];
        while !res_str.is_empty() {
            let allow_idfield = restrictions.is_empty();
            let (restriction, rest_str) = Restriction::decode(res_str, allow_idfield)?;
            restrictions.push(restriction);
            res_str = rest_str;
        }

        let authcode: [u8; 32] = auth_str
            .try_into()
            .map_err(|e| RuneError::Unknown(format!("can not convert to authcode: {:?}", e)))?;
        Ok(Self::from_authcode(authcode, restrictions))
    }
}

const PUNCTUATION: [char; 31] = [
    '!', '"', '#', '$', '%', '&', '\'', '(', ')', '*', '+', ',', '-', '.', '/', ':', ';', '?', '<',
    '=', '>', '@', '[', '\\', ']', '^', '`', '{', '|', '}', '~',
];

fn is_separator(c: char) -> bool {
    PUNCTUATION.contains(&c)
}

fn contains_punctuation(s: &str) -> bool {
    for c in PUNCTUATION {
        if s.contains(c) {
            return true;
        }
    }
    false
}

/// Sha block size in byte. For sha256 this is 64 byte;
const BLOCK_SIZE: usize = 64;

/// Calculate how much we have to increase x until it's divisible by 64.
fn pad_len(x: usize) -> usize {
    (BLOCK_SIZE - (x % BLOCK_SIZE)) % BLOCK_SIZE
}

/// Add padding to the vec.
pub fn add_padding(length: usize, buf: &mut Vec<u8>) {
    // Add single 1-bit.
    buf.push(0x80);
    let pad_len = pad_len(length + 1 + 8);

    // Add the padding zeroes.
    let mut zeros = vec![0x00; pad_len];
    buf.append(&mut zeros);

    // Add the length of the original message (in bits) as 64-bit integer.
    let len_bits = (length as u64) * 8;
    buf.append(&mut len_bits.to_be_bytes().to_vec());
}

// Here comes the tests!
#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    fn check_auth_sha(secret: &[u8], restrictions: Vec<Restriction>) -> [u8; 32] {
        let mut stream = secret.to_vec();

        for r in restrictions {
            add_padding(stream.len(), &mut stream);
            stream.append(&mut r.encode().as_bytes().to_vec());
        }

        let mut hasher = Sha256::new();
        hasher.update(&stream);
        hasher.finalize().try_into().unwrap()
    }

    #[test]
    fn test_rune_auth() {
        let secret = vec![0u8; 16];
        let mut mr = Rune::new_master_rune(&secret, vec![], None, None).unwrap();

        let digest = check_auth_sha(&secret, vec![]);
        assert_eq!(mr.authcode(), digest);
        assert!(mr.is_authorized(Rune::from_authcode(mr.authcode(), vec![])));

        // Add restriction
        let restriction = Restriction::new(vec![Alternative::new(
            "f1".into(),
            Condition::Equal,
            "v1".into(),
            false,
        )
        .unwrap()])
        .unwrap();
        mr.add_restriction(restriction.clone());
        assert_eq!(
            mr.authcode(),
            check_auth_sha(&secret, vec![restriction.clone()])
        );
        assert!(!mr.is_authorized(Rune::from_authcode(mr.authcode(), vec![])));
        assert!(mr.is_authorized(Rune::from_authcode(
            mr.authcode(),
            vec![restriction.clone()]
        )));

        // Add long restriction
        let field = (0..17).map(|_| "f").collect();
        let value = (0..65).map(|_| "v1").collect();
        let alternative = Alternative::new(field, Condition::Equal, value, false).unwrap();
        let long_restriction = Restriction::new(vec![alternative]).unwrap();
        mr.add_restriction(long_restriction.clone());
        assert_eq!(
            mr.authcode(),
            check_auth_sha(&secret, vec![restriction.clone(), long_restriction.clone()])
        );
        assert!(!mr.is_authorized(Rune::from_authcode(
            mr.authcode(),
            vec![restriction.clone()]
        )));
        assert!(!mr.is_authorized(Rune::from_authcode(
            mr.authcode(),
            vec![long_restriction.clone()]
        )));
        assert!(!mr.is_authorized(Rune::from_authcode(
            mr.authcode(),
            vec![long_restriction.clone(), restriction.clone()]
        )));
        assert!(mr.is_authorized(Rune::from_authcode(
            mr.authcode(),
            vec![restriction, long_restriction]
        )));
    }

    #[test]
    fn test_decode_encode_rune() {
        // Decoding and encoding a rune from a string should lead to the same
        // output string.
        let rune_str = "6035731a2cbb022cbeb67645aa0f8a26653d8cc454e0e087d4d19d282b8da4bd:=1";
        let rune = Rune::from_str(rune_str).unwrap();
        assert_eq!(rune.to_string(), rune_str);

        // Decoding and encoding a rune from a string should lead to the same
        // output string.
        let rune_str = "YDVzGiy7Aiy-tnZFqg-KJmU9jMRU4OCH1NGdKCuNpL09MQ==";
        let rune = Rune::from_base64(rune_str).unwrap();
        assert_eq!(rune.to_base64(), rune_str);
    }

    #[test]
    fn test_contains_punctuation() {
        for c in PUNCTUATION {
            assert!(contains_punctuation(&c.to_string()));
        }
        let a = "Foo=123".to_string();
        assert!(contains_punctuation(&a));
        let a = "NoPunct".to_string();
        assert!(!contains_punctuation(&a));
    }

    #[test]
    fn test_pad_len() {
        let a = pad_len(10);
        assert_eq!(a, 54);
        let a = pad_len(64);
        assert_eq!(a, 0);
        let a = pad_len(122);
        assert_eq!(a, 6);
        let a = pad_len(128);
        assert_eq!(a, 0);
    }

    #[test]
    fn test_new_restriction() {
        let res = Restriction::new(vec![]);
        assert!(res.is_err());
        assert_eq!(
            res.unwrap_err(),
            RuneError::Unknown("restriction must have some alternatives".to_string())
        );
        let a1 = Alternative::new(
            "".to_string(),
            Condition::Equal,
            "1010001".to_string(),
            true,
        )
        .unwrap();
        let a2 = Alternative::new(
            "ABC".to_string(),
            Condition::NotEqual,
            "1".to_string(),
            false,
        )
        .unwrap();
        let res = Restriction::new(vec![a1, a2]);
        assert!(res.is_err());
        assert_eq!(
            res.unwrap_err(),
            RuneError::Unknown("unique_id field cannot have alternatives".to_string())
        );
    }

    #[test]
    fn test_decode_restriction() -> Result<(), RuneError> {
        let s = "foo=bar|fizz/buzz&bar^foo";
        let (res, rest) = Restriction::decode(s, false)?;
        assert!(res.alternatives.len() == 2);
        assert!(rest == "bar^foo");
        Ok(())
    }

    #[test]
    fn test_new_alternative() {
        // Test id field not allowed
        let alt = Alternative::new("".to_string(), Condition::Equal, "1".to_string(), false);
        assert!(alt.is_err());
        // Test id field is allowed, but not condition '='
        let alt = Alternative::new("".to_string(), Condition::NotEqual, "1".to_string(), true);
        assert!(alt.is_err());
        // Test id field is allowed and condition is '='
        let alt = Alternative::new("".to_string(), Condition::Equal, "1".to_string(), true);
        assert!(alt.is_ok());
    }

    #[test]
    fn test_encode_alternative() {
        let alt =
            Alternative::new("f1".to_string(), Condition::IntGT, "1".to_string(), false).unwrap();
        assert_eq!(alt.encode(), "f1>1".to_string());
    }

    #[test]
    fn test_decode_alternative() -> Result<(), RuneError> {
        let s = "foo=bar|fizz/buzz&bar^foo";
        let (alt, rest) = Alternative::decode(s, false)?;
        assert!(alt.field == *"foo");
        assert!(alt.value == *"bar");
        assert!(alt.cond == Condition::Equal);
        assert!(rest == "fizz/buzz&bar^foo", "got {}", rest);

        let s = "foo=bar&bar^foo";
        let (alt, rest) = Alternative::decode(s, false)?;
        assert!(alt.field == *"foo");
        assert!(alt.value == *"bar");
        assert!(alt.cond == Condition::Equal);
        assert!(rest == "&bar^foo");

        let s = "nocondition";
        let result = Alternative::decode(s, false);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_alternatives() -> Result<(), RuneError> {
        // test_alt_condition takes away some of the overhead to make the test
        // readable.
        fn test_alt_condition(
            alt: &Alternative,
            field: String,
            value: String,
        ) -> Result<(), RuneError> {
            let mut t: HashMap<String, Box<dyn Tester>> = HashMap::new();
            t.insert(field, Box::new(ConditionTester { value }));
            alt.test(&t)
        }

        // Condition: `!`
        let alt = Alternative::new("f1".to_string(), Condition::Missing, "".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is present"
        );
        assert!(test_alt_condition(&alt, "f2".to_string(), "1".to_string()).is_ok());

        // Condition: `=`
        let alt = Alternative::new("f1".to_string(), Condition::Equal, "1".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert!(test_alt_condition(&alt, "f1".to_string(), "1".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "01".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: != 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: != 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "010".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: != 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10101".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: != 1"
        );

        // Condition: `/`
        let alt = Alternative::new(
            "f1".to_string(),
            Condition::NotEqual,
            "1".to_string(),
            false,
        )?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: = 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "01".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "010".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());

        // Condition: `^`
        let alt = Alternative::new(
            "f1".to_string(),
            Condition::BeginsWith,
            "1".to_string(),
            false,
        )?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert!(test_alt_condition(&alt, "f1".to_string(), "1".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "01".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: does not start with 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "010".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: does not start with 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());

        // Condition: `$`
        let alt = Alternative::new(
            "f1".to_string(),
            Condition::EndsWith,
            "1".to_string(),
            false,
        )?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert!(test_alt_condition(&alt, "f1".to_string(), "1".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "01".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: does not end with 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "010".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: does not end with 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());

        // Condition: `~`
        let alt = Alternative::new(
            "f1".to_string(),
            Condition::Contains,
            "1".to_string(),
            false,
        )?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert!(test_alt_condition(&alt, "f1".to_string(), "1".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "01".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "010".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "020".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: does not contain 1"
        );

        // Condition: `<`
        let alt = Alternative::new("f1".to_string(), Condition::IntLT, "1".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: >= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "01".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: >= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: >= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "010".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: >= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10101".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: >= 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "0".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "x".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: not an integer field"
        );

        // Condition: `<`: check the non-integer alternative.
        let alt = Alternative::new("f1".to_string(), Condition::IntLT, "x".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: not a valid integer"
        );

        // Condition: `>`
        let alt = Alternative::new("f1".to_string(), Condition::IntGT, "1".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: <= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "01".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: <= 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "010".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "0".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: <= 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "x".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: not an integer field"
        );

        // Condition: `>`: check the non-integer alternative.
        let alt = Alternative::new("f1".to_string(), Condition::IntGT, "x".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: not a valid integer"
        );

        // Condition: `{`
        let alt = Alternative::new("f1".to_string(), Condition::LexLT, "1".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered after 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "01".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered after 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "010".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "10101".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered after 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "0".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "020".to_string()).is_ok());

        // Condition: `}`
        let alt = Alternative::new("f1".to_string(), Condition::LexGT, "1".to_string(), false)?;
        assert!(alt.test(&HashMap::new()).unwrap_err().to_string() == *"f1: is missing");
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "1".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered before 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "01".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered before 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "010".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered before 1"
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "0".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered before 1"
        );
        assert_eq!(
            test_alt_condition(&alt, "f1".to_string(), "020".to_string())
                .unwrap_err()
                .to_string(),
            *"f1: is the same or ordered before 1"
        );

        // Condition: `#`
        let alt = Alternative::new("f1".to_string(), Condition::Comment, "1".to_string(), false)?;
        assert!(
            alt.test(&HashMap::new()).is_ok(),
            "Expected None, got {}",
            alt.test(&HashMap::new()).unwrap_err().to_string(),
        );
        assert!(test_alt_condition(&alt, "f1".to_string(), "1".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "01".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "10101".to_string()).is_ok());
        assert!(test_alt_condition(&alt, "f1".to_string(), "0".to_string()).is_ok());
        Ok(())
    }

    #[test]
    fn test_rune_is_authorized() -> Result<(), RuneError> {
        let secret = vec![0; 16];
        let (r1, _) = Restriction::decode("f1=v1|f2=v2", false)?;
        let (r2, _) = Restriction::decode("f2/v3", false)?;
        let mr = Rune::new_master_rune(&secret, vec![r1, r2], None, None)?;
        let enc = mr.to_string();

        let mut other = Rune::from_str(&enc)?;
        let (r3, _) = Restriction::decode("f4=v4", false)?;
        other.add_restriction(r3);

        assert!(mr.is_authorized(other));
        Ok(())
    }

    #[test]
    fn test_vectors() {
        use std::fs::File;
        use std::io::{BufRead, BufReader};
        use std::str::FromStr;

        let secret = vec![0u8; 16];
        let mr = Rune::new_master_rune(&secret, vec![], None, None).unwrap();

        let mut last_rune1: Option<Rune> = None;
        let mut last_rune2: Option<Rune> = None;

        // Read vectors.
        let f = File::open("tests/test_vectors.csv")
            .map_err(|e| RuneError::Unknown(format!("{}", e)))
            .unwrap();
        let buf = BufReader::new(f);
        for result in buf.lines() {
            let line = result.unwrap();
            let splits: Vec<&str> = line.split(',').collect();
            match splits[0] {
                "VALID" => {
                    println!("{}", splits[1]);
                    let rune1 = Rune::from_str(splits[2]).unwrap();
                    let rune2: Rune = Rune::from_base64(splits[3]).unwrap();
                    last_rune1 = Some(rune1.clone());
                    last_rune2 = Some(rune2.clone());
                    assert_eq!(rune1.to_string(), rune2.to_string());
                    assert_eq!(rune1.to_base64(), rune2.to_base64());
                    assert!(mr.is_authorized(rune1.clone()));
                    assert!(mr.is_authorized(rune2.clone()));
                    if splits.len() == 6 {
                        assert_eq!(
                            rune1.restrictions[0].alternatives[0].encode(),
                            format!("={}-{}", splits[4], splits[5])
                        )
                    } else if splits.len() == 5 {
                        assert_eq!(
                            rune1.restrictions[0].alternatives[0].encode(),
                            format!("={}", splits[4])
                        );
                    } else {
                        // Must not have an ID field
                        assert!(splits.len() == 4);
                        assert!(
                            rune1.restrictions.is_empty()
                                || !rune1.restrictions[0].alternatives[0]
                                    .encode()
                                    .starts_with('=')
                        )
                    }
                }
                "MALFORMED" => {
                    // todo: Check for correct error message.
                    println!("{}", splits[1]);
                    let result1 = Rune::from_str(splits[2]);
                    let result2 = Rune::from_base64(splits[3]);
                    assert!(result1.is_err());
                    assert!(result2.is_err());
                }
                "BAD DERIVATION" => {
                    println!("{}", splits[1]);
                    let rune1 = Rune::from_str(splits[2]).unwrap();
                    let rune2 = Rune::from_base64(splits[3]).unwrap();
                    assert!(!mr.is_authorized(rune1.clone()));
                    assert!(!mr.is_authorized(rune2.clone()));
                }
                "PASS" | "FAIL" => {
                    assert!(splits[0] == "PASS" || splits[0] == "FAIL");
                    let rune1 = last_rune1.clone().unwrap();
                    let rune2 = last_rune2.clone().unwrap();
                    let mut values: HashMap<String, Box<dyn Tester>> = HashMap::new();
                    let rest = splits[1..].to_vec();
                    for var in rest {
                        let parts: Vec<&str> = var.split('=').collect();
                        assert_eq!(parts.len(), 2);
                        values.insert(
                            parts[0].to_string(),
                            Box::new(ConditionTester {
                                value: parts[1].to_string(),
                            }),
                        );
                    }
                    if splits[0] == "PASS" {
                        assert!(rune1.are_restrictions_met(&values).is_ok());
                        assert!(rune2.are_restrictions_met(&values).is_ok());
                    } else {
                        assert!(rune1.are_restrictions_met(&values).is_err());
                        assert!(rune2.are_restrictions_met(&values).is_err());
                    }
                }
                "DERIVE" => {
                    println!("{}", splits[1]);
                    let mut rune1 = Rune::from_base64(splits[2]).unwrap();
                    assert!(mr.is_authorized(rune1.clone()));
                    let rune2 = Rune::from_base64(splits[3]).unwrap();
                    assert!(mr.is_authorized(rune2.clone()));
                    // assert!(rune1.is_authorized(rune2.clone()));

                    let mut alts = Vec::new();
                    let mut b = &splits[4..];
                    while !b.is_empty() {
                        alts.push(
                            Alternative::new(
                                b[0].to_string(),
                                b[1].try_into().unwrap(),
                                b[2].to_string(),
                                true,
                            )
                            .unwrap(),
                        );
                        b = &b[3..];
                    }
                    rune1.add_restriction(Restriction { alternatives: alts });
                    assert!(rune1.authcode() == rune2.authcode());
                    last_rune1 = Some(rune1);
                    last_rune2 = Some(rune2);
                }
                p => {
                    panic!("{} is not handled", p)
                }
            }
        }
    }
}
