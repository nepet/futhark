use std::collections::HashMap;

use chrono::Utc;
use futhark::{Condition, Restriction, Rune, Tester};

/// TimelimitTester implements a `futhark::Tester` that is called to check if
/// a rune is timed out. This is if the time at which the rune is used is later
/// than the time given by the `before` field.
/// The time is given as a utc timestamp.
struct TimelimitTester {}

impl Tester for TimelimitTester {
    fn test(&self, alt: &futhark::Alternative) -> Option<String> {
        let now = Utc::now().naive_utc();

        if alt.get_field() != "before" {
            return Some("only understands `before` fields".to_string());
        }
        if alt.get_condition() != Condition::Equal {
            return Some("can only work on equal condition".to_string());
        }
        let value = match alt.get_value().parse::<i64>() {
            Ok(v) => v,
            Err(e) => return Some(e.to_string()),
        };
        let dt = match chrono::NaiveDateTime::from_timestamp_opt(value, 0) {
            Some(t) => t,
            None => return Some("could not parse timestamp".to_string()),
        };

        // Compare times: `now` has to be before the `before` value.
        if (dt - now).num_seconds() <= 0 {
            Some("it is too late to use this rune".to_string())
        } else {
            None
        }
    }
}

fn main() {
    // Create a master rune to append rules to.
    let secret = [0u8; 16];
    let mut mr = Rune::new_master_rune(&secret, vec![], None, None).unwrap();

    // Add restriction.
    let now = Utc::now().naive_utc().timestamp();
    let (res, _) = Restriction::decode(&format!("before={}", now + 60), false).unwrap();
    mr.add_restriction(res);
    let rune = mr.to_base64();

    // Check rune, should be ok as "before" is 60s in the future.
    let mut checks: HashMap<String, Box<dyn Tester>> = HashMap::new();
    checks.insert("before".to_string(), Box::new(TimelimitTester{}));
    let result = mr.check_with_reason(&rune, &checks).unwrap();
    println!("{:?}", result); // Output: None, as the rune is still valid

    // Add another restriction.
    let (res, _) = Restriction::decode(&format!("before={}", now - 60), false).unwrap();
    mr.add_restriction(res);
    let rune = mr.to_base64();

    // Check rune, should fail as new "before" is 60s in the past.
    let mut checks: HashMap<String, Box<dyn Tester>> = HashMap::new();
    checks.insert("before".to_string(), Box::new(TimelimitTester{}));
    let result = mr.check_with_reason(&rune, &checks).unwrap();
    println!("{:?}", result); // Output: Some("it is too late to use this rune")
}
