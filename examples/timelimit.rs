use anyhow::Result;
use std::collections::HashMap;

use chrono::Utc;
use futhark::{Alternative, Check, Condition, Restriction, Rune, RuneError};

/// TimelimitTester implements a `futhark::Tester` that is called to check if
/// a rune is timed out. This is if the time at which the rune is used is later
/// than the time given by the `before` field.
/// The time is given as a utc timestamp.
#[derive(Clone)]
struct TimelimitTester {}

impl Check for TimelimitTester {
    fn check_alternative(&self, alt: &Alternative) -> Result<(), RuneError> {
        let now = Utc::now().naive_utc();

        if alt.get_field() != "before" {
            return Err(RuneError::InvalidField(
                "only understands `before` fields".to_string(),
            ));
        }
        if alt.get_condition() != Condition::Equal {
            return Err(RuneError::InvalidCondition(
                "can only work on equal condition".to_string(),
            ));
        }
        let value = match alt.get_value().parse::<i64>() {
            Ok(v) => v,
            Err(e) => return Err(RuneError::ValueError(e.to_string())),
        };
        let dt = match chrono::NaiveDateTime::from_timestamp_opt(value, 0) {
            Some(t) => t,
            None => return Err(RuneError::Unknown("could not parse timestamp".to_string())),
        };

        // Compare times: `now` has to be before the `before` value.
        if (dt - now).num_seconds() <= 0 {
            return Err(RuneError::ValueError(
                "it is too late to use this rune".to_string(),
            ));
        }
        Ok(())
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
    let check = mr.check_with_reason(&rune, TimelimitTester {});
    println!("{:?}", check); // Output: Ok(())

    // Add another restriction.
    let (res, _) = Restriction::decode(&format!("before={}", now - 60), false).unwrap();
    mr.add_restriction(res);
    let rune = mr.to_base64();

    // Check rune, should fail as new "before" is 60s in the past.
    let check = mr.check_with_reason(&rune, TimelimitTester {});
    println!("{:?}", check); // Output: Err(ValueError("it is too late to use this rune"))
}
