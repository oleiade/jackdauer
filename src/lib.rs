//! Use this crate to easily parse various time formats to durations.
//!
//! It provides stratight forward functions to parse durations from a
//!  textual representation, into [`std::time::Duration`](https://doc.rust-lang.org/stable/std/time/struct.Duration.html) instances.
//! It focuses on providing a simple but deep interface, that's easy and
//! intuitive to use, while remaining performant.
//!
//!
//! # Installation
//!
//! Ddd it as a dependency to your `Cargo.toml`
//! ```toml
//! [dependencies]
//! jackdauer = "0.1.0"
//! ```
//!
//! # Examples
//! ```rust
//! use jackdauer::duration;
//! use std::time::Duration;
//!
//! let nanoseconds = duration("1 nanosecond");
//! let milliseconds = duration("2 milliseconds");
//! let seconds = duration("3 seconds");
//! let minutes = duration("4 minutes");
//! let hours = duration("5 hours");
//! let day = duration("6 days");
//! let week = duration("7 weeks");
//! let month = duration("8 months");
//! let year = duration("9 months");
//! let real_big_duration = duration("9 years, 8 months, 7 weeks and 6 days");
//! let real_small_duration = duration("4 minutes 3 seconds, 2 milliseconds and 1 nanosecond");
//! ```

use std::time::Duration;

/// Parses a `std::time::Duration` from a human readable string of characters.
///
/// The supported syntax for durations consists in a comma separated list of
/// time values, followed by their respective time unit. Alternatively, the "and"
/// keyword can be used in place of a comma. While time values are only accepted
/// in their numerical form, time units are accepted in both their
/// singular and plural forms.
///
/// If the provided string cannot' be parsed, a `ParseError` will be
/// returned as part of the `Result`.
///
/// # Reference
///
/// The accepted time units formats are as follows:
/// - **Years**: `years`, `year` and `y` are accepted
/// - **Months**: `months`, `month`, and `mo` are accepted
/// - **Weeks**: `weeks`, `week`, and `w` are accepted
/// - **Days**: `days`, `day`, and `d` are accepted
/// - **Hours**: `hours`, `hour`, and `h` are accepted
/// - **Minutes**: `minutes` `mins`, and `min` are accepted
/// - **Seconds**: `seconds`, `second`, `secs`, `sec` and `s` are accepted
/// - **Milliseconds**: `milliseconds`, `millisecond`, `ms` are accepted
/// - **Nanoseconds**: `nanoseconds`, `nanosecond`, `ns` are accepted
///
/// # Examples
///
/// ```rust
/// use jackdauer::duration;
///
/// // Singular
/// let nanoseconds = duration("1 nanosecond");
///
/// // Plural
/// let milliseconds = duration("2 milliseconds");
///
/// // Full syntax example
/// let small = duration("3 seconds, 2 milliseconds and 1 nanosecond");
/// ```
pub fn duration(input: &str) -> Result<Duration, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std()))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of years contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::years;
///
/// assert_eq!(years("365 days"), Ok(1));
/// assert_eq!(years("1 year"), Ok(1));
/// assert_eq!(years("2 years"), Ok(2));
/// assert_eq!(years("1 day"), Ok(0));
/// ```
pub fn years(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_YEAR))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of months contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::months;
///
/// assert_eq!(months("30 days"), Ok(1));
/// assert_eq!(months("1 month"), Ok(1));
/// assert_eq!(months("2 months"), Ok(2));
/// assert_eq!(months("1 year"), Ok(12));
/// assert_eq!(months("1 week"), Ok(0));
/// ```
pub fn months(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_MONTH))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of weeks contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::weeks;
///
/// assert_eq!(weeks("7 days"), Ok(1));
/// assert_eq!(weeks("1 week"), Ok(1));
/// assert_eq!(weeks("2 weeks"), Ok(2));
/// assert_eq!(weeks("1 month"), Ok(4));
/// assert_eq!(weeks("2 years"), Ok(104));
/// assert_eq!(weeks("1 day"), Ok(0));
/// ```
pub fn weeks(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_WEEK))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of days contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::days;
///
/// assert_eq!(days("24 hours"), Ok(1));
/// assert_eq!(days("1 day"), Ok(1));
/// assert_eq!(days("2 days"), Ok(2));
/// assert_eq!(days("1 week"), Ok(7));
/// assert_eq!(days("2 months"), Ok(60));
/// assert_eq!(days("3 years"), Ok(1_095));
/// assert_eq!(days("1 hour"), Ok(0))
/// ```
pub fn days(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_DAY))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of hours contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::hours;
///
/// assert_eq!(hours("60 minutes"), Ok(1));
/// assert_eq!(hours("1 hour"), Ok(1));
/// assert_eq!(hours("2 hours"), Ok(2));
/// assert_eq!(hours("3 days"), Ok(72));
/// assert_eq!(hours("4 weeks"), Ok(672));
/// assert_eq!(hours("5 months"), Ok(3_600));
/// assert_eq!(hours("6 years"), Ok(52_560));
/// assert_eq!(hours("1 minute"), Ok(0));
pub fn hours(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_HOUR))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of minutes contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::minutes;
///
/// assert_eq!(minutes("60 seconds"), Ok(1));
/// assert_eq!(minutes("1 minute"), Ok(1));
/// assert_eq!(minutes("2 minutes"), Ok(2));
/// assert_eq!(minutes("3 hours"), Ok(180));
/// assert_eq!(minutes("4 days"), Ok(5_760));
/// assert_eq!(minutes("5 weeks"), Ok(50_400));
/// assert_eq!(minutes("6 months"), Ok(259_200));
/// assert_eq!(minutes("7 years"), Ok(3_679_200));
/// assert_eq!(minutes("1 second"), Ok(0));
pub fn minutes(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs() / crate::time::SECONDS_PER_MINUTE))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of seconds contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::seconds;
///
/// assert_eq!(seconds("1000 milliseconds"), Ok(1));
/// assert_eq!(seconds("1 second"), Ok(1));
/// assert_eq!(seconds("2 seconds"), Ok(2));
/// assert_eq!(seconds("3 minutes"), Ok(180));
/// assert_eq!(seconds("4 hours"), Ok(14_400));
/// assert_eq!(seconds("5 days"), Ok(432_000));
/// assert_eq!(seconds("6 weeks"), Ok(3_628_800));
/// assert_eq!(seconds("7 months"), Ok(18_144_000));
/// assert_eq!(seconds("8 years"), Ok(252_288_000));
pub fn seconds(input: &str) -> Result<u64, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_secs()))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of milliseconds contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::milliseconds;
///
/// assert_eq!(milliseconds("1000000 nanoseconds"), Ok(1));
/// assert_eq!(milliseconds("1 millisecond"), Ok(1));
/// assert_eq!(milliseconds("2 milliseconds"), Ok(2));
/// assert_eq!(milliseconds("3 seconds"), Ok(3_000));
/// assert_eq!(milliseconds("4 hours"), Ok(14_400_000));
/// assert_eq!(milliseconds("5 days"), Ok(432_000_000));
/// assert_eq!(milliseconds("6 weeks"), Ok(3_628_800_000));
/// assert_eq!(milliseconds("7 months"), Ok(18_144_000_000));
/// assert_eq!(milliseconds("8 years"), Ok(252_288_000_000));
/// assert_eq!(milliseconds("9 nanoseconds"), Ok(0))
pub fn milliseconds(input: &str) -> Result<u128, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_millis()))
        .map_err(|_| crate::error::Error::ParseError)?
}

/// Returns the total number of nanoseconds contained in the parsed human readable duration.
///
/// # Examples
///
/// ```rust
/// use jackdauer::nanoseconds;
///
/// assert_eq!(nanoseconds("1 nanosecond"), Ok(1));
/// assert_eq!(nanoseconds("2 nanoseconds"), Ok(2));
/// assert_eq!(nanoseconds("3 milliseconds"), Ok(3_000_000));
/// assert_eq!(nanoseconds("4 seconds"), Ok(4_000_000_000));
/// assert_eq!(nanoseconds("5 hours"), Ok(18_000_000_000_000));
/// assert_eq!(nanoseconds("6 days"), Ok(518_400_000_000_000));
/// assert_eq!(nanoseconds("7 weeks"), Ok(4_233_600_000_000_000));
/// assert_eq!(nanoseconds("8 months"), Ok(20_736_000_000_000_000));
/// assert_eq!(nanoseconds("9 years"), Ok(283_824_000_000_000_000));
pub fn nanoseconds(input: &str) -> Result<u128, crate::error::Error> {
    crate::parser::duration(input)
        .map(|(_, duration)| Ok(duration.to_std().as_nanos()))
        .map_err(|_| crate::error::Error::ParseError)?
}

pub mod error {
    //! Error management
    use std::fmt;

    /// The error type indicating a provided human readable duration error
    #[derive(Debug, PartialEq)]
    pub enum Error {
        ParseError,
    }

    impl std::error::Error for Error {}

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Error::ParseError => write!(f, "parsing the expression failed"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        days, duration, hours, milliseconds, minutes, months, nanoseconds, seconds, weeks, years,
    };
    use std::time::Duration;

    #[test]
    fn test_duration() {
        assert_eq!(
            duration("1 year"),
            Ok(Duration::new(crate::time::SECONDS_PER_YEAR, 0))
        );
        assert_eq!(
            duration("1 month"),
            Ok(Duration::new(crate::time::SECONDS_PER_MONTH, 0))
        );
        assert_eq!(
            duration("1 week"),
            Ok(Duration::new(crate::time::SECONDS_PER_WEEK, 0))
        );
        assert_eq!(
            duration("1 day"),
            Ok(Duration::new(crate::time::SECONDS_PER_DAY, 0))
        );
        assert_eq!(
            duration("1 hour"),
            Ok(Duration::new(crate::time::SECONDS_PER_HOUR, 0))
        );
        assert_eq!(
            duration("1 minute"),
            Ok(Duration::new(crate::time::SECONDS_PER_MINUTE, 0))
        );
        assert_eq!(duration("1 second"), Ok(Duration::new(1, 0)));
        assert_eq!(duration("1 millisecond"), Ok(Duration::new(0, 1_000_000)));
        assert_eq!(duration("1 nanosecond"), Ok(Duration::new(0, 1)));
        assert_eq!(
            duration("1 year 2 months"),
            Ok(Duration::new(36_720_000, 0))
        );
        assert_eq!(
            duration("1 year, 2 months"),
            Ok(Duration::new(36_720_000, 0))
        );
        assert_eq!(
            duration("1 year and 2 months"),
            Ok(Duration::new(36_720_000, 0))
        );
        assert_eq!(
            duration("1 year, 2 months and 3 weeks"),
            Ok(Duration::new(38_534_400, 0))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks and 4 days"),
            Ok(Duration::new(38_880_000, 0))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks, 4 days and 5 hours"),
            Ok(Duration::new(38_898_000, 0))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks, 4 days, 5 hours and 6 minutes"),
            Ok(Duration::new(38_898_360, 0))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes and 7 seconds"),
            Ok(Duration::new(38_898_367, 0))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds and 8 milliseconds"),
            Ok(Duration::new(38_898_367, 8_000_000))
        );
        assert_eq!(
            duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds, 8 milliseconds and 9 nanoseconds"),
            Ok(Duration::new(38_898_367, 8_000_009))
        );
    }

    #[test]
    fn test_years() {
        assert_eq!(years("0 years"), Ok(0));
        assert_eq!(years("0 year"), Ok(0));
        assert_eq!(years("0 y"), Ok(0));
        assert_eq!(years("0years"), Ok(0));
        assert_eq!(years("0year"), Ok(0));
        assert_eq!(years("0y"), Ok(0));
        assert_eq!(years("1 year"), Ok(1));
        assert_eq!(years("1 y"), Ok(1));
        assert_eq!(years("1year"), Ok(1));
        assert_eq!(years("1y"), Ok(1));
        assert_eq!(years("2 years"), Ok(2));
        assert_eq!(years("2 year"), Ok(2));
        assert_eq!(years("2 y"), Ok(2));
        assert_eq!(years("2years"), Ok(2));
        assert_eq!(years("2year"), Ok(2));
        assert_eq!(years("2y"), Ok(2));
    }

    #[test]
    fn test_months() {
        assert_eq!(months("1 year"), Ok(12));
        assert_eq!(months("0 months"), Ok(0));
        assert_eq!(months("0 month"), Ok(0));
        assert_eq!(months("0 mo"), Ok(0));
        assert_eq!(months("0months"), Ok(0));
        assert_eq!(months("0month"), Ok(0));
        assert_eq!(months("0mo"), Ok(0));
        assert_eq!(months("1 month"), Ok(1));
        assert_eq!(months("1 mo"), Ok(1));
        assert_eq!(months("1month"), Ok(1));
        assert_eq!(months("1mo"), Ok(1));
        assert_eq!(months("2 months"), Ok(2));
        assert_eq!(months("2 month"), Ok(2));
        assert_eq!(months("2 mo"), Ok(2));
        assert_eq!(months("2months"), Ok(2));
        assert_eq!(months("2month"), Ok(2));
        assert_eq!(months("2mo"), Ok(2));
    }

    #[test]
    fn test_weeks() {
        assert_eq!(weeks("1 year"), Ok(52));
        assert_eq!(weeks("1 month"), Ok(4));
        assert_eq!(weeks("0 weeks"), Ok(0));
        assert_eq!(weeks("0 week"), Ok(0));
        assert_eq!(weeks("0 w"), Ok(0));
        assert_eq!(weeks("0weeks"), Ok(0));
        assert_eq!(weeks("0week"), Ok(0));
        assert_eq!(weeks("0w"), Ok(0));
        assert_eq!(weeks("1 week"), Ok(1));
        assert_eq!(weeks("1 w"), Ok(1));
        assert_eq!(weeks("1week"), Ok(1));
        assert_eq!(weeks("1w"), Ok(1));
        assert_eq!(weeks("2 weeks"), Ok(2));
        assert_eq!(weeks("2 week"), Ok(2));
        assert_eq!(weeks("2 w"), Ok(2));
        assert_eq!(weeks("2weeks"), Ok(2));
        assert_eq!(weeks("2week"), Ok(2));
        assert_eq!(weeks("2w"), Ok(2));
    }

    #[test]
    fn test_days() {
        assert_eq!(days("1 year"), Ok(365));
        assert_eq!(days("1 month"), Ok(30));
        assert_eq!(days("1 week"), Ok(7));
        assert_eq!(days("0 days"), Ok(0));
        assert_eq!(days("0 day"), Ok(0));
        assert_eq!(days("0 d"), Ok(0));
        assert_eq!(days("0days"), Ok(0));
        assert_eq!(days("0day"), Ok(0));
        assert_eq!(days("0d"), Ok(0));
        assert_eq!(days("1 day"), Ok(1));
        assert_eq!(days("1 d"), Ok(1));
        assert_eq!(days("1day"), Ok(1));
        assert_eq!(days("1d"), Ok(1));
        assert_eq!(days("2 days"), Ok(2));
        assert_eq!(days("2 day"), Ok(2));
        assert_eq!(days("2 d"), Ok(2));
        assert_eq!(days("2days"), Ok(2));
        assert_eq!(days("2day"), Ok(2));
        assert_eq!(days("2d"), Ok(2));
    }

    #[test]
    fn test_hours() {
        assert_eq!(hours("1 year"), Ok(8760));
        assert_eq!(hours("1 month"), Ok(720));
        assert_eq!(hours("1 week"), Ok(168));
        assert_eq!(hours("1 day"), Ok(24));
        assert_eq!(hours("0 hours"), Ok(0));
        assert_eq!(hours("0 hour"), Ok(0));
        assert_eq!(hours("0 h"), Ok(0));
        assert_eq!(hours("0hours"), Ok(0));
        assert_eq!(hours("0hour"), Ok(0));
        assert_eq!(hours("0h"), Ok(0));
        assert_eq!(hours("1 hour"), Ok(1));
        assert_eq!(hours("1 h"), Ok(1));
        assert_eq!(hours("1hour"), Ok(1));
        assert_eq!(hours("1h"), Ok(1));
        assert_eq!(hours("2 hours"), Ok(2));
        assert_eq!(hours("2 hour"), Ok(2));
        assert_eq!(hours("2 h"), Ok(2));
        assert_eq!(hours("2hours"), Ok(2));
        assert_eq!(hours("2hour"), Ok(2));
        assert_eq!(hours("2h"), Ok(2));
    }

    #[test]
    fn test_minutes() {
        assert_eq!(minutes("1 year"), Ok(525_600));
        assert_eq!(minutes("1 month"), Ok(43_200));
        assert_eq!(minutes("1 week"), Ok(10_080));
        assert_eq!(minutes("1 day"), Ok(1440));
        assert_eq!(minutes("1 hour"), Ok(60));
        assert_eq!(minutes("2 minutes"), Ok(2));
        assert_eq!(minutes("1 minute"), Ok(1));
        assert_eq!(minutes("2minutes"), Ok(2));
        assert_eq!(minutes("1minute"), Ok(1));
        assert_eq!(minutes("2 mins"), Ok(2));
        assert_eq!(minutes("1 min"), Ok(1));
        assert_eq!(minutes("2mins"), Ok(2));
        assert_eq!(minutes("1min"), Ok(1));
    }

    #[test]
    fn test_seconds() {
        assert_eq!(seconds("1 year"), Ok(31_536_000));
        assert_eq!(seconds("1 month"), Ok(2_592_000));
        assert_eq!(seconds("1 week"), Ok(604_800));
        assert_eq!(seconds("1 day"), Ok(86_400));
        assert_eq!(seconds("1 hour"), Ok(3_600));
        assert_eq!(seconds("1 minute"), Ok(60));
        assert_eq!(seconds("2 seconds"), Ok(2));
        assert_eq!(seconds("1 second"), Ok(1));
        assert_eq!(seconds("2seconds"), Ok(2));
        assert_eq!(seconds("1second"), Ok(1));
        assert_eq!(seconds("2 secs"), Ok(2));
        assert_eq!(seconds("1 sec"), Ok(1));
        assert_eq!(seconds("2secs"), Ok(2));
        assert_eq!(seconds("1sec"), Ok(1));
        assert_eq!(seconds("2 s"), Ok(2));
        assert_eq!(seconds("1 s"), Ok(1));
        assert_eq!(seconds("2s"), Ok(2));
        assert_eq!(seconds("1s"), Ok(1));
    }

    #[test]
    fn test_milliseconds() {
        assert_eq!(milliseconds("1 second"), Ok(1000));
        assert_eq!(milliseconds("2 milliseconds"), Ok(2));
        assert_eq!(milliseconds("1 millisecond"), Ok(1));
        assert_eq!(milliseconds("2milliseconds"), Ok(2));
        assert_eq!(milliseconds("1millisecond"), Ok(1));
        assert_eq!(milliseconds("2 ms"), Ok(2));
        assert_eq!(milliseconds("1 ms"), Ok(1));
        assert_eq!(milliseconds("2ms"), Ok(2));
        assert_eq!(milliseconds("1ms"), Ok(1));
    }

    #[test]
    fn test_nanoseconds() {
        assert_eq!(nanoseconds("1 second"), Ok(1_000_000_000));
        assert_eq!(nanoseconds("2 nanoseconds"), Ok(2));
        assert_eq!(nanoseconds("1 nanosecond"), Ok(1));
        assert_eq!(nanoseconds("2nanoseconds"), Ok(2));
        assert_eq!(nanoseconds("1nanosecond"), Ok(1));
        assert_eq!(nanoseconds("2 ns"), Ok(2));
        assert_eq!(nanoseconds("1 ns"), Ok(1));
        assert_eq!(nanoseconds("2ns"), Ok(2));
        assert_eq!(nanoseconds("1ns"), Ok(1));
    }
}

mod time {
    // Constant holding the amount of seconds in a minute
    pub const SECONDS_PER_MINUTE: u64 = 60;

    // Constant holding the amount of seconds in an hour
    pub const SECONDS_PER_HOUR: u64 = SECONDS_PER_MINUTE * 60;

    // Constant holding the amount of seconds in a day
    pub const SECONDS_PER_DAY: u64 = SECONDS_PER_HOUR * 24;

    // Constant holding the amount of seconds in a week
    pub const SECONDS_PER_WEEK: u64 = SECONDS_PER_DAY * 7;

    // Constant holding the amount of seconds in a 30 days month
    pub const SECONDS_PER_MONTH: u64 = SECONDS_PER_DAY * 30;

    // Constant holding the amount of seconds in a non leap year
    pub const SECONDS_PER_YEAR: u64 = SECONDS_PER_DAY * 365;

    // Constant holding the amount of nanoseconds in a millisecond
    pub const NANOSECONDS_PER_MILLISECONDS: u32 = 1_000_000;

    /// Internal representation of a Duration component.
    #[derive(Clone, Debug, Default, PartialEq)]
    pub struct Duration {
        pub years: Option<u64>,
        pub months: Option<u64>,
        pub weeks: Option<u64>,
        pub days: Option<u64>,
        pub hours: Option<u64>,
        pub minutes: Option<u64>,
        pub seconds: Option<u64>,
        pub milliseconds: Option<u32>,
        pub nanoseconds: Option<u32>,
    }

    impl Duration {
        /// Convert an internal representation of a Duration back into
        /// a `std::time::Duration`.
        pub fn to_std(&self) -> std::time::Duration {
            let seconds = vec![
                self.years.map_or(0, |v| v * SECONDS_PER_YEAR),
                self.months.map_or(0, |v| v * SECONDS_PER_MONTH),
                self.weeks.map_or(0, |v| v * SECONDS_PER_WEEK),
                self.days.map_or(0, |v| v * SECONDS_PER_DAY),
                self.hours.map_or(0, |v| v * SECONDS_PER_HOUR),
                self.minutes.map_or(0, |v| v * SECONDS_PER_MINUTE),
                self.seconds.map_or(0, |v| v),
            ];

            let nanoseconds = vec![
                self.milliseconds
                    .map_or(0, |v| v * NANOSECONDS_PER_MILLISECONDS),
                self.nanoseconds.map_or(0, |v| v),
            ];

            std::time::Duration::new(seconds.iter().sum(), nanoseconds.iter().sum())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_duration_to_std() {
            assert_eq!(
                crate::time::Duration {
                    nanoseconds: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(0, 1)
            );

            assert_eq!(
                crate::time::Duration {
                    milliseconds: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(0, NANOSECONDS_PER_MILLISECONDS)
            );

            assert_eq!(
                crate::time::Duration {
                    seconds: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(1, 0)
            );

            assert_eq!(
                crate::time::Duration {
                    minutes: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_MINUTE, 0) // 60 seconds
            );

            assert_eq!(
                crate::time::Duration {
                    hours: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_HOUR, 0) // 60 seconds * 60 minutes
            );

            assert_eq!(
                crate::time::Duration {
                    days: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_DAY, 0) // 60 seconds * 60 minutes * 24 hours
            );

            assert_eq!(
                crate::time::Duration {
                    weeks: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_WEEK, 0) // 60 seconds * 60 minutes * 24 hours * 7 days
            );

            assert_eq!(
                crate::time::Duration {
                    months: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_MONTH, 0) // 60 seconds * 60 minutes * 24 hours * 30 days
            );

            assert_eq!(
                crate::time::Duration {
                    years: Some(1),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(SECONDS_PER_YEAR, 0) // 60 seconds * 60 minutes * 24 hours * 365 days
            );

            assert_eq!(
                crate::time::Duration {
                    nanoseconds: Some(1),
                    milliseconds: Some(2),
                    seconds: Some(3),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(3, 2 * NANOSECONDS_PER_MILLISECONDS + 1)
            );

            assert_eq!(
                crate::time::Duration {
                    nanoseconds: Some(1),
                    milliseconds: Some(2),
                    seconds: Some(3),
                    minutes: Some(4),
                    hours: Some(5),
                    ..Default::default()
                }
                .to_std(),
                std::time::Duration::new(
                    3 + (4 * SECONDS_PER_MINUTE) + (5 * SECONDS_PER_HOUR),
                    2 * NANOSECONDS_PER_MILLISECONDS + 1
                ) // 3 seconds + (4 * 60 seconds) + (5 * 60 seconds * 60 minutes)
            );
        }
    }
}

mod parser {
    use nom::branch::alt;
    use nom::bytes::complete::tag;
    use nom::character::complete::{digit0, multispace0};
    use nom::combinator::{all_consuming, map, map_res, opt, recognize};
    use nom::error::context;
    use nom::sequence::{delimited, preceded, terminated, tuple};
    use nom::IResult;

    pub fn duration(input: &str) -> IResult<&str, crate::time::Duration> {
        let parser = tuple((
            opt(terminated(years, delimiter)),
            opt(terminated(months, delimiter)),
            opt(terminated(weeks, delimiter)),
            opt(terminated(days, delimiter)),
            opt(terminated(hours, delimiter)),
            opt(terminated(minutes, delimiter)),
            opt(terminated(seconds, delimiter)),
            opt(terminated(milliseconds, delimiter)),
            opt(terminated(nanoseconds, delimiter)),
        ));

        map(
            all_consuming(parser),
            |(years, months, weeks, days, hours, minutes, seconds, milliseconds, nanoseconds)| {
                crate::time::Duration {
                    years,
                    months,
                    weeks,
                    days,
                    hours,
                    minutes,
                    seconds,
                    milliseconds,
                    nanoseconds,
                }
            },
        )(input)
    }

    fn delimiter(input: &str) -> IResult<&str, &str> {
        terminated(
            recognize(opt(alt((
                tag(","),
                delimited(multispace0, tag("and"), multispace0),
            )))),
            multispace0,
        )(input)
    }

    pub fn years(input: &str) -> IResult<&str, u64> {
        context(
            "years",
            terminated(unsigned_integer_64, preceded(multispace0, year)),
        )(input)
    }

    fn year(input: &str) -> IResult<&str, &str> {
        context("year", alt((tag("years"), tag("year"), tag("y"))))(input)
    }

    pub fn months(input: &str) -> IResult<&str, u64> {
        context(
            "months",
            terminated(unsigned_integer_64, preceded(multispace0, month)),
        )(input)
    }

    fn month(input: &str) -> IResult<&str, &str> {
        context("month", alt((tag("months"), tag("month"), tag("mo"))))(input)
    }

    pub fn weeks(input: &str) -> IResult<&str, u64> {
        context(
            "weeks",
            terminated(unsigned_integer_64, preceded(multispace0, week)),
        )(input)
    }

    fn week(input: &str) -> IResult<&str, &str> {
        context("week", alt((tag("weeks"), tag("week"), tag("w"))))(input)
    }

    pub fn days(input: &str) -> IResult<&str, u64> {
        context(
            "days",
            terminated(unsigned_integer_64, preceded(multispace0, day)),
        )(input)
    }

    fn day(input: &str) -> IResult<&str, &str> {
        context("day", alt((tag("days"), tag("day"), tag("d"))))(input)
    }

    pub fn hours(input: &str) -> IResult<&str, u64> {
        context(
            "hours",
            terminated(unsigned_integer_64, preceded(multispace0, hour)),
        )(input)
    }

    fn hour(input: &str) -> IResult<&str, &str> {
        context("hour", alt((tag("hours"), tag("hour"), tag("h"))))(input)
    }

    pub fn minutes(input: &str) -> IResult<&str, u64> {
        context(
            "minutes",
            terminated(unsigned_integer_64, preceded(multispace0, minute)),
        )(input)
    }

    fn minute(input: &str) -> IResult<&str, &str> {
        context(
            "minute",
            alt((tag("minutes"), tag("minute"), tag("mins"), tag("min"))),
        )(input)
    }

    pub fn seconds(input: &str) -> IResult<&str, u64> {
        context(
            "seconds",
            terminated(unsigned_integer_64, preceded(multispace0, second)),
        )(input)
    }

    fn second(input: &str) -> IResult<&str, &str> {
        context(
            "second",
            alt((
                tag("seconds"),
                tag("second"),
                tag("secs"),
                tag("sec"),
                tag("s"),
            )),
        )(input)
    }

    pub fn milliseconds(input: &str) -> IResult<&str, u32> {
        context(
            "milliseconds",
            terminated(unsigned_integer_32, preceded(multispace0, millisecond)),
        )(input)
    }

    fn millisecond(input: &str) -> IResult<&str, &str> {
        context(
            "millisecond",
            alt((tag("milliseconds"), tag("millisecond"), tag("ms"))),
        )(input)
    }

    pub fn nanoseconds(input: &str) -> IResult<&str, u32> {
        context(
            "nanoseconds",
            terminated(unsigned_integer_32, preceded(multispace0, nanosecond)),
        )(input)
    }

    fn nanosecond(input: &str) -> IResult<&str, &str> {
        context(
            "nanosecond",
            alt((tag("nanoseconds"), tag("nanosecond"), tag("ns"))),
        )(input)
    }

    fn unsigned_integer_32(input: &str) -> IResult<&str, u32> {
        context(
            "unsigned_integer_32",
            map_res(digit0, |s: &str| s.parse::<u32>()),
        )(input)
    }

    fn unsigned_integer_64(input: &str) -> IResult<&str, u64> {
        context(
            "unsigned_integer_64",
            map_res(digit0, |s: &str| s.parse::<u64>()),
        )(input)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        use nom::error::{Error, ErrorKind};
        use nom::Err;

        #[test]
        fn test_duration() {
            assert_eq!(
                duration("1 year"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 month"),
                Ok((
                    "",
                    crate::time::Duration {
                        months: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 week"),
                Ok((
                    "",
                    crate::time::Duration {
                        weeks: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 day"),
                Ok((
                    "",
                    crate::time::Duration {
                        days: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 hour"),
                Ok((
                    "",
                    crate::time::Duration {
                        hours: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 minute"),
                Ok((
                    "",
                    crate::time::Duration {
                        minutes: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 second"),
                Ok((
                    "",
                    crate::time::Duration {
                        seconds: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 millisecond"),
                Ok((
                    "",
                    crate::time::Duration {
                        milliseconds: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 nanosecond"),
                Ok((
                    "",
                    crate::time::Duration {
                        nanoseconds: Some(1),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year 2 months"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year and 2 months"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        minutes: Some(6),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        minutes: Some(6),
                        seconds: Some(7),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        minutes: Some(6),
                        seconds: Some(7),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds and 8 milliseconds"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        minutes: Some(6),
                        seconds: Some(7),
                        milliseconds: Some(8),
                        ..Default::default()
                    }
                ))
            );

            assert_eq!(
                duration("1 year, 2 months, 3 weeks, 4 days, 5 hours, 6 minutes, 7 seconds, 8 milliseconds and 9 nanoseconds"),
                Ok((
                    "",
                    crate::time::Duration {
                        years: Some(1),
                        months: Some(2),
                        weeks: Some(3),
                        days: Some(4),
                        hours: Some(5),
                        minutes: Some(6),
                        seconds: Some(7),
                        milliseconds: Some(8),
                        nanoseconds: Some(9),
                    }
                ))
            );
        }

        #[test]
        fn test_years() {
            assert_eq!(years("2 years"), Ok(("", 2)));
            assert_eq!(years("2 year"), Ok(("", 2)));
            assert_eq!(years("2years"), Ok(("", 2)));
            assert_eq!(years("2year"), Ok(("", 2)));
            assert_eq!(years("2 y"), Ok(("", 2)));
            assert_eq!(years("2y"), Ok(("", 2)));
        }

        #[test]
        fn test_year() {
            assert_eq!(year("years"), Ok(("", "years")));
            assert_eq!(year("year"), Ok(("", "year")));
            assert_eq!(year("y"), Ok(("", "y")));
        }

        #[test]
        fn test_months() {
            assert_eq!(months("2 months"), Ok(("", 2)));
            assert_eq!(months("2 month"), Ok(("", 2)));
            assert_eq!(months("2months"), Ok(("", 2)));
            assert_eq!(months("2month"), Ok(("", 2)));
            assert_eq!(months("2 mo"), Ok(("", 2)));
            assert_eq!(months("2mo"), Ok(("", 2)));
        }

        #[test]
        fn test_month() {
            assert_eq!(month("months"), Ok(("", "months")));
            assert_eq!(month("month"), Ok(("", "month")));
            assert_eq!(month("mo"), Ok(("", "mo")));
        }

        #[test]
        fn test_weeks() {
            assert_eq!(weeks("2 weeks"), Ok(("", 2)));
            assert_eq!(weeks("2 week"), Ok(("", 2)));
            assert_eq!(weeks("2weeks"), Ok(("", 2)));
            assert_eq!(weeks("2week"), Ok(("", 2)));
            assert_eq!(weeks("2 w"), Ok(("", 2)));
            assert_eq!(weeks("2w"), Ok(("", 2)));
        }

        #[test]
        fn test_week() {
            assert_eq!(week("weeks"), Ok(("", "weeks")));
            assert_eq!(week("week"), Ok(("", "week")));
            assert_eq!(week("w"), Ok(("", "w")));
        }

        #[test]
        fn test_days() {
            assert_eq!(days("2 days"), Ok(("", 2)));
            assert_eq!(days("2 day"), Ok(("", 2)));
            assert_eq!(days("2days"), Ok(("", 2)));
            assert_eq!(days("2day"), Ok(("", 2)));
            assert_eq!(days("2 d"), Ok(("", 2)));
            assert_eq!(days("2d"), Ok(("", 2)));
        }

        #[test]
        fn test_day() {
            assert_eq!(day("days"), Ok(("", "days")));
            assert_eq!(day("day"), Ok(("", "day")));
            assert_eq!(day("d"), Ok(("", "d")));
        }

        #[test]
        fn test_hours() {
            assert_eq!(hours("2 hours"), Ok(("", 2)));
            assert_eq!(hours("2 hour"), Ok(("", 2)));
            assert_eq!(hours("2hours"), Ok(("", 2)));
            assert_eq!(hours("2hour"), Ok(("", 2)));
            assert_eq!(hours("2 h"), Ok(("", 2)));
            assert_eq!(hours("2h"), Ok(("", 2)));
        }

        #[test]
        fn test_hour() {
            assert_eq!(hour("hours"), Ok(("", "hours")));
            assert_eq!(hour("hour"), Ok(("", "hour")));
            assert_eq!(hour("h"), Ok(("", "h")));
        }

        #[test]
        fn test_minutes() {
            assert_eq!(minutes("2 minutes"), Ok(("", 2)));
            assert_eq!(minutes("1 minute"), Ok(("", 1)));
            assert_eq!(minutes("2minutes"), Ok(("", 2)));
            assert_eq!(minutes("1minute"), Ok(("", 1)));
            assert_eq!(minutes("2 mins"), Ok(("", 2)));
            assert_eq!(minutes("1 min"), Ok(("", 1)));
            assert_eq!(minutes("2mins"), Ok(("", 2)));
            assert_eq!(minutes("1min"), Ok(("", 1)));
        }

        #[test]
        fn test_minute() {
            assert_eq!(minute("minutes"), Ok(("", "minutes")));
            assert_eq!(minute("minute"), Ok(("", "minute")));
            assert_eq!(minute("mins"), Ok(("", "mins")));
            assert_eq!(minute("min"), Ok(("", "min")));
        }

        #[test]
        fn test_seconds() {
            assert_eq!(seconds("2 seconds"), Ok(("", 2)));
            assert_eq!(seconds("1 second"), Ok(("", 1)));
            assert_eq!(seconds("2seconds"), Ok(("", 2)));
            assert_eq!(seconds("1second"), Ok(("", 1)));
            assert_eq!(seconds("2 secs"), Ok(("", 2)));
            assert_eq!(seconds("1 sec"), Ok(("", 1)));
            assert_eq!(seconds("2secs"), Ok(("", 2)));
            assert_eq!(seconds("1sec"), Ok(("", 1)));
            assert_eq!(seconds("1 s"), Ok(("", 1)));
            assert_eq!(seconds("1s"), Ok(("", 1)));
        }

        #[test]
        fn test_second() {
            assert_eq!(second("seconds"), Ok(("", "seconds")));
            assert_eq!(second("second"), Ok(("", "second")));
            assert_eq!(second("secs"), Ok(("", "secs")));
            assert_eq!(second("sec"), Ok(("", "sec")));
            assert_eq!(second("s"), Ok(("", "s")));
        }

        #[test]
        fn test_milliseconds() {
            assert_eq!(milliseconds("2 milliseconds"), Ok(("", 2)));
            assert_eq!(milliseconds("1 millisecond"), Ok(("", 1)));
            assert_eq!(milliseconds("1 ms"), Ok(("", 1)));

            assert_eq!(milliseconds("2milliseconds"), Ok(("", 2)));
            assert_eq!(milliseconds("1millisecond"), Ok(("", 1)));
            assert_eq!(milliseconds("1ms"), Ok(("", 1)));
        }

        #[test]
        fn test_millisecond() {
            assert_eq!(millisecond("milliseconds"), Ok(("", "milliseconds")));
            assert_eq!(millisecond("millisecond"), Ok(("", "millisecond")));
            assert_eq!(millisecond("ms"), Ok(("", "ms")));
        }

        #[test]
        fn test_nanoseconds() {
            assert_eq!(nanoseconds("2 nanoseconds"), Ok(("", 2)));
            assert_eq!(nanoseconds("1 nanosecond"), Ok(("", 1)));
            assert_eq!(nanoseconds("1 ns"), Ok(("", 1)));

            assert_eq!(nanoseconds("2nanoseconds"), Ok(("", 2)));
            assert_eq!(nanoseconds("1nanosecond"), Ok(("", 1)));
            assert_eq!(nanoseconds("1ns"), Ok(("", 1)));
        }

        #[test]
        fn test_nanosecond() {
            assert_eq!(nanosecond("nanoseconds"), Ok(("", "nanoseconds")));
            assert_eq!(nanosecond("nanosecond"), Ok(("", "nanosecond")));
            assert_eq!(nanosecond("ns"), Ok(("", "ns")));
        }

        #[test]
        fn test_u64() {
            assert_eq!(unsigned_integer_64("0"), Ok(("", 0)));
            assert_eq!(unsigned_integer_64("1"), Ok(("", 1)));
            assert_eq!(
                unsigned_integer_64("18446744073709551615"),
                Ok(("", 18_446_744_073_709_551_615))
            );

            assert_eq!(
                unsigned_integer_64("18446744073709551616"),
                Err(Err::Error(Error::new(
                    "18446744073709551616",
                    ErrorKind::MapRes
                )))
            );
        }
    }
}
