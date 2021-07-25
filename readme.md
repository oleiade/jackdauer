# JackDauer

![CI](https://github.com/oleiade/jackdauer/actions/workflows/main.yml/badge.svg)

Use this Rust crate to easily parse various time formats to durations.

## Demo

```rust
use dauer::duration;
use std::time::Duration;

let nanoseconds = duration("1 nanosecond");
let milliseconds = duration("2 milliseconds");
let seconds = duration("3 seconds");
let minutes = duration("4 minutes");
let hours = duration("5 hours");
let day = duration("6 days");
let week = duration("7 weeks");
let month = duration("8 months");
let year = duration("9 months");
let real_big_duration = duration("9 years, 8 months, 7 weeks and 6 days");
let real_small_duration = duration("4 minutes 3 seconds, 2 milliseconds and 1 nanosecond");
```

## Features

- The [`duration`](https://docs.rs/jackdauer/0.1.0/jackdauer/fn.duration.html) function provides straight forward functions to parse durations from a human-readable format, into std::time::Duration instances.
- The time unit specific functions return unsigned integers representing the amount of said time unit parsed from a human-readable format:
  - [`years`](fn.years.html): returns the parsed duration as an amount of years
  - [`months`](fn.months.html): returns the parsed duration as an amount of months
  - [`weeks`](fn.weeks.html): returns the parsed duration as an amount of weeks
  - [`days`](fn.days.html): returns the parsed duration as an amount of days
  - [`hours`](fn.hours.html): returns the parsed duration as an amount of hours
  - [`minutes`](fn.minutes.html): returns the parsed duration as an amount of minutes
  - [`seconds`](fn.seconds.html): returns the parsed duration as an amount of seconds
  - [`milliseconds`](fn.milliseconds.html): returns the parsed duration as an amount of years
  - [`nanoseconds`](fn.nanoseconds.html): returns the parsed duration as an amount of years

## Installation

Add it as a dependency to your `Cargo.toml`

```toml
[dependencies]
jackdauer = "0.1.0"
```

## Documentation

[Documentation]((https://docs.rs/jackdauer/0.1.0/jackdauer/)

## Authors

- [@oleiade](https://www.github.com/oleiade)

## FAQ

#### What's the name about?

"Dauer" is the German word for duration. When thinking about time, it reminded me of this show called "24", and its main character "Jack Bauer" (which, incidentally also happens to mean "builder" in German). The contraction of both gives "Jack Dauer".

#### But why the ridiculous name?

It's 2021, COVID-19 is still raging out there. The last year and a half has been quite gloomy, and I thought I needed (and you needed too; maybe you're not just aware of it) of some terrible pun to shed some light on my day to day quarantined life.

## Acknowledgements

- [This crate wouldn't have been possible without Nom, the parser combinator library](https://github.com/Geal/nom)
- [Inspiration taken from the awesome ms javascript library](https://github.com/vercel/ms#readme)
- [readme.so, a superb tool that helped me build this README](https://readme.so)

## License

[MIT](https://choosealicense.com/licenses/mit/)
