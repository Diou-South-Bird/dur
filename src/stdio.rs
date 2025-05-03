//! Implementations of the std `print`, `println`, `eprint`, and `eprintln` macros
//! for status messages.
//! 
//! ## Warning:
//! These implementations are non-blocking.

use core::fmt;
use crate::syscall;

struct StdIo(usize);

impl fmt::Write for StdIo {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        unsafe { syscall!(2, self.0, s.as_ptr(), s.len()) };
        Ok(())
    }
}

/// See std's [`print!`] for details.
/// See [`std::fmt`] for formatting.
#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ($crate::stdio::_print(format_args!($($arg)*)));
}

/// See std's [`println!`] for details.
/// See [`std::fmt`] for formatting.
#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ($crate::print!("{}\n", format_args!($($arg)*)));
}

/// See std's [`eprint!`] for details.
/// See [`std::fmt`] for formatting.
#[macro_export]
macro_rules! eprint {
    ($($arg:tt)*) => ($crate::stdio::_eprint(format_args!($($arg)*)));
}

/// See std's [`eprintln!`] for details.
/// See [`std::fmt`] for formatting.
#[macro_export]
macro_rules! eprintln {
    () => ($crate::eprint!("\n"));
    ($($arg:tt)*) => ($crate::eprint!("{}\n", format_args!($($arg)*)));
}

#[doc(hidden)]
pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    StdIo(1).write_fmt(args).unwrap();
}

#[doc(hidden)]
pub fn _eprint(args: fmt::Arguments) {
    use core::fmt::Write;
    StdIo(2).write_fmt(args).unwrap();
}
