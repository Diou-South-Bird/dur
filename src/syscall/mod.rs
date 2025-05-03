//! Syscalls with platform-independent signatures.

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "aarch64"))]
#[path="aarch64-linux/mod.rs"]
mod platform;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path="aarch64-macos/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "arm",
    not(target_feature = "thumb-mode")))]
#[path="arm_thumb-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "arm",
    target_feature = "thumb-mode"))]
#[path="arm-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "loongarch64"))]
#[path="loongarch64-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "mips"))]
#[path="mips-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "mips64"))]
#[path="mips64-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "powerpc"))]
#[path="powerpc-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "powerpc64"))]
#[path="powerpc64-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "riscv32"))]
#[path="riscv32-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "riscv64"))]
#[path="riscv64-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "s390x"))]
#[path="s390x-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "x86"))]
#[path="x86-linux/mod.rs"]
mod platform;

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "x86_64"))]
#[path="x86_64-linux/mod.rs"]
mod platform;

#[cfg(all(target_os = "freebsd", target_arch = "x86_64"))]
#[path="x86_64-freebsd/mod.rs"]
mod platform;

#[cfg(all(target_os = "macos", target_arch = "x86_64"))]
#[path="x86_64-macos/mod.rs"]
mod platform;

#[cfg(not(any(
    all(any(target_os = "linux", target_os = "android", target_os = "macos"),
        target_arch = "aarch64"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "arm"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "loongarch64"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "mips"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "mips64"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "powerpc"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "powerpc64"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "riscv32"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "riscv64"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "s390x"),
    all(any(target_os = "linux", target_os = "android"), target_arch = "x86"),
    all(any(target_os = "linux", target_os = "android", target_os = "freebsd", target_os = "macos"),
        target_arch = "x86_64"),
)))]
#[path="undef-undef/mod.rs"]
mod platform;

pub use platform::{*, nr::NRS};

/// Evaluates a return value from a syscall.
/// 
/// Returns either `Ok` with the return value if successful or
/// `Err` with the error number if the return value was an error.
pub fn sys_ret(val: usize) -> Result<usize, i32> {
    if val > -4096isize as usize {
        // Truncation of the error value is guaranteed to never occur due to
        // the above check. This is the same check that musl uses:
        // https://git.musl-libc.org/cgit/musl/tree/src/internal/syscall_ret.c?h=v1.1.15
        Err(-(val as i32))
    } else {
        Ok(val)
    }
}

/// Performs a syscall and returns `usize`.
/// 
/// Accepts a syscall number and a variable number of arguments (0 to 6).
#[macro_export]
macro_rules! syscall {
    ($nr:expr) => {
        $crate::syscall::syscall0($crate::syscall::NRS[$nr])
    };
    ($nr:expr, $a1:expr) => {
        $crate::syscall::syscall1($crate::syscall::NRS[$nr], $a1 as usize)
    };
    ($nr:expr, $a1:expr, $a2:expr) => {
        $crate::syscall::syscall2($crate::syscall::NRS[$nr], $a1 as usize, $a2 as usize)
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr) => {
        $crate::syscall::syscall3($crate::syscall::NRS[$nr], $a1 as usize, $a2 as usize, $a3 as usize)
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr) => {
        $crate::syscall::syscall4(
            $crate::syscall::NRS[$nr],
            $a1 as usize,
            $a2 as usize,
            $a3 as usize,
            $a4 as usize,
        )
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr, $a5:expr) => {
        $crate::syscall::syscall5(
            $crate::syscall::NRS[$nr],
            $a1 as usize,
            $a2 as usize,
            $a3 as usize,
            $a4 as usize,
            $a5 as usize,
        )
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr, $a5:expr, $a6:expr) => {
        $crate::syscall::syscall6(
            $crate::syscall::NRS[$nr],
            $a1 as usize,
            $a2 as usize,
            $a3 as usize,
            $a4 as usize,
            $a5 as usize,
            $a6 as usize,
        )
    };
}
