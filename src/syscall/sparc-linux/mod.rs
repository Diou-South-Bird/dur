// Undefined or unsupported platform. No syscalls here.
use core::mem::MaybeUninit;

/// Issues a system call with 0 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall0(_n: usize) -> usize {
    MaybeUninit::uninit()
}

/// Issues a system call with 1 argument.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall1(_n: usize, _arg1: usize) -> usize {
    MaybeUninit::uninit().assume_init()
}

/// Issues a system call with 2 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall2(_n: usize, _arg1: usize, _arg2: usize) -> usize {
    MaybeUninit::uninit().assume_init()
}

/// Issues a system call with 3 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall3(
    _n: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    MaybeUninit::uninit().assume_init()
}

/// Issues a system call with 4 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall4(
    _n: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
    _arg4: usize,
) -> usize {
    MaybeUninit::uninit().assume_init()
}

/// Issues a system call with 5 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall5(
    _n: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
    _arg4: usize,
    _arg5: usize,
) -> usize {
    MaybeUninit::uninit().assume_init()
}

/// Issues a system call with 6 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall6(
    _n: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
    _arg4: usize,
    _arg5: usize,
    _arg6: usize,
) -> usize {
    MaybeUninit::uninit().assume_init()
}
