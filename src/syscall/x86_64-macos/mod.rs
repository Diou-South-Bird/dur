// On x86-64, the following registers are used for args 1-6:
// arg1: %rdi
// arg2: %rsi
// arg3: %rdx
// arg4: %r10
// arg5: %r8
// arg6: %r9
//
// %rax is used for both the syscall number and the syscall return value.
//
// %rcx and %r11 are always clobbered. Syscalls can also modify memory. With the
// `asm!()` macro, it is assumed that memory is clobbered unless the nomem
// option is specified. On MacOS, on error, the carry flag (CF) in bit 0 of the
// flags register is set and %rax will contain the error code.

pub mod nr;

use core::arch::asm;

/// Issues a system call with 0 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall0(n: usize) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 1 argument.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall1(n: usize, arg1: usize) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 2 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall2(n: usize, arg1: usize, arg2: usize) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        in("rsi") arg2,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 3 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall3(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        in("rsi") arg2,
        in("rdx") arg3,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 4 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall4(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        in("rsi") arg2,
        in("rdx") arg3,
        in("r10") arg4,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 5 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall5(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        in("rsi") arg2,
        in("rdx") arg3,
        in("r10") arg4,
        in("r8")  arg5,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}

/// Issues a system call with 6 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall6(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
    arg6: usize,
) -> usize {
    let ret: usize;
    let err: usize;
    asm!(
        "syscall",
        inlateout("rax") n => ret,
        in("rdi") arg1,
        in("rsi") arg2,
        in("rdx") arg3,
        in("r10") arg4,
        in("r8")  arg5,
        in("r9")  arg6,
        out("rcx") _, // rcx is used to store old rip
        out("r11") err, // r11 is used to store old rflags
        options(nostack, preserves_flags)
    );
    if err & 1 == 0 {
        ret
    } else {
        ret.wrapping_neg()
    }
}
