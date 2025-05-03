// SPARC uses the following registers for args 1-6:
//
// arg1: %o0
// arg2: %o1
// arg3: %o2
// arg4: %o3
// arg5: %o4
// arg6: %o5
//
// %g0 specifies the syscall number.
// %o1 is also used for the return value.
// %cc is the only clobbered register.

pub mod nr;

use core::arch::asm;

/// Issues a raw system call with 0 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall0(n: usize) -> usize {
    let ret: usize;
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("g1") n,
        lateout("%o0") => ret,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 1 argument.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall1(n: usize, arg1: usize) -> usize {
    let ret: usize;
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("g1") n,
        inlateout("%o0") arg1 => ret,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 2 arguments.
///
/// # Safety
///
/// Running a system call is inherently unsafe. It is the caller's
/// responsibility to ensure safety.
#[inline]
pub unsafe fn syscall2(n: usize, arg1: usize, arg2: usize) -> usize {
    let ret: usize;
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("%g1") n,
        inlateout("%o0") arg1 => ret,
        in("%o1") arg2,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 3 arguments.
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
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("%g1") n,
        inlateout("%o0") arg1 => ret,
        in("%o1") arg2,
        in("%o2") arg3,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 4 arguments.
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
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("%g1") n,
        inlateout("%o0") arg1 => ret,
        in("%o1") arg2,
        in("%o2") arg3,
        in("%o3") arg4,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 5 arguments.
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
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("%g1") n,
        inlateout("%o0") arg1 => ret,
        in("%o1") arg2,
        in("%o2") arg3,
        in("%o3") arg4,
        in("%o4") arg5,
        lateout("%cc") => _,
    );
    ret
}

/// Issues a raw system call with 6 arguments.
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
    arg6: usize,
) -> usize {
    let ret: usize;
    asm!(
        "t 109",
        "bcc,pt %xcc, 1f",
        "sub %g0, %o0, %o0",
        "1:",
        in("%g1") n,
        inlateout("%o0") arg1 => ret,
        in("%o1") arg2,
        in("%o2") arg3,
        in("%o3") arg4,
        in("%o4") arg5,
        in("%o5") arg6,
        lateout("%cc") => _,
    );
    ret
}
