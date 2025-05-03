//! Platform-independent syscall wrappers.

use crate::syscall;

// TODO: these items should be platform-independent
// start with Linux x86_64

// Stat structures for stat, fstat, and lstat calls

#[cfg(target_os = "macos")]
#[repr(C)]
#[allow(non_camel_case_types)]
pub struct stat {
    pub st_dev: i32,
    pub st_ino: u32, // or i32?
    pub st_mode: u16,
    pub st_nlink: u16,
    pub st_uid: u32,
    pub st_gid: u32,
    pub st_rdev: i32,
    pub st_atime: i64,
    pub st_atimensec: i64,
    pub st_mtime: i64,
    pub st_mtimensec: i64,
    pub st_ctime: i64,
    pub st_ctimensec: i64,
    pub st_size: i64,
    pub st_blocks: i64,
    pub st_blksize: i32,
    pub st_flags: u32,
    pub st_gen: u32,
    pub st_lspare: i32,
    pub st_qspare: [i64; 2],
}

#[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "powerpc64")))]
#[repr(C)]
#[allow(non_camel_case_types)]
pub struct stat {
    pub st_dev: u64,
    pub st_ino: u64,
    pub st_nlink: u64,
    pub st_mode: u32,
    pub st_uid: u32,
    pub st_gid: u32,
    pub __pad0: i32,
    pub st_rdev: u64,
    pub st_size: i64,
    pub st_blksize: i64,
    pub st_blocks: i64,
    pub st_atime: i64,
    pub st_atimensec: i64,
    pub st_mtime: i64,
    pub st_mtimensec: i64,
    pub st_ctime: i64,
    pub st_ctimensec: i64,
    pub __unused: [i64; 3],
}

//pub struct Test(pub [u8; core::mem::size_of::<stat>()]);

#[cfg(all(any(target_os = "linux", target_os = "android"), target_arch = "arm"))]
pub unsafe fn mmap(
    addr: *const (),
    len: usize,
    prot: i32,
    flags: i32,
    fd: i32,
    offset: u64,
) -> usize {
    unsafe { syscall!(381, addr, len, prot, flags, fd, (offset / 4096) + (offset != 0) as u64) } // TODO page sizes for different architectures
}

#[cfg(not(all(any(target_os = "linux", target_os = "android"), target_arch = "arm")))]
pub unsafe fn mmap(
    addr: *const (),
    len: usize,
    prot: i32,
    flags: i32,
    fd: i32,
    offset: u64,
) -> usize {
    unsafe { syscall!(121, addr, len, prot, flags, fd, offset) }
}

#[cfg(all(any(target_os = "linux", target_os = "android"),
    any(target_arch = "aarch64", target_arch = "loongarch64",
    target_arch = "riscv32", target_arch = "riscv64")))]
pub unsafe fn open(path: *const u8, flags: i32) -> usize {
    const AT_FDCWD: i32 = -100;
    unsafe { syscall!(246, AT_FDCWD, path, flags, 0) }
}

#[cfg(not(all(any(target_os = "linux", target_os = "android"),
    any(target_arch = "aarch64", target_arch = "loongarch64",
    target_arch = "riscv32", target_arch = "riscv64"))))]
pub unsafe fn open(path: *const u8, flags: i32) -> usize {
    unsafe { syscall!(94, path, flags, 0) }
}
