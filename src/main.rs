//! DUR (Default UArc Runner), an implementation of the UArc specification.
//! 
//! A interpreter and linker for UArc executables.
//! 
//! It aims to:
//! * Be well-rounded and suitable for standard usage.
//! * Be no-libstd and dependency-free.
//! * Leverage as less libcore internals (implementation details) as possible.
//! * Be portable; being able to be run on popular Unix-like OSes.
//! * Be as fast as possible without generating machine code,
//!   meaning that it won't abstract upon memory, syscalls, etc.
//! 
//! ## Optional Goals:
//! * Be able to be run as a freestanding executable.
//! * Hot Code Reloading
//! 
//! This root module will also contain code to load the executable

#![no_std]
#![no_main]

mod stdio;
mod syscall;
mod wrappers;
mod utils;

use core::{
    arch::asm,
    mem::MaybeUninit,
    panic::PanicInfo,
};
use wrappers::*;
use syscall::sys_ret;
use utils::*;

#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    eprintln!("{}", info);
    unsafe { syscall!(0, 101) };
    loop {}
}

// TODO: Make start logic platform independent (Works on x86_64 macOS & linux? only)
#[doc(hidden)]
#[unsafe(no_mangle)]
pub extern "C" fn _start() {
    unsafe { asm!("mov rdi, rsp", "call {entry}", entry = sym __start) };
}

// ANSI escape codes for formatting status messages
//const BOLD: &str = "\x1B[1m";
const ERR: &str = "[dur] \x1B[1;31merror\x1B[39m:";
const NORM: &str = "\x1B[m";

// The UArc magic number
const MAGIC: u64 = 0x7f__415243__00__00_01_00;

// The proxy entrypoint
#[inline]
pub unsafe extern "C" fn __start(stack_top: *const u8) -> ! {
    // Setup command line arguments on the stack for executable (and loader)
    let argc = unsafe { *(stack_top.add(8) as *const u64) };
    let argv = unsafe { stack_top.add(16) as *const *const u8 };
    let envp = unsafe { stack_top.add(24 + (argc as usize) * 8) as *const *const u8 };

    println!("argc: {argc}");

    if argc < 2 {
        eprintln!("{ERR} no input file given{NORM}");
        unsafe { syscall!(0, 22) };
    }

    // Open executable
    let input = unsafe { *argv.add(1) };

    print!("exec: ");
    unsafe { syscall!(2, 1, input, strlen(input)) }; println!();

    let fd = unsafe {
        match sys_ret(open(input, 0)) {
            Ok(fd) => fd as i32,
            Err(errno) => {
                eprintln!("{ERR} failed to open `{}`{NORM}", mkstr(input));
                syscall!(0, errno) as _
            },
        }
    };

    // Load executable
    let mut stat = MaybeUninit::<stat>::zeroed();
    unsafe { syscall!(4, fd, &raw mut stat) };
    let stat = unsafe { stat.assume_init() };

    // DEBUG STAT
    /*
    for (i, b) in stat.0.iter().enumerate() {
        println!("{}: {}", i, b);
    }
    */
    
    println!("size: {}", stat.st_size);
    
    const PROT_READ: i32 = 1;
    const MAP_SHARED: i32 = 1;
    unsafe {
        CP = match sys_ret(
            mmap(ptr::null(), stat.st_size as _, PROT_READ, MAP_SHARED, fd, 0)
        ) {
            Ok(addr) => addr as _,
            Err(errno) => {
                eprintln!("{ERR} failed to load exec `{}`{NORM}", mkstr(input));
                syscall!(0, errno) as _
            },
        };
    }
    
    // DEBUG LOADED EXECUTABLE
    println!("contents:\n```");
    unsafe { syscall!(2, 1, CP, stat.st_size) };
    println!("\n```\n");

    unsafe {
        if stat.st_size < 8
        || (*(CP as *const u64)).to_be() != MAGIC {
            eprintln!("{ERR} exec `{}` format error{NORM}", mkstr(input));
            syscall!(0, 8);
        }

        CP = CP.add(8);
        IP = CP;
    }
    
    // TEST STACK ADDRESSES
    let byte = unsafe { *IP };
    println!("stack addresses:");
    println!("{:p} <- stack_top", stack_top);
    println!("{:p} <- last local", &byte);
    println!("{:p} <- stat of exec", &stat);
    println!("{:p} <- envp", &envp);
    println!("{:p} <- argv", &argv);
    println!("{:p} <- argc", &argc);

    // Runtime!
    unsafe {
        MP = &raw const argc as _;
        FP = MP;
        // Transfer control to virtual machine
        run();
    }
}

include!("run.rs");
