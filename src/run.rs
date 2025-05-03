use core::{
    hint,
    ptr,
};

// DEBUG
use core::fmt;

// Registers
static mut A0: u64 = 0;
static mut A1: u64 = 0;
static mut A2: u64 = 0;
static mut A3: u64 = 0;
static mut A4: u64 = 0;
static mut A5: u64 = 0;
/// Memory pointer.
static mut MP: u64 = 0;
/// Memory frame pointer.
static mut FP: u64 = 0;
/// Link register.
static mut LX: u64 = 0;
/// Syscall number and syscall return value.
static mut RX: u64 = 0;

// Hidden Registers
/// Code pointer.
static mut CP: *const u8 = ptr::null();
/// Instruction pointer.
static mut IP: *const u8 = ptr::null();

/// Status register.
/// 
/// ## Bits
/// `0` - OF overflow
/// 
/// `1` - CF carry
/// 
/// `2..3` - ORD ordering `0b00` - eq, `0b01` - gt, `0b11` - lt)
static mut ST: u8 = 0;

#[allow(non_snake_case)]
fn OF() -> u8 {
    unsafe { ST & 0b1 }
}

#[allow(non_snake_case)]
fn CF() -> u8 {
    unsafe { (ST >> 1) & 0b1 }
}

#[allow(non_snake_case)]
fn ORD() -> u8 {
    unsafe { (ST >> 2) & 0b11 }
}

#[inline]
fn sigill() -> ! {
    println!("\n[dur_sigill] => {:p}", unsafe { IP });

    unsafe { 
        let pid = syscall!(7); // `getpid` is always successful
        sys_ret(syscall!(14, pid, 4)).unwrap();
    }

    loop {}
}

#[inline]
fn arg_fields(arg: u8) -> (u8, *mut u64) {
    let mem = arg & 0b1;
    let reg = (arg >> 1) & 0b1111; // 0b1111111
    let reg = match reg {
        0 => &raw mut A0, 1 => &raw mut A1,
        2 => &raw mut A2, 3 => &raw mut A3,
        4 => &raw mut A4, 5 => &raw mut A5,
        6 => &raw mut MP, 7 => &raw mut FP,
        8 => &raw mut LX, 9 => &raw mut RX,
        _ => sigill(),
    };

    (mem, reg)
}

/// # Safety
/// 
/// Caller must ensure that the mem bit of `arg` is 1.
#[inline]
unsafe fn arg_offset(arg: u32) -> isize { // i32 not u32
    ((arg as i32) << 6 >> 11) as isize // >> 8 not << 6 >> 11
}

/// # DEBUG
fn reg_info() {
    const PURP: &str = "\x1B[95m";
    const GREN: &str = "\x1B[92m";
    const CYAN: &str = "\x1B[96m";
    const YELW: &str = "\x1B[93m";

    unsafe {
        println!();

        println!(
            "{PURP}{:p}{NORM} <{PURP}+{}{NORM}>: {GREN}0x{:02x}{NORM}",
            IP as *const u8,
            IP as usize - CP as usize,
            *IP,
        );

        println!(
            "    ({CYAN}OF={YELW}0b{:b}{NORM}, {CYAN}CF={YELW}?{NORM}, {CYAN}ORD={YELW}0b{:02b}{NORM})",
            ST & 0b1,
            (ST >> 2) & 0b11,
        );

        println!(
            "    ({CYAN}q0{NORM}={YELW}{:x}{NORM}, {CYAN}q1{NORM}={YELW}{:x}{NORM}, {CYAN}q2{NORM}={YELW}{:x}{NORM}, {CYAN}q3{NORM}={YELW}{:x}{NORM}, {CYAN}q4{NORM}={YELW}{:x}{NORM})",
            A0 as u64,
            A1 as u64,
            A2 as u64,
            A3 as u64,
            A4 as u64,
        );

        println!(
            "    ({CYAN}q5{NORM}={YELW}{:x}{NORM}, {CYAN}q6{NORM}={YELW}{:x}{NORM}, {CYAN}q7{NORM}={YELW}{:x}{NORM}, {CYAN}q8{NORM}={YELW}{:x}{NORM}, {CYAN}q9{NORM}={YELW}{:x}{NORM})",
            A5 as u64,
            MP as u64,
            FP as u64,
            LX as u64,
            RX as u64,
        );

        println!(
            "    ({CYAN}[q6]{NORM}={YELW}{}{NORM}, {CYAN}[q7]{NORM}={YELW}{}{NORM})\n",
            (MP as *const u64).read_unaligned(),
            (FP as *const u64).read_unaligned(),
        );
    }
}

/*
/// Ends the current instruction.
/// 
/// Also takes an additional argument `f` which will take the instruction counter address
/// one byte after the end of the current instruction argument.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn end(ic: *const u8) {
    unsafe { IP = ic };
}

/// Identity function: ends the current instruction and delegates a value.
/// 
/// Also takes an additional argument `f` which will take the instruction counter address
/// one byte after the end of the current instruction argument.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn val<T>(ic: *const u8, val: T) -> T {
    unsafe { IP = ic };
    val
}
*/

/*
/// Takes an immediate at the instruction counter and ends the current instruction.
/// 
/// Also takes an additional argument `f` which will take the instruction counter address
/// one byte after the end of the current instruction argument.
/// 
/// Used in [`ins!`].
/// 
/// ## TODO
/// This may not work on big-endian platforms.
#[inline]
unsafe fn imm<T: ToLe + fmt::LowerHex>(ic: *const u8) -> T {
    let ret = unsafe {
        IP = ic.add(size_of::<T>());
        (ic as *const T).read_unaligned().to_le()
    };

    println!("[load immediate] {:x}", ret);

    ret
}
*/

/// Takes an immediate relative to the current instruction.
/// 
/// Used in [`ins!`].
/// 
/// ## TODO
/// This may not work on big-endian platforms.
#[inline]
unsafe fn imm<T: ToLe + fmt::LowerHex>() -> T {
    for i in 0..=(core::mem::size_of::<T>() - 1) {
        println!("{:?}", unsafe { *IP.add(8 + i) } as char);
    }
    println!("[debug:immediate_addr] {:p}", unsafe { IP.add(8) });
    println!("[debug:immediate_off] {}", unsafe { IP.add(8) as usize - CP as usize });
    println!("[debug:size] {}", core::mem::size_of::<T>());
    let ret2 = unsafe { (IP.add(8) as *const u128).read_unaligned().to_le() };
    println!("_ {:x}", ret2);
    let ret = unsafe { (IP.add(8) as *const T).read_unaligned().to_le() };
    println!("[load immediate] {:x}", ret);
    ret
}

/*
/// Write to an address specified by the instruction argument at the instruction counter.
/// 
/// Also takes an additional argument `f` which will take the instruction counter address
/// one byte after the end of the current instruction argument. `f` is ran to get the value
/// to write.
/// 
/// # Safety
/// 
/// See [`std::ptr::write()`] when writing to a register and [`std::ptr::write_unaligned()`]
/// when writing to other memory regions.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn write<T: fmt::Display>(ic: *const u8, mut f: impl FnMut(*const u8) -> T) {
    let (mem, dst) = unsafe { arg_fields(*ic) };

    if mem == 0 {
        if size_of::<T>() == 16 { sigill(); }
        unsafe { (dst as *mut T).write(f(ic.add(1))) };
        println!("[write to register]");
    } else {
        unsafe {
            let offset = arg_offset((ic as *const i32).read_unaligned());
            (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset).write_unaligned(f(ic.add(4)));

            let ptr = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset);
            println!("[write to memory]");
            println!("| [write offset] {}", offset);
            println!("| [write address] => {:p}", ptr);
        }
    }
}
*/

/// Writes `val` to an address specified by the register argument `arg`.
/// 
/// # Safety
/// 
/// See [`std::ptr::write()`] when writing to a register and [`std::ptr::write_unaligned()`]
/// when writing to other memory regions.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn write<T: fmt::Display>(arg: u32, val: T) {
    let (mem, dst) = arg_fields(arg as u8);

    if mem == 0 {
        if size_of::<T>() == 16 { sigill(); }
        unsafe { (dst as *mut T).write(val) };
        println!("[write to register]");
    } else {
        unsafe {
            let offset = arg_offset(arg);
            (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset).write_unaligned(val);

            let ptr = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset);
            println!("[write to memory]");
            println!("| [write offset] {}", offset);
            println!("| [write address] => {:p}", ptr);
        }
    }
}

/*
/// Read from an address specified by the instruction argument at the instruction counter.
/// 
/// Also takes an additional argument `f` which will take the instruction counter address
/// one byte after the end of the current instruction argument. `f` is run after the address
/// is read and gets the second value of the binary return.
/// 
/// # Safety
/// 
/// See [`std::ptr::read()`] when reading from a register and [`std::ptr::read_unaligned()`]
/// when reading from other memory regions.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn read<T: fmt::LowerHex, U>(ic: *const u8, mut f: impl FnMut(*const u8) -> U) -> (T, U) {
    let (mem, dst) = unsafe { arg_fields(*ic) };

    if mem == 0 {
        if size_of::<T>() == 16 { sigill(); }
        let ret = unsafe { ((dst as *mut T).read(), f(ic.add(1))) };
        println!("[read from register] {:x}", ret.0);
        ret
    } else {
        unsafe {
            let offset = arg_offset((ic as *const i32).read_unaligned());
            let lhs = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset).read_unaligned();
            let rhs = f(ic.add(4));

            let ptr = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset);
            println!("[read from memory] {:x}", lhs);
            println!("| [read offset] {:x}", offset);
            println!("| [read address] => {:p}", ptr);

            (lhs, rhs)
        }
    }
}
*/

/// Reads a value from an address specified by the register argument.
/// 
/// # Safety
/// 
/// See [`std::ptr::read()`] when reading from a register and [`std::ptr::read_unaligned()`]
/// when reading from other memory regions.
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn read<T: fmt::LowerHex>(arg: u32) -> T {
    let (mem, dst) = arg_fields(arg as u8);

    if mem == 0 {
        if size_of::<T>() == 16 { sigill(); }
        let ret = unsafe { (dst as *mut T).read() };
        println!("[read from register] {:x}", ret);
        ret
    } else {
        unsafe {
            let offset = arg_offset(arg);
            let ret = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset).read_unaligned();

            let ptr = (dst.read() as usize as *mut T)
                .wrapping_byte_offset(offset);
            println!("[read from memory] {:x}", ret);
            println!("| [read offset] {:x}", offset);
            println!("| [read address] => {:p}", ptr);

            ret
        }
    }
}

/*
/// Swaps the values of two addresses specified by the instruction argument at the
/// instruction counter and the instruction argument returned by `f`.
/// 
/// `f` is ran before the swap to get the second instruction argument for the swap
/// operation.
/// 
/// # Safety
/// 
/// See [`std::ptr::swap()`].
/// 
/// Used in [`ins!`].
#[inline]
unsafe fn swap<T>(ic: *const u8, mut f: impl FnMut(*const u8) -> *const u8) {
    let (mem, dst) = unsafe { arg_fields(*ic) };

    let (dst, ic) = if mem == 0 {
        if size_of::<T>() == 16 { sigill(); }
        unsafe { (dst as *mut T, f(ic.add(1))) }
    } else {
        unsafe {
            let offset = arg_offset((ic as *const i32).read_unaligned());
            ((dst.read() as usize as *mut T)
                .byte_offset(offset), f(ic.add(4)))
        }
    };

    let (mem2, src) = unsafe { arg_fields(*ic) };

    // TODO: write & read unaligned
    if mem2 == 0 {
        if size_of::<T>() == 16 { sigill(); }
        let src = src as *mut T;
        unsafe {
            let tmp = dst.read();
            dst.write(src.read());
            src.write(tmp);
        }
    } else {
        unsafe {
            let offset = arg_offset((ic as *const i32).read_unaligned());
            let src = (src.read() as usize as *mut T)
                .byte_offset(offset);
            let tmp = dst.read();
            dst.write(src.read());
            src.write(tmp);
        }
    }
}
*/

/// Convience method to generate generic instruction logic on *unsigned* words.
macro_rules! ins {
    (|$typ:ident, $arg1:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let ins = (IP as *const u64).read_unaligned();
        let size = (ins >> 8) as u8 & 0b1111;
        let $arg1 = (ins >> 12) as u32 & REG_MASK;

        ins!(@BODY size, $typ, $($exp)*);
    }};
    (|$typ:ident, $arg1:ident, $arg2:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let ins = (IP as *const u64).read_unaligned();
        let size = (ins >> 8) as u8 & 0b1111;
        let $arg1 = (ins >> 12) as u32 & REG_MASK;
        let $arg2 = (ins >> 38) as u32 & REG_MASK;

        ins!(@BODY size, $typ, $($exp)*);
    }};
    (@I |$typ:ident, $arg1:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let ins = (IP as *const u64).read_unaligned();
        let size = (ins >> 8) as u8 & 0b1111;
        let $arg1 = (ins >> 12) as u32 & REG_MASK;

        ins!(@I @BODY size, $typ, $($exp)*);
    }};
    (@I |$typ:ident, $arg1:ident, $arg2:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let ins = (IP as *const u64).read_unaligned();
        let size = (ins >> 8) as u8 & 0b1111;
        let $arg1 = (ins >> 12) as u32 & REG_MASK;
        let $arg2 = (ins >> 38) as u32 & REG_MASK;

        ins!(@I @BODY size, $typ, $($exp)*);
    }};
    (@BODY $size:ident, $typ:ident, $($exp:tt)*) => {{
        match $size {
            0 => {
                type $typ = u8;
                $($exp)*
            },
            1 => {
                type $typ = u16;
                $($exp)*
            },
            2 => {
                type $typ = u32;
                $($exp)*
            },
            3 => {
                type $typ = u64;
                $($exp)*
            },
            4 => {
                type $typ = u128;
                $($exp)*
            },
            _ => sigill(),
        }
        IP = IP.add(8);
    }};
    (@I @BODY $size:ident, $typ:ident, $($exp:tt)*) => {{
        match $size {
            0 => {
                type $typ = u8;
                { $($exp)* }
                IP = IP.add(9);
            },
            1 => {
                type $typ = u16;
                { $($exp)* }
                IP = IP.add(10);
            },
            2 => {
                type $typ = u32;
                { $($exp)* }
                IP = IP.add(12);
            },
            3 => {
                type $typ = u64;
                { $($exp)* }
                IP = IP.add(16);
            },
            4 => {
                type $typ = u128;
                { $($exp)* }
                IP = IP.add(24);
            },
            _ => sigill(),
        }
    }};
}

/// Convience method to generate generic instruction logic that operates on *signed* words.
macro_rules! sins {
    (|$typ:ident, $arg1:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let args = (IP as *const u64).read_unaligned();
        let size = (args >> 8) as u8 & 0b1111;
        let $arg1 = (args >> 12) as u32 & REG_MASK;

        ins!(@BODY size, $typ, $($exp)*);
    }};
    (|$typ:ident, $arg1:ident, $arg2:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let args = (IP as *const u64).read_unaligned();
        let size = (args >> 8) as u8 & 0b1111;
        let $arg1 = (args >> 12) as u32 & REG_MASK;
        let $arg2 = (args >> 38) as u32 & REG_MASK;

        ins!(@BODY size, $typ, $($exp)*);
    }};
    (@I |$typ:ident, $arg1:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let args = (IP as *const u64).read_unaligned();
        let size = (args >> 8) as u8 & 0b1111;
        let $arg1 = (args >> 12) as u32 & REG_MASK;

        ins!(@I @BODY size, $typ, $($exp)*);
        println!("??");
    }};
    (@I |$typ:ident, $arg1:ident, $arg2:ident| $($exp:tt)*) => {{
        reg_info();

        const REG_MASK: u32 = !(0b111111 << 26);
        let args = (IP as *const u64).read_unaligned();
        let size = (args >> 8) as u8 & 0b1111;
        let $arg1 = (args >> 12) as u32 & REG_MASK;
        let $arg2 = (args >> 38) as u32 & REG_MASK;

        ins!(@I @BODY size, $typ, $($exp)*);
    }};
    (@BODY $size:ident, $typ:ident, $($exp:tt)*) => {{
        match $size {
            0 => {
                type $typ = i8;
                $($exp)*
            },
            1 => {
                type $typ = i16;
                $($exp)*
            },
            2 => {
                type $typ = i32;
                $($exp)*
            },
            3 => {
                type $typ = i64;
                $($exp)*
            },
            4 => {
                type $typ = i128;
                $($exp)*
            },
            _ => sigill(),
        }
        IP = IP.add(8);
    }};
    (@I @BODY $size:ident, $typ:ident, $($exp:tt)*) => {{
        match $size {
            0 => {
                type $typ = i8;
                { $($exp)* }
                IP = IP.add(9);
            },
            1 => {
                type $typ = i16;
                { $($exp)* }
                IP = IP.add(10);
            },
            2 => {
                type $typ = i32;
                { $($exp)* }
                IP = IP.add(12);
            },
            3 => {
                type $typ = i64;
                { $($exp)* }
                IP = IP.add(16);
            },
            4 => {
                type $typ = i128;
                { $($exp)* }
                IP = IP.add(24);
            },
            _ => sigill(),
        }
    }};
}

/// Convience method to generate *rmw binary* operator logic.
macro_rules! rmw_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, lhs, rhs| write::<T>(lhs, read::<T>(lhs).$op(read::<T>(rhs))))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(@I |T, lhs| write::<T>(lhs, read::<T>(lhs).$op(imm::<T>())))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, lhs, rhs| write::<T>(lhs, read::<T>(lhs).$op(read::<T>(rhs))))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(@I |T, lhs| write::<T>(lhs, read::<T>(lhs).$op(imm::<T>())))
        }
    };
    ($op:tt) => {
        unsafe {
            ins!(|T, lhs, rhs| write::<T>(lhs, read::<T>(lhs) $op read::<T>(rhs)))
        }
    };
    (@I $op:tt) => {
        unsafe {
            ins!(@I |T, lhs| write::<T>(lhs, read::<T>(lhs) $op imm::<T>()))
        }
    };
}

/// Convience method to generate *rmw binary* operator logic that may *overflow*.
macro_rules! ovrflw_rmw_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, lhs, rhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(read::<T>(rhs));
                ST |= ov as u8;
                res
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(@I |T, lhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(imm::<T>());
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, lhs, rhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(read::<T>(rhs));
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(@I |T, lhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(imm::<T>());
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *binary* operator logic.
macro_rules! binop {
    ($op:ident) => {unsafe { ins!(|T, dst, src| write::<T>(dst, read::<T>(src).$op())) }};
    (@S $op:ident) => {unsafe { sins!(|T, dst, src| write::<T>(dst, read::<T>(src).$op())) }};
    ($op:tt) => {unsafe { ins!(|T, dst, src| write::<T>(dst, $op read::<T>(src))) }};
    (@S $op:tt) => {unsafe { sins!(|T, dst, src| write::<T>(dst, $op read::<T>(src))) }};
}

/// Convience method to generate *binary* operator logic that may *overflow*.
macro_rules! ovrflw_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, dst, src| write::<T>(dst, {
                let (res, ov) = read::<T>(src).$op();
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, dst, src| write::<T>(dst, {
                let (res, ov) = read::<T>(src).$op();
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *binary shift* operator logic.
macro_rules! sh_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, lhs, rhs| write::<T>(lhs, read::<T>(lhs).$op(read::<u32>(rhs))))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(@I |T, lhs| write::<T>(lhs, read::<T>(lhs).$op(imm::<u32>())))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, lhs, rhs| write::<T>(lhs, read::<T>(lhs).$op(read::<u32>(rhs))))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(@I |T, lhs| write::<T>(lhs, read::<T>(lhs).$op(imm::<u32>())))
        }
    };
}

/// Convience method to generate *binary shift* operator logic that may overflow.
macro_rules! ovrflw_sh_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, lhs, rhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(read::<u32>(rhs));
                ST |= ov as u8;
                res
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(@I |T, lhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(imm::<u32>());
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, lhs, rhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(read::<u32>(rhs));
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(@I |T, lhs| write::<T>(lhs, {
                let (res, ov) = read::<T>(lhs).$op(imm::<u32>());
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *"counting-bits" binary* operator logic.
macro_rules! cnt_binop {
    ($op:ident) => {unsafe { ins!(|T, dst, src| write::<u32>(dst, read::<T>(src).$op())) }};
    (@S $op:ident) => {unsafe { sins!(|T, dst, src| write::<u32>(dst, read::<T>(src).$op())) }};
}

/// Convience method to generate *comparison binary* operator logic.
macro_rules! cmp_binop {
    () => {
        unsafe {
            ins!(|T, lhs, rhs| {
                let res = read::<T>(lhs).cmp(&read::<T>(rhs));
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@I) => {
        unsafe {
            ins!(@I |T, lhs| {
                let res = read::<T>(lhs).cmp(&imm::<T>());
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@S) => {
        unsafe {
            sins!(|T, lhs, rhs| {
                let res = read::<T>(lhs).cmp(&read::<T>(rhs));
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@S @I) => {
        unsafe {
            sins!(@I |T, lhs| {
                let res = read::<T>(lhs).cmp(&imm::<T>());
                ST &= 0b11;
                ST |= (res as u8) << 2;
                println!("?");
            })
        }
    };
}

macro_rules! j_unop {
    ($cond:expr) => {
        unsafe {
            reg_info();

            let lhs = imm::<u32>();

            if $cond {
                let addr = (lhs as i32) << 1 >> 1;

                if lhs >> 31 == 0b1 {
                    IP = IP.offset(addr as isize);
                    println!("[jump to immediate relative IP]");
                    println!("[jump offset] {:x}", addr as isize);
                    println!("[jump address] => {:p}", { IP });
                } else {
                    IP = CP.add(addr as usize);
                    println!("[jump to immediate relative CP]");
                    println!("[jump offset] {:x}", addr as usize);
                    println!("[jump address] => {:p}", { IP });
                }
            } else {
                IP = IP.add(12);
            }
        }
    };
    (@R $cond:expr) => {
        unsafe {
            reg_info();

            const REG_MASK: u32 = !(0b111111 << 26);
            let args = (IP as *const u64).read_unaligned();
            let lhs = (args >> 12) as u32 & REG_MASK;

            if $cond {
                IP = CP.add(read::<u32>(lhs) as usize);
                let off = read::<u32>(lhs) as usize;
                println!("[jump to register]");
                println!("[jump offset] {:x}", off);
                println!("[jump address] => {:p}", { IP });
            } else {
                IP = IP.add(8);
            }
        }
    };
    (@L $cond:expr) => {
        unsafe {
            reg_info();

            let lhs = imm::<u32>();
            LX = IP as _;

            if $cond {
                let addr = (lhs as i32) << 1 >> 1;

                if lhs >> 31 == 0b1 {
                    IP = IP.offset(addr as isize);
                    println!("[jump to immediate relative IP]");
                    println!("[jump offset] {:x}", addr as isize);
                    println!("[jump address] => {:p}", { IP });
                } else {
                    IP = CP.add(addr as usize);
                    println!("[jump to immediate relative CP]");
                    println!("[jump offset] {:x}", addr as usize);
                    println!("[jump address] => {:p}", { IP });
                }
            } else {
                IP = IP.add(12);
            }
        }
    };
    (@R @L $cond:expr) => {
        unsafe {
            reg_info();

            const REG_MASK: u32 = !(0b111111 << 26);
            let args = (IP as *const u64).read_unaligned();
            let lhs = (args >> 12) as u32 & REG_MASK;
            LX = IP as _;

            if $cond {
                IP = CP.add(read::<u32>(lhs) as usize);
                let off = read::<u32>(lhs) as usize;
                println!("[jump to register]");
                println!("[jump offset] {:x}", off);
                println!("[jump address] => {:p}", { IP });
            } else {
                IP = IP.add(8);
            }
        }
    };
}

macro_rules! int_impl {
    ($trt:ident { $($exp:tt)* }) => {
        int_impl!(@IMP $trt, u8, $($exp)*);
        int_impl!(@IMP $trt, u16, $($exp)*);
        int_impl!(@IMP $trt, u32, $($exp)*);
        int_impl!(@IMP $trt, u64, $($exp)*);
        int_impl!(@IMP $trt, u128, $($exp)*);
        int_impl!(@IMP $trt, i8, $($exp)*);
        int_impl!(@IMP $trt, i16, $($exp)*);
        int_impl!(@IMP $trt, i32, $($exp)*);
        int_impl!(@IMP $trt, i64, $($exp)*);
        int_impl!(@IMP $trt, i128, $($exp)*);
    };
    (@IMP $trt:ident, $typ:ident, $($exp:tt)*) => {
        impl $trt for $typ {
            $($exp)*
        }
    };
}

trait DivUnchecked: Sized {
    /// Calculates the divisor when `self` is divided by `rhs`.
    /// 
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic
    /// overflow would occur. Note that for unsigned integers overflow never occurs,
    /// so the second value is always `false`.
    /// 
    /// It is **Undefined Behavior** if `rhs` is zero.
    fn overflowing_div_unchecked(self, rhs: Self) -> (Self, bool);

    /// Calculates the remainder when `self` is divided by `rhs`.
    /// 
    /// Returns a tuple of the remainder after dividing along with a boolean indicating 
    /// whether an arithmetic overflow would occur. Note that for unsigned integers overflow
    /// never occurs, so the second value is always `false`.
    /// 
    /// It is **Undefined Behavior** if `rhs` is zero.
    fn overflowing_rem_unchecked(self, rhs: Self) -> (Self, bool);
}

int_impl!(DivUnchecked {
    fn overflowing_div_unchecked(self, rhs: Self) -> (Self, bool) {
        if rhs == 0 {
            unsafe { hint::unreachable_unchecked() };
        }
        self.overflowing_div(rhs)
    }

    fn overflowing_rem_unchecked(self, rhs: Self) -> (Self, bool) {
        if rhs == 0 {
            unsafe { hint::unreachable_unchecked() };
        }
        self.overflowing_rem(rhs)
    }
});

trait ToLe: Sized {
    /// Converts `self` to little endian from the target’s endianness.
    /// 
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    fn to_le(self) -> Self;
}

int_impl!(ToLe {
    fn to_le(self) -> Self {
        self.to_le()
    }
});

// Continues logic from `__start`. Interprets the loaded executable and well, executes it.
#[inline]
pub unsafe fn run() -> ! {
    loop {
        //println!("????");
        let op = unsafe { *IP };
        /*
        let mut buf = [0u8; 4];
        _ = itoa(&mut buf, op as u32, 16);
        print!("0x");
        unsafe { syscall!(2, 1, buf.as_ptr(), 4) };
        println!();
        */
        match op {
            // nop - No operation
            0x00 => unsafe { IP = IP.add(8) },
            // clr - Clear bits
            //0x01 => unsafe { ins!(|T, ic| write::<T>(ic, |ic| val(ic, 0))) },
            // clr - Clear bits
            0x01 => unsafe { ins!(|T, reg| write::<T>(reg, 0)) },
            // str - Store
            0x02 => unsafe { ins!(|T, dst, src| write::<T>(dst, read(src))) },
            // stri - Store Immediate
            //0x03 => unsafe { ins!(|T, ic| write::<T>(ic, |ic| imm(ic))) },
            // stri - Store Immediate
            0x03 => unsafe { ins!(@I |T, dst| write::<T>(dst, imm())) },
            /*
            // ld - Load
            0x04 => unsafe {
                ins!(|T, ic| {
                    let (arg1, ic) = read::<T, *const u8>(ic, |ic| ic);
                    write(ic, |ic| val(ic, arg1));
                })
            },
            */
            /*
            // swp - Swap
            0x04 => unsafe {
                ins!(|T, dst_ic| {
                    let tmp = read::<T, ()>(dst_ic, |_| {}).0;
                    write::<T>(dst_ic, |src_ic| read(src_ic, |_| write(src_ic, |ic| val(ic, tmp))).0);
                })
            },
            */
            0x04 => unsafe {
                ins!(|T, dst, src| {
                    let tmp = read::<T>(dst);
                    write::<T>(dst, read(src));
                    write(src, tmp);
                })
            },
            // add - Add
            0x05 => ovrflw_rmw_binop!(@S overflowing_add),
            // addi - Add Immediate
            0x06 => ovrflw_rmw_binop!(@S @I overflowing_add),
            // uadd - Unsigned Add
            0x07 => ovrflw_rmw_binop!(overflowing_add),
            // uaddi - Unsigned Add Immediate
            0x08 => ovrflw_rmw_binop!(@I overflowing_add),
            // sub - Subtract
            0x09 => ovrflw_rmw_binop!(@S overflowing_sub),
            // subi - Subtract Immediate
            0x0A => ovrflw_rmw_binop!(@S @I overflowing_sub),
            // usub - Unsigned Subtract
            0x0B => ovrflw_rmw_binop!(overflowing_sub),
            // usubi - Unsigned Subtract Immediate
            0x0C => ovrflw_rmw_binop!(@I overflowing_sub),
            // mul - Multiply
            0x0D => ovrflw_rmw_binop!(@S overflowing_mul),
            // muli - Multiply Immediate
            0x0E => ovrflw_rmw_binop!(@S @I overflowing_mul),
            // umul - Unsigned Multiply
            0x0F => ovrflw_rmw_binop!(overflowing_mul),
            // umuli - Unsigned Multiply Immediate
            0x10 => ovrflw_rmw_binop!(@I overflowing_mul),
            // div - Divide
            0x11 => ovrflw_rmw_binop!(@S overflowing_div_unchecked),
            // divi - Divide Immediate
            0x12 => ovrflw_rmw_binop!(@S @I overflowing_div_unchecked),
            // udiv - Unsigned Divide Immediate
            0x13 => ovrflw_rmw_binop!(overflowing_div_unchecked),
            // udivi - Unsigned Divide Immediate
            0x14 => ovrflw_rmw_binop!(@I overflowing_div_unchecked),
            // rem - Modulo
            0x15 => ovrflw_rmw_binop!(@S overflowing_rem_unchecked),
            // remi - Modulo Immediate
            0x16 => ovrflw_rmw_binop!(@S @I overflowing_rem_unchecked),
            // urem - Unsigned Modulo Immediate
            0x17 => ovrflw_rmw_binop!(overflowing_rem_unchecked),
            // uremi - Unsigned Modulo Immediate
            0x18 => ovrflw_rmw_binop!(@I overflowing_rem_unchecked),
            // neg - Negate
            0x19 => ovrflw_binop!(@S overflowing_neg), // neg %d0, %d1 %d1 is negated and stored in %d0
            // shl - Shift Left
            0x1A => ovrflw_sh_binop!(overflowing_shl),
            // shli - Shift Left Immediate
            0x1B => ovrflw_sh_binop!(@I overflowing_shl),
            // shr - Shift Right
            0x1C => ovrflw_sh_binop!(overflowing_shr),
            // shri - Shift Right Immediate
            0x1D => ovrflw_sh_binop!(@I overflowing_shr),
            // sar - Arithmetic Shift Right
            0x1E => ovrflw_sh_binop!(@S overflowing_shr),
            // sari - Arithmetic Shift Right Immediate
            0x1F => ovrflw_sh_binop!(@S @I overflowing_shr),
            // rol - Rotate Left
            0x20 => sh_binop!(rotate_left),
            // roli - Rotate Left Immediate
            0x21 => sh_binop!(@I rotate_left),
            // ror - Rotate Right
            0x22 => sh_binop!(rotate_right),
            // rori - Rotate Right Immediate
            0x23 => sh_binop!(@I rotate_right),
            // and - Bitwise And
            0x24 => rmw_binop!(&),
            // andi - Bitwise And Immediate
            0x25 => rmw_binop!(@I &),
            // or - Bitwise Or
            0x26 => rmw_binop!(|),
            // ori - Bitwise Or Immediate
            0x27 => rmw_binop!(@I |),
            // xor - Bitwise Exclusive Or
            0x28 => rmw_binop!(^),
            // xori - Bitwise Exclusive Or Immediate
            0x29 => rmw_binop!(@I ^),
            // not - Bitwise Not
            0x2A => binop!(!), // same as neg
            // adc - Add With Carry
            0x2B => sigill(),
            // adci - Add With Carry Immediate
            0x2C => sigill(),
            // uadc - Unsigned Add With Carry
            0x2D => sigill(),
            // uadci - Unsigned Add With Carry Immediate
            0x2E => sigill(),
            // sbb - Subtract With Borrow
            0x2F => sigill(),
            // sbbi - Subtract With Borrow Immediate
            0x30 => sigill(),
            // usbb - Unsigned Subtract With Borrow
            0x31 => sigill(),
            // usbb - Unsigned Subtract With Borrow Immediate
            0x32 => sigill(),
            // adw - Wrapping Add
            0x33 => rmw_binop!(@S wrapping_add),
            // adwi - Wrapping Add Immediate
            0x34 => rmw_binop!(@S @I wrapping_add),
            // uadw - Unsigned Wrapping Add
            0x35 => rmw_binop!(wrapping_add),
            // uadwi - Unsigned Wrapping Add Immediate
            0x36 => rmw_binop!(@I wrapping_add),
            // sbw - Wrapping Subtract
            0x37 => rmw_binop!(@S wrapping_sub),
            // sbwi - Wrapping Subtract Immediate
            0x38 => rmw_binop!(@S @I wrapping_sub),
            // usbw - Unsigned Wrapping Subtract
            0x39 => rmw_binop!(wrapping_sub),
            // usbwi - Unsigned Wrapping Subtract Immediate
            0x3A => rmw_binop!(@I wrapping_sub),
            // mlw - Wrapping Multiply
            0x3B => rmw_binop!(@S wrapping_mul),
            // mlwi - Wrapping Multiply Immediate
            0x3C => rmw_binop!(@S @I wrapping_mul),
            // umlw - Unsigned Wrapping Multiply
            0x3D => rmw_binop!(wrapping_mul),
            // umlwi - Unsigned Wrapping Multiply Immediate
            0x3E => rmw_binop!(@I wrapping_mul),
            // dvw - Wrapping Divide
            0x3F => rmw_binop!(@S wrapping_div),
            // dvwi - Wrapping Divide Immediate
            0x40 => rmw_binop!(@S @I wrapping_div),
            // udvw - Unsigned Wrapping Divide
            0x41 => rmw_binop!(wrapping_div),
            // udvwi - Unsigned Wrapping Divide Immediate
            0x42 => rmw_binop!(@I wrapping_div),
            // remw - Wrapping Modulo
            0x43 => rmw_binop!(@S wrapping_rem),
            // remwi - Wrapping Modulo Immediate
            0x44 => rmw_binop!(@S @I wrapping_rem),
            // uremw - Unsigned Wrapping Modulo
            0x45 => rmw_binop!(wrapping_rem),
            // uremwi - Unsigned Wrapping Modulo Immediate
            0x46 => rmw_binop!(@I wrapping_rem),
            // negw - Wrapping Negate
            0x47 => binop!(@S wrapping_neg), // same as neg
            // shlw - Wrapping Shift Left
            0x48 => sh_binop!(wrapping_shl),
            // shlwi - Wrapping Shift Left Immediate
            0x49 => sh_binop!(@I wrapping_shl),
            // shrw - Wrapping Shift Right
            0x4A => sh_binop!(wrapping_shr),
            // shrwi - Wrapping Shift Right Immediate
            0x4B => sh_binop!(@I wrapping_shr),
            // sarw - Wrapping Arithmetic Shift Right
            0x4C => sh_binop!(@S wrapping_shr),
            // sarwi - Wrapping Arithmetic Shift Right Immediate
            0x4D => sh_binop!(@S @I wrapping_shr),
            // ads - Saturating Add
            0x4E => rmw_binop!(@S saturating_add),
            // adsi - Saturating Add Immediate
            0x4F => rmw_binop!(@S @I saturating_add),
            // uads - Unsigned Saturating Add
            0x50 => rmw_binop!(saturating_add),
            // uadsi - Unsigned Saturating Add Immediate
            0x51 => rmw_binop!(@I saturating_add),
            // sbs - Saturating Subtract
            0x52 => rmw_binop!(@S saturating_sub),
            // sbsi - Saturating Subtract Immediate
            0x53 => rmw_binop!(@S @I saturating_sub),
            // usbs - Unsigned Saturating Subtract
            0x54 => rmw_binop!(saturating_sub),
            // usbsi - Unsigned Saturating Subtract Immediate
            0x55 => rmw_binop!(@I saturating_sub),
            // mls - Saturating Multiply
            0x56 => rmw_binop!(@S saturating_mul),
            // mlsi - Saturating Multiply Immediate
            0x57 => rmw_binop!(@S @I saturating_mul),
            // umls - Unsigned Saturating Multiply
            0x58 => rmw_binop!(saturating_mul),
            // umlsi - Unsigned Saturating Multiply Immediate
            0x59 => rmw_binop!(@I saturating_mul),
            // dvs - Saturating Divide
            0x5A => rmw_binop!(@S saturating_div),
            // dvsi - Saturating Divide Immediate
            0x5B => rmw_binop!(@S @I saturating_div),
            // udvs - Unsigned Saturating Divide
            0x5C => rmw_binop!(saturating_div),
            // udvsi - Unsigned Saturating Divide Immediate
            0x5D => rmw_binop!(@I saturating_div),
            // ctpop - Count Population (Count Ones)
            0x5E => cnt_binop!(count_ones),
            // ctlz - Count Leading Zeros
            0x5F => cnt_binop!(leading_zeros),
            // cttz - Count Trailing Zeros
            0x60 => cnt_binop!(trailing_zeros),
            // brev - Reverse Bytes
            0x61 => binop!(swap_bytes), // same as neg
            // rvbit - Reverse Bits
            0x62 => binop!(reverse_bits), // same as neg
            // max - Maximum
            0x63 => rmw_binop!(@S max),
            // maxi - Maximum With Immediate
            0x64 => rmw_binop!(@S @I max),
            // umax - Unsigned Maximum
            0x65 => rmw_binop!(max),
            // umaxi - Unsigned Maximum With Immediate
            0x66 => rmw_binop!(@I max),
            // min - Minimum
            0x67 => rmw_binop!(@S min),
            // mini - Minimum With Immediate
            0x68 => rmw_binop!(@S @I min),
            // umin - Unsigned Minimum
            0x69 => rmw_binop!(min),
            // umini - Unsigned Minimum With Immediate
            0x6A => rmw_binop!(@I min),
            // cmp - Compare
            0x6B => cmp_binop!(@S),
            // cmpi - Compare Immediate
            0x6C => cmp_binop!(@S @I),
            // ucmp - Unsigned Compare
            0x6D => cmp_binop!(),
            // ucmpi - Unsigned Compare Immediate
            0x6E => cmp_binop!(@I),
            // jeq - Jump If Equal (ORD=0b00)
            0x6F => j_unop!(ORD() == 0b00),
            // jeqr - Jump Register If Equal
            0x70 => j_unop!(@R ORD() == 0b00),
            // jne - Jump If Not Equal
            0x71 => j_unop!(ORD() != 0b00),
            // jner - Jump Register If Not Equal
            0x72 => j_unop!(@R ORD() != 0b00),
            // jlt - Jump If Less Than (ORD=0b11)
            0x73 => j_unop!(ORD() == 0b11),
            // jltr - Jump Register If Less Than
            0x74 => j_unop!(@R ORD() == 0b11),
            // jgt - Jump If Greater Than (ORD=0b01)
            0x75 => j_unop!(ORD() == 0b01),
            // jgtr - Jump Register If Greater Than
            0x76 => j_unop!(@R ORD() == 0b01),
            // jle - Jump If Less Than Or Equal
            0x77 => j_unop!(ORD() != 0b01),
            // jler - Jump Register If Less Than Or Equal
            0x78 => j_unop!(@R ORD() != 0b01),
            // jge - Jump If Greater Than Or Equal
            0x79 => j_unop!(ORD() != 0b11),
            // jger - Jump Register If Greater Than Or Equal
            0x7A => j_unop!(@R ORD() != 0b11),
            // jo - Jump If Overflow
            0x7B => j_unop!(OF() == 0b1),
            // jor - Jump Register If Overflow
            0x7C => j_unop!(@R OF() == 0b1),
            // jno - Jump If No Overflow
            0x7D => j_unop!(OF() == 0b0),
            // jnor - Jump Register If No Overflow
            0x7E => j_unop!(@R OF() == 0b0),
            // jc - Jump If Carry
            0x7F => j_unop!(CF() == 0b1),
            // jcr - Jump Register If Carry
            0x80 => j_unop!(@R CF() == 0b1),
            // jnc - Jump If No Carry
            0x81 => j_unop!(CF() == 0b0),
            // jncr - Jump Register If No Carry
            0x82 => j_unop!(@R CF() == 0b0),
            // j - Jump
            0x83 => j_unop!(true),
            // jr - Jump Register
            0x84 => j_unop!(@R true),
            // jl - Jump And Link
            0x85 => j_unop!(@L true),
            // jrl - Jump Register And Link
            0x86 => j_unop!(@R @L true),
            // lnk - Link
            0x87 => unsafe {
                reg_info();
                LX = IP.add(8) as _;
                IP = IP.add(8);
            },
            // yld - Yield
            0x88 => unsafe {
                reg_info();
                hint::spin_loop();
                IP = IP.add(8);
            },
            // syscall - Syscall
            0x89 => unsafe {
                reg_info();
                RX = syscall!(RX as usize, A0, A1, A2, A3, A4, A5) as u64;
                IP = IP.add(8);
            },
            _ => {
                println!("headless");
                sigill();
            },
        }
        //println!("???");
        //println!("next instruction");
    }
}
