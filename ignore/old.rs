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
static mut MP: u64 = 0;
static mut FP: u64 = 0;
static mut LX: u64 = 0;
static mut RX: u64 = 0;

// Hidden Registers
/// Instruction pointer.
static mut IP: *const u8 = ptr::null();

/// Status register.
/// 
/// ## Bits
/// 0 - overflow
/// 
/// 1 - carry
/// 
/// 2..3 - ordering (0b00 - eq, 0b01 - gt, 0b11 - lt)
static mut ST: u8 = 0;

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
    let reg = (arg >> 1) & 0b1111111;
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
unsafe fn arg_offset(arg: i32) -> isize {
    (arg >> 8) as isize
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
            "{PURP}{:p}{NORM} <{GREN}0x{:02x}{NORM}>:",
            IP as *const u8,
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

/// Convience method to generate generic instruction logic on *unsigned* words.
macro_rules! ins {
    (|$typ:ident, $ic:ident| $($exp:tt)*) => {{
        reg_info();

        let size = *IP.add(1);
        let $ic = IP.add(2);

        match size {
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
    }};
}

/// Convience method to generate generic instruction logic that operates on *signed* words.
macro_rules! sins {
    (|$typ:ident, $ic:ident| $($exp:tt)*) => {{
        reg_info();

        let size = *IP.add(1);
        let $ic = IP.add(2);

        match size {
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
    }};
}

/// Convience method to generate *binary* operator logic.
macro_rules! trinop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                lhs.$op(rhs)
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                lhs.$op(rhs)
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                lhs.$op(rhs)
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                lhs.$op(rhs)
            }))
        }
    };
    ($op:tt) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                lhs $op rhs
            }))
        }
    };
    (@I $op:tt) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                lhs $op rhs
            }))
        }
    };
}

/// Convience method to generate *binary* operator logic that may *overflow*.
macro_rules! ovrflw_trinop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *unary* operator logic.
macro_rules! binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                lhs.$op()
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                lhs.$op()
            }))
        }
    };
    ($op:tt) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                $op lhs
            }))
        }
    };
    (@S $op:tt) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                $op lhs
            }))
        }
    };
}

/// Convience method to generate *unary* operator logic that may *overflow*.
macro_rules! ovrflw_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                let (res, ov) = lhs.$op();
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                let (res, ov) = lhs.$op();
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *binary shift* operator logic.
macro_rules! sh_trinop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| read(ic, |ic| end(ic)).0);
                lhs.$op(rhs)
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| imm(ic));
                lhs.$op(rhs)
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| read(ic, |ic| end(ic)).0);
                lhs.$op(rhs)
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| imm(ic));
                lhs.$op(rhs)
            }))
        }
    };
}

/// Convience method to generate *binary shift* operator logic that may overflow.
macro_rules! ovrflw_sh_trinop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| read(ic, |ic| end(ic)).0);
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@I $op:ident) => {
        unsafe {
            ins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| imm(ic));
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| read(ic, |ic| end(ic)).0);
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
    (@S @I $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<T>(ic, |ic| {
                let (lhs, rhs) = read::<T, u32>(ic, |ic| imm(ic));
                let (res, ov) = lhs.$op(rhs);
                ST |= ov as u8;
                res
            }))
        }
    };
}

/// Convience method to generate *"counting-bits" unary* operator logic.
macro_rules! cnt_binop {
    ($op:ident) => {
        unsafe {
            ins!(|T, ic| write::<u32>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                lhs.$op()
            }))
        }
    };
    (@S $op:ident) => {
        unsafe {
            sins!(|T, ic| write::<u32>(ic, |ic| {
                let lhs = read::<T, ()>(ic, |ic| end(ic)).0;
                lhs.$op()
            }))
        }
    };
}

/// Convience method to generate *comparison binary* operator logic.
macro_rules! cmp_binop {
    () => {
        unsafe {
            ins!(|T, ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                let res = lhs.cmp(&rhs);
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@I) => {
        unsafe {
            ins!(|T, ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                let res = lhs.cmp(&rhs);
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@S) => {
        unsafe {
            sins!(|T, ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| read(ic, |ic| end(ic)).0);
                let res = lhs.cmp(&rhs);
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
        }
    };
    (@S @I) => {
        unsafe {
            sins!(|T, ic| {
                let (lhs, rhs) = read::<T, T>(ic, |ic| imm(ic));
                let res = lhs.cmp(&rhs);
                ST &= 0b11;
                ST |= (res as u8) << 2;
            })
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

// TODO: handle divide by zero
// Continues logic from `__start`. Interprets the loaded executable and well, executes it.
#[inline]
pub unsafe fn run() -> ! {
    loop {
        let op = unsafe { *IP };
        match op {
            // nop - No operation
            0x00 => unsafe { IP = IP.add(1) },
            // clr - Clear bits
            0x01 => unsafe { ins!(|T, ic| write::<T>(ic, |ic| val(ic, 0))) },
            // str - Store
            0x02 => unsafe { ins!(|T, ic| write::<T>(ic, |ic| read(ic, |ic| end(ic)).0)) },
            // stri - Store Immediate
            0x03 => unsafe { ins!(|T, ic| write::<T>(ic, |ic| imm(ic))) },
            // ld - Load
            0x04 => unsafe {
                ins!(|T, ic| {
                    let (arg1, ic) = read::<T, *const u8>(ic, |ic| ic);
                    write(ic, |ic| val(ic, arg1));
                })
            },
            // swp - Swap
            0x05 => unsafe {
                ins!(|T, dst_ic| {
                    let tmp = read::<T, ()>(dst_ic, |_| {}).0;
                    write::<T>(dst_ic, |src_ic| read(src_ic, |_| write(src_ic, |ic| val(ic, tmp))).0);
                })
            },
            // add - Add
            0x06 => ovrflw_trinop!(@S overflowing_add),
            // addi - Add Immediate
            0x07 => ovrflw_trinop!(@S @I overflowing_add),
            // uadd - Unsigned Add
            0x08 => ovrflw_trinop!(overflowing_add),
            // uaddi - Unsigned Add Immediate
            0x09 => ovrflw_trinop!(@I overflowing_add),
            // sub - Subtract
            0x0A => ovrflw_trinop!(@S overflowing_sub),
            // subi - Subtract Immediate
            0x0B => ovrflw_trinop!(@S @I overflowing_sub),
            // usub - Unsigned Subtract
            0x0C => ovrflw_trinop!(overflowing_sub),
            // usubi - Unsigned Subtract Immediate
            0x0D => ovrflw_trinop!(@I overflowing_sub),
            // mul - Multiply
            0x0E => ovrflw_trinop!(@S overflowing_mul),
            // muli - Multiply Immediate
            0x0F => ovrflw_trinop!(@S @I overflowing_mul),
            // umul - Unsigned Multiply
            0x10 => ovrflw_trinop!(overflowing_mul),
            // umuli - Unsigned Multiply Immediate
            0x11 => ovrflw_trinop!(@I overflowing_mul),
            // div - Divide
            0x12 => ovrflw_trinop!(@S overflowing_div_unchecked),
            // divi - Divide Immediate
            0x13 => ovrflw_trinop!(@S @I overflowing_div_unchecked),
            // udiv - Unsigned Divide Immediate
            0x14 => ovrflw_trinop!(overflowing_div_unchecked),
            // udivi - Unsigned Divide Immediate
            0x15 => ovrflw_trinop!(@I overflowing_div_unchecked),
            // rem - Modulo
            0x16 => ovrflw_trinop!(@S overflowing_rem_unchecked),
            // remi - Modulo Immediate
            0x17 => ovrflw_trinop!(@S @I overflowing_rem_unchecked),
            // urem - Unsigned Modulo Immediate
            0x18 => ovrflw_trinop!(overflowing_rem_unchecked),
            // uremi - Unsigned Modulo Immediate
            0x19 => ovrflw_trinop!(@I overflowing_rem_unchecked),
            // neg - Negate
            0x1A => ovrflw_binop!(@S overflowing_neg),
            // shl - Shift Left
            0x1B => ovrflw_sh_trinop!(overflowing_shl),
            // shli - Shift Left Immediate
            0x1C => ovrflw_sh_trinop!(@I overflowing_shl),
            // shr - Shift Right
            0x1D => ovrflw_sh_trinop!(overflowing_shr),
            // shri - Shift Right Immediate
            0x1E => ovrflw_sh_trinop!(@I overflowing_shr),
            // sar - Arithmetic Shift Right
            0x1F => ovrflw_sh_trinop!(@S overflowing_shr),
            // sari - Arithmetic Shift Right Immediate
            0x20 => ovrflw_sh_trinop!(@S @I overflowing_shr),
            // rol - Rotate Left
            0x21 => sh_trinop!(rotate_left),
            // roli - Rotate Left Immediate
            0x22 => sh_trinop!(@I rotate_left),
            // ror - Rotate Right
            0x23 => sh_trinop!(rotate_right),
            // rori - Rotate Right Immediate
            0x24 => sh_trinop!(@I rotate_right),
            // and - Bitwise And
            0x25 => trinop!(&),
            // andi - Bitwise And Immediate
            0x26 => trinop!(@I &),
            // or - Bitwise Or
            0x27 => trinop!(|),
            // ori - Bitwise Or Immediate
            0x28 => trinop!(@I |),
            // xor - Bitwise Exclusive Or
            0x29 => trinop!(^),
            // xori - Bitwise Exclusive Or Immediate
            0x2A => trinop!(@I ^),
            // not - Bitwise Not
            0x2B => binop!(!),
            // TODO: adc, adci, uadc, uadci, sbb, sbbi, usbb, usbbi
            0x2C => sigill(),
            0x2D => sigill(),
            0x2E => sigill(),
            0x2F => sigill(),
            0x30 => sigill(),
            0x31 => sigill(),
            0x32 => sigill(),
            0x33 => sigill(),
            // adw - Wrapping Add
            0x34 => trinop!(@S wrapping_add),
            // adwi - Wrapping Add Immediate
            0x35 => trinop!(@S @I wrapping_add),
            // uadw - Unsigned Wrapping Add
            0x36 => trinop!(wrapping_add),
            // uadwi - Unsigned Wrapping Add Immediate
            0x37 => trinop!(@I wrapping_add),
            // sbw - Wrapping Subtract
            0x38 => trinop!(@S wrapping_sub),
            // sbwi - Wrapping Subtract Immediate
            0x39 => trinop!(@S @I wrapping_sub),
            // usbw - Unsigned Wrapping Subtract
            0x3A => trinop!(wrapping_sub),
            // usbwi - Unsigned Wrapping Subtract Immediate
            0x3B => trinop!(@I wrapping_sub),
            // mlw - Wrapping Multiply
            0x3C => trinop!(@S wrapping_mul),
            // mlwi - Wrapping Multiply Immediate
            0x3D => trinop!(@S @I wrapping_mul),
            // umlw - Unsigned Wrapping Multiply
            0x3E => trinop!(wrapping_mul),
            // umlwi - Unsigned Wrapping Multiply Immediate
            0x3F => trinop!(@I wrapping_mul),
            // dvw - Wrapping Divide
            0x40 => trinop!(@S wrapping_div),
            // dvwi - Wrapping Divide Immediate
            0x41 => trinop!(@S @I wrapping_div),
            // udvw - Unsigned Wrapping Divide
            0x42 => trinop!(wrapping_div),
            // udvwi - Unsigned Wrapping Divide Immediate
            0x43 => trinop!(@I wrapping_div),
            // remw - Wrapping Modulo
            0x44 => trinop!(@S wrapping_rem),
            // remwi - Wrapping Modulo Immediate
            0x45 => trinop!(@S @I wrapping_rem),
            // uremw - Unsigned Wrapping Modulo
            0x46 => trinop!(wrapping_rem),
            // uremwi - Unsigned Wrapping Modulo Immediate
            0x47 => trinop!(@I wrapping_rem),
            // negw - Wrapping Negate
            0x48 => binop!(@S wrapping_neg),
            // shlw - Wrapping Shift Left
            0x49 => sh_trinop!(wrapping_shl),
            // shlwi - Wrapping Shift Left Immediate
            0x4A => sh_trinop!(@I wrapping_shl),
            // shrw - Wrapping Shift Right
            0x4B => sh_trinop!(wrapping_shr),
            // shrwi - Wrapping Shift Right Immediate
            0x4C => sh_trinop!(@I wrapping_shr),
            // sarw - Wrapping Arithmetic Shift Right
            0x4D => sh_trinop!(@S wrapping_shr),
            // sarwi - Wrapping Arithmetic Shift Right Immediate
            0x4E => sh_trinop!(@S @I wrapping_shr),
            // ads - Saturating Add
            0x4F => trinop!(@S saturating_add),
            // adsi - Saturating Add Immediate
            0x50 => trinop!(@S @I saturating_add),
            // uads - Unsigned Saturating Add
            0x51 => trinop!(saturating_add),
            // uadsi - Unsigned Saturating Add Immediate
            0x52 => trinop!(@I saturating_add),
            // sbs - Saturating Subtract
            0x53 => trinop!(@S saturating_sub),
            // sbsi - Saturating Subtract Immediate
            0x54 => trinop!(@S @I saturating_sub),
            // usbs - Unsigned Saturating Subtract
            0x55 => trinop!(saturating_sub),
            // usbsi - Unsigned Saturating Subtract Immediate
            0x56 => trinop!(@I saturating_sub),
            // mls - Saturating Multiply
            0x57 => trinop!(@S saturating_mul),
            // mlsi - Saturating Multiply Immediate
            0x58 => trinop!(@S @I saturating_mul),
            // umls - Unsigned Saturating Multiply
            0x59 => trinop!(saturating_mul),
            // umlsi - Unsigned Saturating Multiply Immediate
            0x5A => trinop!(@I saturating_mul),
            // dvs - Saturating Divide
            0x5B => trinop!(@S saturating_div),
            // dvsi - Saturating Divide Immediate
            0x5C => trinop!(@S @I saturating_div),
            // udvs - Unsigned Saturating Divide
            0x5D => trinop!(saturating_div),
            // udvsi - Unsigned Saturating Divide Immediate
            0x5E => trinop!(@I saturating_div),
            // ctz - Count Zeros
            0x5F => cnt_binop!(count_zeros),
            // cto - Count Ones (Population Count)
            0x60 => cnt_binop!(count_ones),
            // ctlz - Count Leading Zeros
            0x61 => cnt_binop!(leading_zeros),
            // ctlo - Count Leading Ones
            0x62 => cnt_binop!(leading_ones),
            // cttz - Count Trailing Zeros
            0x63 => cnt_binop!(trailing_zeros),
            // ctto - Count Trailing Ones
            0x64 => cnt_binop!(trailing_ones),
            // brev - Reverse Bytes
            0x65 => binop!(swap_bytes),
            // rvbit - Reverse Bits
            0x66 => binop!(reverse_bits),
            // max - Maximum
            0x67 => trinop!(@S max),
            // maxi - Maximum With Immediate
            0x68 => trinop!(@S @I max),
            // umax - Unsigned Maximum
            0x69 => trinop!(max),
            // umaxi - Unsigned Maximum With Immediate
            0x6A => trinop!(@I max),
            // min - Minimum
            0x6B => trinop!(@S min),
            // mini - Minimum With Immediate
            0x6C => trinop!(@S @I min),
            // umin - Unsigned Minimum
            0x6D => trinop!(min),
            // umini - Unsigned Minimum With Immediate
            0x6E => trinop!(@I min),
            // cmp - Compare
            0x6F => cmp_binop!(@S),
            // cmpi - Compare Immediate
            0x70 => cmp_binop!(@S @I),
            // ucmp - Unsigned Compare
            0x71 => cmp_binop!(),
            // ucmpi - Unsigned Compare Immediate
            0x72 => cmp_binop!(@I),
            _ => {
                println!("headless");
                sigill();
            },
        }
        //println!("next instruction");
    }
}
