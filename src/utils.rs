use core::{
    slice,
    str,
};

pub unsafe fn strlen(mut s: *const u8) -> usize {
    let mut count = 0;

    unsafe {
        while *s != b'\0' {
            count += 1;
            s = s.add(1);
        }
    }

    count
}

pub fn itoa(s: &mut [u8], n: u32, radix: u32) {
    assert!(radix > 1);

    fn itoa_loop(s: &mut [u8], n: u32, radix: u32, i: &mut usize) {
        if n > radix - 1 {
            itoa_loop(s, n / radix, radix, i)
        }

        let digit = (n % radix) as u8;
        let c = match digit {
            0..=9 => b'0' + digit,
            _ => b'a' + digit - 10,
        };

        s[*i] = c;
        *i += 1;

        assert!(*i != s.len());
    }

    itoa_loop(s, n, radix, &mut 0);
}

pub unsafe fn mkstr<'a>(buf: *const u8) -> &'a str {
    unsafe { str::from_utf8_unchecked(slice::from_raw_parts(buf, strlen(buf))) }
}
