pub use util::prelude::*;

pub mod util {
    //! Copyright (c) 2018 Daiki Mizukami.
    //!
    //! Licensed under the Unlicense unless explicitly mentioned.


    pub mod prelude {
        pub use super::common::prelude::*;
        pub use super::io::prelude::*;
        pub use super::num::prelude::*;
    }

    pub mod common {
        use std::fmt::Debug;
        use std::mem;


        pub mod prelude {
            pub use super::IteratorUnwrappedExt;
            pub use super::IteratorTakeHeadsExt;
            pub use super::memchr;
            pub use super::memchr2;
            pub use super::memchr3;
        }

        pub trait Unwrap {
            type Item;

            fn unwrap(self) -> Self::Item;
        }

        impl<T, E: Debug> Unwrap for Result<T, E> {
            type Item = T;

            fn unwrap(self) -> T {
                Result::unwrap(self)
            }
        }

        impl<T> Unwrap for Option<T> {
            type Item = T;

            fn unwrap(self) -> T {
                Option::unwrap(self)
            }
        }


        pub trait IteratorUnwrappedExt: Sized {
            fn unwrapped(self) -> Unwrapped<Self>;
        }

        impl<I> IteratorUnwrappedExt for I
            where I: Iterator, I::Item: Unwrap
        {
            fn unwrapped(self) -> Unwrapped<Self> {
                Unwrapped(self)
            }
        }

        pub struct Unwrapped<I>(I);

        impl<I> Iterator for Unwrapped<I>
            where I: Iterator, I::Item: Unwrap
        {
            type Item = <I::Item as Unwrap>::Item;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.next().map(Unwrap::unwrap)
            }
        }

        pub trait IteratorTakeHeadsExt: Sized {
            fn take_heads(self) -> TakeHeads<Self>;
        }

        impl<I: Iterator> IteratorTakeHeadsExt for I {
            fn take_heads(self) -> TakeHeads<Self> {
                TakeHeads(self)
            }
        }

        pub struct TakeHeads<I>(I);

        impl<I: Iterator> Iterator for TakeHeads<I> {
            type Item = I::Item;

            fn next(&mut self) -> Option<I::Item> {
                let ret = self.0.next();
                if ret.is_some() {
                    while let Some(_) = self.0.next() {}
                }
                ret
            }
        }


        pub trait FromByteStream: Sized {
            type Parser: ParseByteStream<Output=Self>;

            fn parser() -> Self::Parser;
        }

        pub trait ParseByteStream {
            type Output;

            fn eat(&mut self, slice: &[u8]);
            fn take(&mut self) -> Self::Output;
        }

        impl FromByteStream for () {
            type Parser = ();

            fn parser() -> () {}
        }

        impl ParseByteStream for () {
            type Output = ();

            fn eat(&mut self, _: &[u8]) {}
            fn take(&mut self) -> () {}
        }

        impl FromByteStream for String {
            type Parser = StringParser;

            fn parser() -> StringParser {
                Default::default()
            }
        }

        #[derive(Default)]
        pub struct StringParser(Vec<u8>);

        impl ParseByteStream for StringParser {
            type Output = String;

            fn eat(&mut self, s: &[u8]) {
                self.0.extend_from_slice(s)
            }

            fn take(&mut self) -> String {
                let vec = mem::replace(&mut self.0, Vec::new());
                String::from_utf8(vec).unwrap()
            }
        }

        #[derive(Default)]
        pub struct UnsignedParser<T>(T);

        macro_rules! parse_unsigned {
            ($($t:ty),*) => {$(
                impl FromByteStream for $t {
                    type Parser = UnsignedParser<$t>;

                    fn parser() -> UnsignedParser<$t> {
                        Default::default()
                    }
                }

                impl ParseByteStream for UnsignedParser<$t> {
                    type Output = $t;

                    fn eat(&mut self, s: &[u8]) {
                        for &b in s {
                            let n = atoi(b).unwrap() as $t;
                            self.0 = self.0
                                .checked_mul(10).unwrap()
                                .checked_add(n).unwrap();
                        }
                    }

                    fn take(&mut self) -> $t {
                        mem::replace(&mut self.0, 0)
                    }
                }
            )*};
        }

        pub struct SignedParser<T>(SignedParserState<T>);

        impl<T> Default for SignedParser<T> {
            fn default() -> Self {
                SignedParser(SignedParserState::None)
            }
        }

        macro_rules! parse_signed {
            ($($t:ty),*) => {$(
                impl FromByteStream for $t {
                    type Parser = SignedParser<$t>;

                    fn parser() -> SignedParser<$t> {
                        Default::default()
                    }
                }

                impl ParseByteStream for SignedParser<$t> {
                    type Output = $t;

                    fn eat(&mut self, s: &[u8]) {
                        use self::SignedParserState::*;

                        match self.0 {
                            Signed(ref mut n) | Unsigned(ref mut n) => {
                                for &b in s {
                                    let d = atoi(b).unwrap() as $t;
                                    *n = n.checked_mul(10).unwrap()
                                        .checked_add(d).unwrap();
                                }
                            },
                            None => if let Some((&b, rest)) = s.split_first() {
                                self.0 = if let Some(n) = atoi(b) {
                                    Unsigned(n as $t)
                                } else if b'-' == b {
                                    Signed(0)
                                } else {
                                    panic!("SignedParser::eat: invalid digit");
                                };

                                self.eat(rest);
                            },
                        }
                    }

                    fn take(&mut self) -> $t {
                        use self::SignedParserState::*;

                        match mem::replace(&mut self.0, None) {
                            Unsigned(n) => n,
                            Signed(n) => n.checked_neg().unwrap(),
                            None => panic!(
                                "SignedParser::take: no bytes were read"
                            ),
                        }
                    }
                }
            )*};
        }

        enum SignedParserState<T> {
            Unsigned(T),
            Signed(T),
            None,
        }

        fn atoi(c: u8) -> Option<u8> {
            if b'0' <= c && c <= b'9' {
                Some(c - b'0')
            } else {
                None
            }
        }

        parse_unsigned! { u8, u16, u32, u64, usize }
        parse_signed! { i8, i16, i32, i64, isize }


        pub fn memchr(c: u8, src: &[u8]) -> Option<usize> {
            use std::os::raw::{c_int, c_void};
            use super::ffi::memchr;

            let p = unsafe {
                memchr(src.as_ptr() as *const c_void, c as c_int, src.len())
            };

            if p.is_null() {
                None
            } else {
                Some(p as usize - src.as_ptr() as usize)
            }
        }


        pub use self::rust_memchr::*;

        // Code derived from Andrew Gallant's rust-memchr:
        // https://github.com/BurntSushi/rust-memchr/blob/df1092f/src/lib.rs
        // Licensed under the Unlicense.
        mod rust_memchr {
            use std::cmp;
            use std::mem;

            fn repeat_byte(b: u8) -> usize {
                let mut rep = (b as usize) << 8 | b as usize;
                rep = rep << 16 | rep;
                rep = rep << 32 | rep;
                rep
            }

            fn contains_zero_byte(x: usize) -> bool {
                x.wrapping_sub(0x0101010101010101) & !x & 0x8080808080808080 != 0
            }

            pub fn memchr2(needle1: u8, needle2: u8, haystack: &[u8])
                -> Option<usize>
            {
                fn slow(b1: u8, b2: u8, haystack: &[u8]) -> Option<usize> {
                    haystack.iter().position(|&b| b == b1 || b == b2)
                }

                #[allow(non_snake_case)]
                let USIZE_BYTES: usize = mem::size_of::<usize>();

                let len = haystack.len();
                let ptr = haystack.as_ptr();
                let align = (ptr as usize) & (USIZE_BYTES - 1);
                let mut i = 0;
                if align > 0 {
                    i = cmp::min(USIZE_BYTES - align, len);
                    if let Some(found) = slow(needle1, needle2, &haystack[..i]) {
                        return Some(found);
                    }
                }
                let repeated_b1 = repeat_byte(needle1);
                let repeated_b2 = repeat_byte(needle2);
                if len >= USIZE_BYTES {
                    while i <= len - USIZE_BYTES {
                        unsafe {
                            let u = *(ptr.offset(i as isize) as *const usize);
                            let found_ub1 = contains_zero_byte(u ^ repeated_b1);
                            let found_ub2 = contains_zero_byte(u ^ repeated_b2);
                            if found_ub1 || found_ub2 {
                                break;
                            }
                        }
                        i += USIZE_BYTES;
                    }
                }
                slow(needle1, needle2, &haystack[i..]).map(|pos| i + pos)
            }

            pub fn memchr3(
                needle1: u8,
                needle2: u8,
                needle3: u8,
                haystack: &[u8],
            ) -> Option<usize> {
                fn slow(b1: u8, b2: u8, b3: u8, haystack: &[u8]) -> Option<usize> {
                    haystack.iter().position(|&b| b == b1 || b == b2 || b == b3)
                }

                #[allow(non_snake_case)]
                let USIZE_BYTES: usize = mem::size_of::<usize>();

                let len = haystack.len();
                let ptr = haystack.as_ptr();
                let align = (ptr as usize) & (USIZE_BYTES - 1);
                let mut i = 0;
                if align > 0 {
                    i = cmp::min(USIZE_BYTES - align, len);
                    if let Some(found) = slow(needle1, needle2, needle3, &haystack[..i]) {
                        return Some(found);
                    }
                }
                let repeated_b1 = repeat_byte(needle1);
                let repeated_b2 = repeat_byte(needle2);
                let repeated_b3 = repeat_byte(needle3);
                if len >= USIZE_BYTES {
                    while i <= len - USIZE_BYTES {
                        unsafe {
                            let u = *(ptr.offset(i as isize) as *const usize);
                            let found_ub1 = contains_zero_byte(u ^ repeated_b1);
                            let found_ub2 = contains_zero_byte(u ^ repeated_b2);
                            let found_ub3 = contains_zero_byte(u ^ repeated_b3);
                            if found_ub1 || found_ub2 || found_ub3 {
                                break;
                            }
                        }
                        i += USIZE_BYTES;
                    }
                }
                slow(needle1, needle2, needle3, &haystack[i..]).map(|pos| i + pos)
            }
        }
    }

    pub mod num {
        use std::ops::Mul;

        pub mod prelude {
            pub use super::MulSquareExt;
        }

        pub trait MulSquareExt {
            fn square(self) -> Self;
        }

        impl<M: Mul<Output=Self>+Copy> MulSquareExt for M {
            fn square(self) -> Self {
                self * self
            }
        }
    }


    pub mod io {
        use std::io;
        use std::io::*;

        use super::common::*;


        pub mod prelude {
            pub use super::BufReadScanExt;
            pub use super::stdin;
            pub use super::stdout;
        }

        pub trait BufReadScanExt {
            fn scan<T: FromByteStream>(&mut self) -> Option<Result<T>>;
            fn scan_with<P: ParseByteStream>(&mut self, parser: &mut P)
                -> Option<Result<P::Output>>;
            fn scanner<T: FromByteStream>(self) -> Scanner<Self, T::Parser>
                where Self: Sized;
            fn scanner_with<P: ParseByteStream>(self, parser: P)
                -> Scanner<Self, P>
                where Self: Sized;
            fn scanner2<T, U>(self) -> Scanner2<Self, T::Parser, U::Parser>
            where
                Self: Sized,
                T: FromByteStream,
                U: FromByteStream;
            fn scanner2_with<P1, P2>(self, parser1: P1, parser2: P2)
                -> Scanner2<Self, P1, P2>
            where
                Self: Sized,
                P1: ParseByteStream,
                P2: ParseByteStream;
            fn scanner3<T, U, V>(self)
                -> Scanner3<Self, T::Parser, U::Parser, V::Parser>
            where
                Self: Sized,
                T: FromByteStream,
                U: FromByteStream,
                V: FromByteStream;
            fn scanner3_with<P1, P2, P3>(
                self,
                parser1: P1,
                parser2: P2,
                parser3: P3,
            )
                -> Scanner3<Self, P1, P2, P3>
            where
                Self: Sized,
                P1: ParseByteStream,
                P2: ParseByteStream,
                P3: ParseByteStream;
        }

        impl<R: BufRead+?Sized> BufReadScanExt for R {
            fn scan<T>(&mut self) -> Option<Result<T>>
                where T: FromByteStream
            {
                self.scan_with(&mut T::parser())
            }

            fn scan_with<P: ParseByteStream>(&mut self, parser: &mut P)
                -> Option<Result<P::Output>>
            {
                match skip_whitespace(self) {
                    Ok(true) => return None,
                    Ok(false) => (),
                    Err(e) => return Some(Err(e)),
                }

                let mut first = true;
                loop {
                    let (consume, done) = {
                        let buf = match self.fill_buf() {
                            Ok(b) => b,
                            Err(ref e)
                                if e.kind() == ErrorKind::Interrupted =>
                            {
                                continue;
                            },
                            Err(e) => return Some(Err(e)),
                        };

                        if buf.is_empty() {
                            return if first {
                                None
                            } else {
                                Some(Ok(parser.take()))
                            };
                        }

                        let i = memchr3(b' ', b'\r', b'\n', buf)
                            .unwrap_or(buf.len());

                        parser.eat(&buf[..i]);

                        (i, i != buf.len())
                    };

                    if consume != 0 {
                        self.consume(consume);
                    }

                    if done {
                        return Some(Ok(parser.take()));
                    }

                    first = false;
                }
            }

            fn scanner<T>(self) -> Scanner<Self, T::Parser>
            where
                Self: Sized,
                T: FromByteStream
            {
                self.scanner_with(T::parser())
            }

            fn scanner_with<P>(self, parser: P) -> Scanner<Self, P>
                where Self: Sized, P: ParseByteStream
            {
                Scanner {
                    reader: self,
                    // XXX: struct field shorthands are unstable on
                    // AtCoder's current version of rustc (1.15.1).
                    parser: parser,
                }
            }

            fn scanner2<T, U>(self) -> Scanner2<Self, T::Parser, U::Parser>
            where
                Self: Sized,
                T: FromByteStream,
                U: FromByteStream,
            {
                self.scanner2_with(T::parser(), U::parser())
            }

            fn scanner2_with<P1, P2>(self, parser1: P1, parser2: P2)
                -> Scanner2<Self, P1, P2>
            where
                Self: Sized,
                P1: ParseByteStream,
                P2: ParseByteStream,
            {
                Scanner2 {
                    reader: self,
                    parser1: parser1,
                    parser2: parser2,
                }
            }

            fn scanner3<T, U, V>(self)
                -> Scanner3<Self, T::Parser, U::Parser, V::Parser>
            where
                Self: Sized,
                T: FromByteStream,
                U: FromByteStream,
                V: FromByteStream,
            {
                self.scanner3_with(T::parser(),U::parser(),V::parser())
            }

            fn scanner3_with<P1, P2, P3>(
                self,
                parser1: P1,
                parser2: P2,
                parser3: P3,
            )
                -> Scanner3<Self, P1, P2, P3>
            where
                Self: Sized,
                P1: ParseByteStream,
                P2: ParseByteStream,
                P3: ParseByteStream,
            {
                Scanner3 {
                    reader: self,
                    parser1: parser1,
                    parser2: parser2,
                    parser3: parser3,
                }
            }
        }

        fn skip_whitespace<R: BufRead+?Sized>(r: &mut R) -> Result<bool> {
            let mut found_newline = false;

            loop {
                let (consume, done) = {
                    let mut buf = match r.fill_buf() {
                        Ok(b) => b,
                        Err(ref e) if e.kind() == ErrorKind::Interrupted => {
                            continue;
                        },
                        Err(e) => return Err(e),
                    };

                    let mut consume = 0;
                    let mut done = false;
                    for &b in buf {
                        match b {
                            b' ' | b'\r' => (),
                            b'\n' => found_newline = true,
                            _ => {
                                done = true;
                                break;
                            },
                        }
                        consume += 1;
                    }

                    (consume, done)
                };

                if consume != 0 {
                    r.consume(consume);
                }

                if done || consume == 0 {
                    return Ok(found_newline);
                }
            }
        }

        pub struct Scanner<R, P> {
            reader: R,
            parser: P,
        }

        impl<R, P> Scanner<R, P> {
            pub fn into_inner(self) -> R {
                self.reader
            }

            pub fn switch<T: FromByteStream>(self) -> Scanner<R, T::Parser> {
                self.switch_parser(T::parser())
            }

            pub fn switch_parser<Q: ParseByteStream>(self, parser: Q)
                -> Scanner<R, Q>
            {
                Scanner {
                    reader: self.reader,
                    parser: parser,
                }
            }
        }

        impl<R: BufRead, P: ParseByteStream> Iterator for Scanner<R, P> {
            type Item = Result<P::Output>;

            fn next(&mut self) -> Option<Result<P::Output>> {
                self.reader.scan_with(&mut self.parser)
            }
        }

        pub struct Scanner2<R, P1, P2> {
            reader: R,
            parser1: P1,
            parser2: P2,
        }

        impl<R, P1, P2> Scanner2<R, P1, P2> {
            pub fn into_inner(self) -> R {
                self.reader
            }

            pub fn switch<T, U>(self) -> Scanner2<R, T::Parser, U::Parser>
            where
                T: FromByteStream,
                U: FromByteStream,
            {
                self.switch_parsers(T::parser(), U::parser())
            }

            pub fn switch_parsers<Q1, Q2>(self, parser1: Q1, parser2: Q2)
                -> Scanner2<R, Q1, Q2>
            where
                Q1: ParseByteStream,
                Q2: ParseByteStream,
            {
                Scanner2 {
                    reader: self.reader,
                    parser1: parser1,
                    parser2: parser2,
                }
            }
        }

        impl<R: BufRead, P1, P2> Iterator for Scanner2<R, P1, P2>
            where P1: ParseByteStream, P2: ParseByteStream
        {
            type Item = Result<(P1::Output, P2::Output)>;

            fn next(&mut self) -> Option<Self::Item> {
                self.reader.scan_with(&mut self.parser1).map(|r| r.and_then(|t|
                    self.reader.scan_with(&mut self.parser2)
                        .expect("Scanner2: missing second item")
                        .map(|u| (t, u))
                ))
            }
        }

        pub struct Scanner3<R, P1, P2, P3> {
            reader: R,
            parser1: P1,
            parser2: P2,
            parser3: P3,
        }

        impl<R, P1, P2, P3> Scanner3<R, P1, P2, P3> {
            pub fn into_inner(self) -> R {
                self.reader
            }

            pub fn switch<T, U, V>(self)
                -> Scanner3<R, T::Parser, U::Parser, V::Parser>
            where
                T: FromByteStream,
                U: FromByteStream,
                V: FromByteStream,
            {
                self.switch_parsers(T::parser(), U::parser(), V::parser())
            }

            pub fn switch_parsers<Q1, Q2, Q3>(
                self,
                parser1: Q1,
                parser2: Q2,
                parser3: Q3,
            )
                -> Scanner3<R, Q1, Q2, Q3>
            where
                Q1: ParseByteStream,
                Q2: ParseByteStream,
            {
                Scanner3 {
                    reader: self.reader,
                    parser1: parser1,
                    parser2: parser2,
                    parser3: parser3,
                }
            }
        }

        impl<R: BufRead, P1, P2, P3> Iterator for Scanner3<R, P1, P2, P3>
            where P1: ParseByteStream, P2: ParseByteStream, P3: ParseByteStream
        {
            type Item = Result<(P1::Output, P2::Output, P3::Output)>;

            fn next(&mut self) -> Option<Self::Item> {
                self.reader.scan_with(&mut self.parser1).map(|r| r.and_then(|t|
                    self.reader.scan_with(&mut self.parser2)
                        .expect("Scanner3: missing second item")
                        .and_then(|u| {
                            self.reader.scan_with(&mut self.parser3)
                                .expect("Scanner3: missing third item")
                                .map(|v| (t, u, v))
                        })
                ))
            }
        }


        pub fn stdin() -> LockedStdio<Stdin, StdinLock<'static>> {
            let handle = io::stdin();
            unsafe {
                LockedStdio {
                    lock: (*(&handle as *const Stdin)).lock(),
                    _handle: handle,
                }
            }
        }

        pub fn stdout() -> LockedStdio<Stdout, StdoutLock<'static>> {
            let handle = io::stdout();
            unsafe {
                LockedStdio {
                    lock: (*(&handle as *const Stdout)).lock(),
                    _handle: handle,
                }
            }
        }

        pub struct LockedStdio<H, L> {
            _handle: H,
            lock: L,
        }

        impl<H, L: Read> Read for LockedStdio<H, L> {
            fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
                Read::read(&mut self.lock, buf)
            }
        }

        impl<H, L: BufRead> BufRead for LockedStdio<H, L> {
            fn fill_buf(&mut self) -> Result<&[u8]> {
                BufRead::fill_buf(&mut self.lock)
            }

            fn consume(&mut self, amt: usize) {
                BufRead::consume(&mut self.lock, amt);
            }
        }

        impl<H, L: Write> Write for LockedStdio<H, L> {
            fn write(&mut self, buf: &[u8]) -> Result<usize> {
                Write::write(&mut self.lock, buf)
            }

            fn flush(&mut self) -> Result<()> {
                Write::flush(&mut self.lock)
            }
        }
    }

    mod ffi {
        use std::os::raw::{c_int, c_void};

        extern {
            pub fn memchr(src: *const c_void, c: c_int, n: usize)
                -> *mut c_void;
        }
    }
}

#[cfg(test)]
mod tests;
