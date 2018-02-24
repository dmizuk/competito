use std::cmp;
use std::io::{self, BufRead, Read};
use std::mem;

use util::prelude::*;

#[test]
fn scanner() {
    let mut input = [
        b"-123 \r" as _,
        b"\n  0 1 2 3\n" as _,
        b"1" as _, b"234" as _, b" 2345 3456 " as _, b" 1" as _, b"\n" as _,
    ];
    let mut scanner = BufReadMock(&mut input).scanner::<i32>().unwrapped();

    assert!(scanner.by_ref().eq(vec![-123]));
    assert!(scanner.by_ref().eq(vec![0, 1, 2, 3]));
    assert!(scanner.by_ref().eq(vec![1234, 2345, 3456, 1]));
    assert!(scanner.next().is_none());
}

#[test]
fn scanner2() {
    let mut scanner = b"0 1 2 3\n4  5".scanner2::<i32, i32>().unwrapped();

    assert!(scanner.by_ref().eq(vec![(0, 1), (2, 3)]));
    assert!(scanner.by_ref().eq(vec![(4, 5)]));
    assert!(scanner.next().is_none());
}

#[test]
#[should_panic(expected = "Scanner2: missing the item for `parser2`")]
fn scanner2_missing_item() {
    b"a b c".scanner2::<(), ()>().unwrapped().skip(1).next();
}

#[test]
fn take_heads() {
    let array = [Some(0), Some(1), None, Some(2), None, None, Some(3)];
    let mut iter = IteratorMock(&array).cloned().take_heads();

    assert_eq!(iter.next().unwrap(), 0);
    assert_eq!(iter.next().unwrap(), 2);
    assert!(iter.next().is_none());
    assert_eq!(iter.next().unwrap(), 3);
    assert!(iter.next().is_none());
}

struct BufReadMock<'a>(&'a mut [&'a [u8]]);

impl<'a> BufRead for BufReadMock<'a> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        Ok(self.0[0])
    }

    fn consume(&mut self, amt: usize) {
        struct Slice<T> {
            ptr: *mut T,
            len: usize,
        }

        let amt = cmp::min(amt, self.0[0].len());
        self.0[0] = &self.0[0][amt..];

        if self.0[0].len() == 0 && self.0.len() > 1 {
            // XXX: very unsafe!
            unsafe {
                let slice = mem::transmute::<&mut &mut [&[u8]], &mut Slice<&[u8]>>(
                    &mut self.0
                );
                slice.ptr = slice.ptr.offset(1);
                slice.len -= 1;
            }
        }
    }
}

impl<'a> Read for BufReadMock<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0[0].read(buf)
    }
}

struct IteratorMock<'a, T: 'a>(&'a [Option<T>]);

impl<'a, T: 'a> Iterator for IteratorMock<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.split_first().and_then(|(t, rest)| {
            self.0 = rest;
            t.as_ref()
        })
    }
}
