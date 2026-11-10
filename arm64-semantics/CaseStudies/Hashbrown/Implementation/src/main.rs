#![forbid(unsafe_code)]
// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

use hashbrown_verified::{
    hashbrown_clear, hashbrown_contains_key, hashbrown_drop, hashbrown_get, hashbrown_insert,
    hashbrown_is_empty, hashbrown_len, hashbrown_new, hashbrown_remove, hashbrown_with_capacity,
};
use std::io::{self, Read, Write};
use std::process::ExitCode;

const MAX_LINE_LEN: usize = 4096;
const MAX_WITH_CAPACITY: u64 = 4096;

enum CliCmd {
    Insert(u64, u64),
    Get(u64),
    Remove(u64),
    Contains(u64),
    WithCapacity(u64),
    Len,
    IsEmpty,
    Clear,
}

#[inline(never)]
fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut it_a = a.iter();
    let mut it_b = b.iter();
    while let (Some(&x), Some(&y)) = (it_a.next(), it_b.next()) {
        if x != y {
            return false;
        }
    }
    true
}

#[inline(never)]
fn strip_prefix<'a>(bs: &'a [u8], pfx: &[u8]) -> Option<&'a [u8]> {
    let (head, rest) = bs.split_at_checked(pfx.len())?;
    if bytes_eq(head, pfx) {
        Some(rest)
    } else {
        None
    }
}

#[inline(never)]
fn split_once_space(bs: &[u8]) -> Option<(&[u8], &[u8])> {
    let mut idx = 0;
    for &b in bs {
        if b == b' ' {
            let (lhs, rest) = bs.split_at_checked(idx)?;
            let (_, rhs) = rest.split_at_checked(1)?;
            return Some((lhs, rhs));
        }
        idx += 1;
    }
    None
}

#[inline(never)]
fn parse_decimal_u64(bs: &[u8]) -> Option<u64> {
    if bs.is_empty() {
        return None;
    }
    let mut acc: u64 = 0;
    for &b in bs {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = acc.checked_mul(10)?.checked_add(u64::from(b - b'0'))?;
    }
    Some(acc)
}

#[inline(never)]
fn parse_command(line: &[u8]) -> Option<CliCmd> {
    if let Some(rest) = strip_prefix(line, b"insert ") {
        let (ks, vs) = split_once_space(rest)?;
        let k = parse_decimal_u64(ks)?;
        let v = parse_decimal_u64(vs)?;
        Some(CliCmd::Insert(k, v))
    } else if let Some(rest) = strip_prefix(line, b"remove ") {
        Some(CliCmd::Remove(parse_decimal_u64(rest)?))
    } else if let Some(rest) = strip_prefix(line, b"get ") {
        Some(CliCmd::Get(parse_decimal_u64(rest)?))
    } else if let Some(rest) = strip_prefix(line, b"contains ") {
        Some(CliCmd::Contains(parse_decimal_u64(rest)?))
    } else if let Some(rest) = strip_prefix(line, b"with_capacity ") {
        let cap = parse_decimal_u64(rest)?;
        if cap <= MAX_WITH_CAPACITY {
            Some(CliCmd::WithCapacity(cap))
        } else {
            None
        }
    } else if bytes_eq(line, b"len") {
        Some(CliCmd::Len)
    } else if bytes_eq(line, b"is_empty") {
        Some(CliCmd::IsEmpty)
    } else if bytes_eq(line, b"clear") {
        Some(CliCmd::Clear)
    } else {
        None
    }
}

#[inline(never)]
fn print_u64(v: u64) {
    println!("{v}");
}

#[inline(never)]
fn print_bool(b: bool) {
    if b {
        println!("true");
    } else {
        println!("false");
    }
}

fn main() -> ExitCode {
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return ExitCode::from(2);
    }

    let body = match input.split_last() {
        None => return ExitCode::SUCCESS,
        Some((&b'\n', rest)) => rest,
        Some(_) => input.as_slice(),
    };

    if body
        .split(|&b| b == b'\n')
        .any(|line| line.len() > MAX_LINE_LEN)
    {
        let _ = io::stderr().write_all(b"error: line too long\n");
        return ExitCode::FAILURE;
    }

    let mut map = hashbrown_new();
    for line in body.split(|&b| b == b'\n') {
        match parse_command(line) {
            Some(CliCmd::Insert(k, v)) => {
                let _ = hashbrown_insert(&mut map, k, v);
            }
            Some(CliCmd::Remove(k)) => {
                let _ = hashbrown_remove(&mut map, k);
            }
            Some(CliCmd::Get(k)) => match hashbrown_get(&map, k) {
                Some(v) => print_u64(v),
                None => println!("none"),
            },
            Some(CliCmd::Contains(k)) => {
                print_bool(hashbrown_contains_key(&map, k));
            }
            Some(CliCmd::WithCapacity(cap)) => {
                hashbrown_drop(map);
                map = hashbrown_with_capacity(cap as usize);
            }
            Some(CliCmd::Len) => {
                print_u64(hashbrown_len(&map) as u64);
            }
            Some(CliCmd::IsEmpty) => {
                print_bool(hashbrown_is_empty(&map));
            }
            Some(CliCmd::Clear) => {
                hashbrown_clear(&mut map);
            }
            None => {
                let _ = io::stderr().write_all(b"error: invalid command\n");
            }
        }
    }
    hashbrown_drop(map);

    ExitCode::SUCCESS
}
