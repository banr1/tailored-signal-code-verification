// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. See
// `third_party/libsignal/README.md`.

//! The `libsignal-cli` CLI's process I/O: the files of the party's directory (and of a bundle
//! directory), stdin and stdout. Nothing else in the CLI touches the operating system; it uses
//! this crate as its module `io`.
//!
//! Each of these four entrypoints is `#[inline(never)]` and returns unit [`IoError`] on I/O or
//! cap rejection so OS error representations stay inside this crate:
//! - [`read_file`] and [`read_stdin`] are hand-written `unsafe` C-ABI calls into `musl` (`open`,
//!   `read`, `close`, `__errno_location`) because the frozen verification engine has no verified
//!   bounded `std` read (`std::fs::read` and `Stdin::read_to_end` are unbounded). Each call reads
//!   in 4 KiB stack chunks asking for at most `cap + 1 - len` bytes per `read`, checks
//!   `len + n <= cap` before growing the output `Vec`, and grows with `reserve_exact` clamped at
//!   `cap` so `Vec` capacity never exceeds [`FILE_CAP`] (`2 MiB`) or [`STDIN_CAP`] (`1 MiB`).
//!   Missing files (`ENOENT`) return `Ok(Vec::new())`; closed `stdin` (`EBADF` on `fd = 0`)
//!   returns `Ok(out)` matching `std::io::Stdin`; `EINTR` retries `open` and `read` (unreachable
//!   in the deterministic process model; any other negative return yields `Err(IoError)`); paths
//!   of 4096 bytes (`PATH_MAX`) or more or containing an interior NUL byte return `Err(IoError)`
//!   using a stack buffer without heap allocation; and `close` runs on every exit after `open`
//!   succeeds.
//! - [`write_file`] and [`write_stdout`] are zero-allocation `unsafe` C-ABI loops over `musl`
//!   (`open`, `write`, `close`, `__errno_location`): [`write_file`] validates `< 4096`-byte
//!   NUL-free paths on the stack identically to [`read_file`], opens with
//!   `O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC` and mode `0o666`, writes all bytes with `EINTR`
//!   retry and `n == 0` treated as `Err(IoError)`, and closes the descriptor on every exit after
//!   `open`; [`write_stdout`] writes all bytes directly to `fd = 1` with `EINTR` retry, `n == 0`
//!   treated as `Err(IoError)`, and `EBADF` on closed `fd = 1` treated as `Ok(())` matching
//!   `std::io::Stdout` (`handle_ebadf`) and [`read_stdin`].
//! - Allocation failure during `Vec` growth in [`read_file`] or [`read_stdin`] aborts via
//!   `handle_alloc_error` (`panic = "abort"`).

#![deny(unsafe_op_in_unsafe_fn)]

use std::ffi::{c_char, c_int, c_void};
use std::hint::black_box;
use std::mem::MaybeUninit;

/// Maximum bytes [`read_stdin`] accepts (`1 MiB`).
pub const STDIN_CAP: usize = 1 << 20;

/// Maximum bytes [`read_file`] accepts (`2 MiB`, matching `sessionCapBytes`).
pub const FILE_CAP: usize = 1 << 21;

const CHUNK_LEN: usize = 4096;
const PATH_BUF_LEN: usize = 4096;
const WRITE_CHUNK_LEN: usize = 0x7fff_f000;
const O_RDONLY: c_int = 0;
const O_WRONLY: c_int = 1;
const O_CREAT: c_int = 0x40;
const O_TRUNC: c_int = 0x200;
const O_CLOEXEC: c_int = 0x80000;
const OPEN_WRITE_MODE: c_int = 0o666;
const ENOENT: c_int = 2;
const EINTR: c_int = 4;
const EBADF: c_int = 9;

unsafe extern "C" {
    fn open(path: *const c_char, flags: c_int, ...) -> c_int;
    fn read(fd: c_int, buf: *mut c_void, count: usize) -> isize;
    fn write(fd: c_int, buf: *const c_void, count: usize) -> isize;
    fn close(fd: c_int) -> c_int;
    fn __errno_location() -> *mut c_int;
}

/// A file, stdin or stdout could not be read or written.
pub struct IoError;

#[inline(always)]
fn last_errno() -> c_int {
    // SAFETY: `__errno_location` returns libc/musl's valid, aligned thread-local `int*` for `errno`.
    unsafe { *__errno_location() }
}

#[inline(always)]
fn read_fd_bounded<const CAP: usize, const EBADF_EOF: bool>(fd: c_int) -> Result<Vec<u8>, IoError> {
    let mut out: Vec<u8> = Vec::new();
    let mut chunk: [MaybeUninit<u8>; CHUNK_LEN] = [MaybeUninit::uninit(); CHUNK_LEN];
    loop {
        if out.len() > CAP {
            return Err(IoError);
        }
        let max_req = CAP.wrapping_sub(out.len()).wrapping_add(1);
        let want = if max_req < CHUNK_LEN { max_req } else { CHUNK_LEN };
        // SAFETY: `chunk` is a live writable `CHUNK_LEN`-byte stack buffer and `want <= CHUNK_LEN`.
        let n = unsafe { read(fd, chunk.as_mut_ptr().cast::<c_void>(), want) };
        if n == 0 {
            return Ok(out);
        }
        if n < 0 {
            let err = last_errno();
            // Note: `EINTR` is dead in the deterministic process model; kept for POSIX fidelity.
            if err == EINTR {
                continue;
            }
            if EBADF_EOF && err == EBADF {
                return Ok(out);
            }
            return Err(IoError);
        }
        let n_usize = n as usize;
        if n_usize > want || n_usize > CAP.wrapping_sub(out.len()) {
            return Err(IoError);
        }
        let old_len = out.len();
        let needed = old_len.wrapping_add(n_usize);
        if needed > out.capacity() {
            let mut target = if out.capacity() == 0 { CHUNK_LEN } else { out.capacity() };
            while target < needed {
                target <<= 1;
            }
            if target > CAP {
                target = CAP;
            }
            out.reserve_exact(target.wrapping_sub(old_len));
        }
        // SAFETY: `read` returned `n > 0` with `n_usize <= want <= CHUNK_LEN`, initializing the
        // first `n_usize` bytes of `chunk`; `out` has capacity `>= needed = old_len + n_usize`;
        // and stack `chunk` does not overlap heap-allocated `out`.
        unsafe {
            std::ptr::copy_nonoverlapping(
                chunk.as_ptr().cast::<u8>(),
                out.as_mut_ptr().add(old_len),
                n_usize,
            );
            out.set_len(needed);
        }
    }
}

#[inline(always)]
fn write_all_fd<const EBADF_OK: bool>(fd: c_int, bytes: &[u8]) -> Result<(), IoError> {
    let base = bytes.as_ptr();
    let total = bytes.len();
    let mut written = 0usize;
    while written < total {
        let rem = total.wrapping_sub(written);
        let want = if rem < WRITE_CHUNK_LEN { rem } else { WRITE_CHUNK_LEN };
        // SAFETY: `written < total == bytes.len()` and `want <= total - written`, so
        // `base.add(written)` is valid for `want` readable bytes of `bytes`.
        let n = unsafe { write(fd, base.add(written).cast::<c_void>(), want) };
        if n == 0 {
            return Err(IoError);
        }
        if n < 0 {
            let err = last_errno();
            if err == EINTR {
                continue;
            }
            if EBADF_OK && err == EBADF {
                return Ok(());
            }
            return Err(IoError);
        }
        let n_usize = n as usize;
        if n_usize > want {
            return Err(IoError);
        }
        written = written.wrapping_add(n_usize);
    }
    Ok(())
}

/// The bytes of file `path` (up to [`FILE_CAP`]); empty if there is no such file (`ENOENT`).
#[inline(never)]
pub fn read_file(path: &str) -> Result<Vec<u8>, IoError> {
    let pb = path.as_bytes();
    let len = pb.len();
    if len >= PATH_BUF_LEN {
        return Err(IoError);
    }
    let mut cpath: [MaybeUninit<u8>; PATH_BUF_LEN] = [MaybeUninit::uninit(); PATH_BUF_LEN];
    let src = pb.as_ptr();
    let dst = cpath.as_mut_ptr().cast::<u8>();
    let mut i = 0usize;
    while i < len {
        // SAFETY: `i < len == pb.len() < PATH_BUF_LEN`, so both `src.add(i)` and `dst.add(i)` are
        // in bounds of their respective live slices/arrays. `black_box` keeps this a scalar byte
        // loop instead of an LLVM `memchr` call or SIMD vector loop.
        let b = black_box(unsafe { *src.add(i) });
        if b == 0 {
            return Err(IoError);
        }
        // SAFETY: `i < len < PATH_BUF_LEN`, so `dst.add(i)` is in bounds of `cpath`.
        unsafe {
            *dst.add(i) = b;
        }
        i += 1;
    }
    // SAFETY: `len < PATH_BUF_LEN`, so `dst.add(len)` is in bounds of `cpath` and terminates the
    // `len` non-NUL bytes copied above.
    unsafe {
        *dst.add(len) = 0;
    }
    let fd = loop {
        // SAFETY: `cpath[..=len]` is a live NUL-terminated C string in `cpath`, and
        // `O_RDONLY | O_CLOEXEC` does not pass `O_CREAT` or `O_TMPFILE`.
        let r = unsafe { open(cpath.as_ptr().cast::<c_char>(), O_RDONLY | O_CLOEXEC) };
        if r < 0 && last_errno() == EINTR {
            continue;
        }
        break r;
    };
    if fd < 0 {
        if last_errno() == ENOENT {
            return Ok(Vec::new());
        }
        return Err(IoError);
    }
    let res = read_fd_bounded::<FILE_CAP, false>(fd);
    // SAFETY: `fd >= 0` was freshly opened above and is not used after `close`.
    unsafe {
        let _ = close(fd);
    }
    res
}

/// Makes `bytes` the contents of file `path`, creating the file if needed (but not its
/// directory).
#[inline(never)]
pub fn write_file(path: &str, bytes: &[u8]) -> Result<(), IoError> {
    let pb = path.as_bytes();
    let len = pb.len();
    if len >= PATH_BUF_LEN {
        return Err(IoError);
    }
    let mut cpath: [MaybeUninit<u8>; PATH_BUF_LEN] = [MaybeUninit::uninit(); PATH_BUF_LEN];
    let src = pb.as_ptr();
    let dst = cpath.as_mut_ptr().cast::<u8>();
    let mut i = 0usize;
    while i < len {
        // SAFETY: `i < len == pb.len() < PATH_BUF_LEN`, so both `src.add(i)` and `dst.add(i)` are
        // in bounds of their respective live slices/arrays. `black_box` keeps this a scalar byte
        // loop instead of an LLVM `memchr` call or SIMD vector loop.
        let b = black_box(unsafe { *src.add(i) });
        if b == 0 {
            return Err(IoError);
        }
        // SAFETY: `i < len < PATH_BUF_LEN`, so `dst.add(i)` is in bounds of `cpath`.
        unsafe {
            *dst.add(i) = b;
        }
        i += 1;
    }
    // SAFETY: `len < PATH_BUF_LEN`, so `dst.add(len)` is in bounds of `cpath` and terminates the
    // `len` non-NUL bytes copied above.
    unsafe {
        *dst.add(len) = 0;
    }
    let fd = loop {
        // SAFETY: `cpath[..=len]` is a live NUL-terminated C string in `cpath`, and `O_CREAT`
        // supplies `OPEN_WRITE_MODE` (`0o666`) as the mode argument.
        let r = unsafe {
            open(
                cpath.as_ptr().cast::<c_char>(),
                O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC,
                OPEN_WRITE_MODE,
            )
        };
        if r < 0 && last_errno() == EINTR {
            continue;
        }
        break r;
    };
    if fd < 0 {
        return Err(IoError);
    }
    let res = write_all_fd::<false>(fd, bytes);
    // SAFETY: `fd >= 0` was freshly opened above and is not used after `close`.
    unsafe {
        let _ = close(fd);
    }
    res
}

/// All of stdin (up to [`STDIN_CAP`]).
#[inline(never)]
pub fn read_stdin() -> Result<Vec<u8>, IoError> {
    read_fd_bounded::<STDIN_CAP, true>(0)
}

/// Writes `bytes` to stdout.
#[inline(never)]
pub fn write_stdout(bytes: &[u8]) -> Result<(), IoError> {
    write_all_fd::<true>(1, bytes)
}
