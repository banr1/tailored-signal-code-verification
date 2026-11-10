// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Differential validation of cooperative POSIX file-system `SVC #0` syscalls in
//! Unicorn (`UC_ARCH_ARM64`) backed by real Linux kernel VFS syscalls and cross-checked
//! step-by-step against Lean's `execSyscall` evaluator (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (validates the Linux AArch64 syscall numbers, flag masks,
//!   128-byte `struct stat` field layout, error codes, and file-descriptor state transitions
//!   modeled in `Arm64/Trusted/ISA/{State,Eval}.lean` against both the host Linux kernel and
//!   Lean's compiled `diff_eval --fs-diff-trace` evaluator).

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ffi::c_void;
use std::fs::{self, File, OpenOptions, Permissions};
use std::io::Read;
use std::mem::{offset_of, size_of};
use std::os::linux::fs::MetadataExt as LinuxMetadataExt;
use std::os::unix::fs::{FileExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::ptr::{null_mut, read_volatile, write_volatile};
use std::rc::Rc;

use unicorn_engine::unicorn_const::{Arch, Mode, Permission};
use unicorn_engine::{RegisterARM64, Unicorn};

const SYS_FCNTL: u64 = 25;
const SYS_IOCTL: u64 = 29;
const SYS_OPENAT: u64 = 56;
const SYS_CLOSE: u64 = 57;
const SYS_LSEEK: u64 = 62;
const SYS_READ: u64 = 63;
const SYS_WRITE: u64 = 64;
const SYS_PREAD64: u64 = 67;
const SYS_FSTAT: u64 = 80;
const SYS_CLOCK_GETTIME: u64 = 113;

unsafe extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
    fn ioctl(fd: i32, request: u64, arg: u64) -> i32;
    fn lseek64(fd: i32, offset: i64, whence: i32) -> i64;
    #[link_name = "read"]
    fn host_read(fd: i32, buf: *mut c_void, count: usize) -> isize;
}

/// Canonical 128-byte Linux AArch64 `asm-generic` `struct stat` ABI layout.
#[repr(C)]
#[derive(Clone, Copy)]
struct Aarch64LinuxStat {
    st_dev: u64,
    st_ino: u64,
    st_mode: u32,
    st_nlink: u32,
    st_uid: u32,
    st_gid: u32,
    st_rdev: u64,
    __pad1: u64,
    st_size: i64,
    st_blksize: i32,
    __pad2: i32,
    st_blocks: i64,
    st_times: [u8; 56],
}

const _: () = assert!(size_of::<Aarch64LinuxStat>() == 128);
const _: () = assert!(offset_of!(Aarch64LinuxStat, st_mode) == 16);
const _: () = assert!(offset_of!(Aarch64LinuxStat, st_nlink) == 20);
const _: () = assert!(offset_of!(Aarch64LinuxStat, st_size) == 48);
const _: () = assert!(offset_of!(Aarch64LinuxStat, st_blksize) == 56);
const _: () = assert!(offset_of!(Aarch64LinuxStat, st_blocks) == 64);

impl Aarch64LinuxStat {
    /// Populate the 128-byte AArch64 Linux `struct stat` directly from kernel `Metadata`
    /// returned by host `fstat` / `lstat` (`fs::Metadata`).
    fn from_kernel_metadata(meta: &fs::Metadata) -> [u8; 128] {
        let blocks = if (meta.st_mode() & 0o170000) == 0o040000 {
            0
        } else {
            ((meta.st_size() + 511) / 512) as i64
        };
        let stat = Self {
            st_dev: meta.st_dev(),
            st_ino: meta.st_ino(),
            st_mode: meta.st_mode(),
            st_nlink: meta.st_nlink() as u32,
            st_uid: meta.st_uid(),
            st_gid: meta.st_gid(),
            st_rdev: meta.st_rdev(),
            __pad1: 0,
            st_size: meta.st_size() as i64,
            st_blksize: meta.st_blksize() as i32,
            __pad2: 0,
            st_blocks: blocks,
            st_times: [0u8; 56],
        };
        // SAFETY: `Aarch64LinuxStat` is a `#[repr(C)]` plain-old-data struct of exact size 128 bytes
        // with all padding fields explicitly zero-initialized.
        unsafe { core::mem::transmute::<Self, [u8; 128]>(stat) }
    }
}

struct HostLinuxFs {
    root: PathBuf,
    fds: BTreeMap<u64, File>,
    guard_page: *mut c_void,
}

impl HostLinuxFs {
    fn new(root: PathBuf) -> Self {
        // SAFETY: Maps a single 4 KiB `PROT_NONE` anonymous page in user space (`< TASK_SIZE`)
        // to mirror in-range unmapped guest pointers (`0x90000`) when probing host `read`/`write`.
        let guard_page = unsafe { mmap(null_mut(), 0x1000, 0, 0x22, -1, 0) };
        assert_ne!(guard_page as isize, -1, "mmap of PROT_NONE guard page failed");
        Self {
            root,
            fds: BTreeMap::new(),
            guard_page,
        }
    }
}

impl Drop for HostLinuxFs {
    fn drop(&mut self) {
        // SAFETY: Unmaps the 4 KiB `PROT_NONE` page allocated in `HostLinuxFs::new`.
        unsafe {
            let _ = munmap(self.guard_page, 0x1000);
        }
    }
}

impl HostLinuxFs {

    fn alloc_fd(&self) -> u64 {
        for fd in 3..1024u64 {
            if !self.fds.contains_key(&fd) {
                return fd;
            }
        }
        u64::MAX
    }

    fn resolve_guest_path(&self, raw: &str) -> Result<PathBuf, i64> {
        if raw.is_empty() {
            return Err(-2); // -ENOENT
        }
        assert!(
            !raw.starts_with('/'),
            "expected CWD-relative guest path in FS differential test, got {raw:?}"
        );
        Ok(self.root.join(raw))
    }
}

fn read_guest_c_string(uc: &Unicorn<'_, ()>, ptr: u64) -> Result<String, i64> {
    let mut bytes = Vec::new();
    for i in 0..4096u64 {
        let mut b = [0u8; 1];
        uc.mem_read(ptr.wrapping_add(i), &mut b)
            .map_err(|_| -14i64)?;
        if b[0] == 0 {
            return String::from_utf8(bytes).map_err(|_| -2i64);
        }
        bytes.push(b[0]);
    }
    Err(-36) // -ENAMETOOLONG
}

fn dispatch_linux_fs_syscall(
    uc: &mut Unicorn<'_, ()>,
    fs_hook: &RefCell<HostLinuxFs>,
    sysno: u64,
    a0: u64,
    a1: u64,
    a2: u64,
    a3: u64,
) -> i64 {
    let raw_fd_i32 = a0 as i32;
    let guest_fd = a0 as u32 as u64;
    match sysno {
        SYS_FCNTL => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let host_fd = fs_hook
                .borrow()
                .fds
                .get(&guest_fd)
                .map(|f| f.as_raw_fd())
                .unwrap_or(-1);
            // SAFETY: Calls host Linux `fcntl(2)` directly; returns `-EBADF` (-9) when
            // `host_fd == -1`, `0` on `F_SETFD`, and `FD_CLOEXEC` (1) on `F_GETFD` after
            // an `O_CLOEXEC` open.
            let rc = unsafe { fcntl(host_fd, a1 as i32, a2) };
            if rc < 0 {
                -(std::io::Error::last_os_error().raw_os_error().unwrap_or(9) as i64)
            } else {
                rc as i64
            }
        }
        SYS_IOCTL => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let host_fd = fs_hook
                .borrow()
                .fds
                .get(&guest_fd)
                .map(|f| f.as_raw_fd())
                .unwrap_or(-1);
            // SAFETY: Calls host Linux `ioctl(2)` directly; when `host_fd == -1` the kernel
            // returns `-1` with `errno = EBADF` (-9), and on an open regular file returns
            // `-1` with `errno = ENOTTY` (-25).
            let rc = unsafe { ioctl(host_fd, a1, a2) };
            if rc < 0 {
                -(std::io::Error::last_os_error().raw_os_error().unwrap_or(9) as i64)
            } else {
                rc as i64
            }
        }
        SYS_CLOCK_GETTIME => {
            uc.mem_write(a1, &[0u8; 16]).unwrap();
            0
        }
        SYS_OPENAT => match read_guest_c_string(uc, a1) {
            Err(e) => e,
            Ok(raw) => {
                let mut fs = fs_hook.borrow_mut();
                match fs.resolve_guest_path(&raw) {
                    Err(e) => e,
                    Ok(host_path) => {
                        let flags = a2 as u32;
                        let acc = flags & 3;
                        let mut opts = OpenOptions::new();
                        opts.read(acc == 0 || acc == 2);
                        opts.write(acc == 1 || acc == 2);
                        if (flags & 0x40) != 0 {
                            opts.mode((a3 as u32) & 0o7777);
                            if (flags & 0x80) != 0 {
                                opts.create_new(true);
                            } else {
                                opts.create(true);
                            }
                        }
                        if (flags & 0x200) != 0 {
                            opts.truncate(true);
                        }
                        if (flags & 0x400) != 0 {
                            opts.append(true);
                        }
                        opts.custom_flags((flags & 0x80000) as i32);
                        match opts.open(&host_path) {
                            Err(err) => -(err.raw_os_error().unwrap_or(5) as i64),
                            Ok(file) => {
                                if (flags & 0x80000) == 0 {
                                    // Rust's `std::fs::OpenOptions` adds `O_CLOEXEC` by default;
                                    // clear `FD_CLOEXEC` when guest `openat(2)` omitted `O_CLOEXEC`.
                                    let rc = unsafe { fcntl(file.as_raw_fd(), 2, 0u64) };
                                    assert_eq!(rc, 0, "clear OpenOptions default FD_CLOEXEC");
                                }
                                let fd = fs.alloc_fd();
                                fs.fds.insert(fd, file);
                                fd as i64
                            }
                        }
                    }
                }
            }
        },
        SYS_CLOSE => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let mut fs = fs_hook.borrow_mut();
            match fs.fds.remove(&guest_fd) {
                None => -9, // -EBADF
                Some(file) => {
                    drop(file);
                    0
                }
            }
        }
        SYS_LSEEK => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let fs = fs_hook.borrow();
            match fs.fds.get(&guest_fd) {
                None => -9,
                Some(file) => {
                    // SAFETY: Calls host Linux `lseek64(2)` directly using the guest `offset` (`a1 as i64`)
                    // and `whence` (`a2 as i32`).
                    let pos = unsafe { lseek64(file.as_raw_fd(), a1 as i64, a2 as i32) };
                    if pos < 0 {
                        -(std::io::Error::last_os_error().raw_os_error().unwrap_or(22) as i64)
                    } else {
                        pos
                    }
                }
            }
        }
        SYS_READ => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let mut fs = fs_hook.borrow_mut();
            let guard_page = fs.guard_page;
            match fs.fds.get_mut(&guest_fd) {
                None => -9,
                Some(file) => {
                    let mut probe = [0u8; 1];
                    if a2 >= (1u64 << 48) || uc.mem_read(a1, &mut probe).is_err() {
                        // SAFETY: Passes the in-range `PROT_NONE` host user page (`guard_page`)
                        // and `a2` directly to host `read(2)` so `access_ok` (`-EFAULT` on
                        // `a2 >= TASK_SIZE`) and `generic_read_dir` (`-EISDIR` on in-range
                        // unmapped `buf`) are exercised in the real Linux kernel.
                        let rc = unsafe { host_read(file.as_raw_fd(), guard_page, a2 as usize) };
                        if rc < 0 {
                            -(std::io::Error::last_os_error().raw_os_error().unwrap_or(9) as i64)
                        } else {
                            rc as i64
                        }
                    } else {
                        let mut buf = vec![0u8; a2 as usize];
                        match file.read(&mut buf) {
                            Err(e) => -(e.raw_os_error().unwrap_or(9) as i64),
                            Ok(n) => {
                                uc.mem_write(a1, &buf[..n]).unwrap();
                                n as i64
                            }
                        }
                    }
                }
            }
        }
        SYS_PREAD64 => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let fs = fs_hook.borrow();
            match fs.fds.get(&guest_fd) {
                None => -9,
                Some(file) => {
                    let mut buf = vec![0u8; a2 as usize];
                    match file.read_at(&mut buf, a3) {
                        Err(e) => -(e.raw_os_error().unwrap_or(22) as i64),
                        Ok(n) => {
                            uc.mem_write(a1, &buf[..n]).unwrap();
                            n as i64
                        }
                    }
                }
            }
        }
        SYS_WRITE => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let fs = fs_hook.borrow();
            let guard_page = fs.guard_page;
            match fs.fds.get(&guest_fd) {
                None => -9,
                Some(file) => {
                    let mut probe = [0u8; 1];
                    if a2 >= (1u64 << 48) || uc.mem_read(a1, &mut probe).is_err() {
                        // SAFETY: Passes the in-range `PROT_NONE` host user page (`guard_page`)
                        // and `a2` directly to host `write(2)` so `access_ok`, 0-byte writes,
                        // and `rw_verify_area` (`-EINVAL` before `copy_from_user`) are exercised
                        // in the real Linux kernel.
                        let rc = unsafe {
                            host_write(file.as_raw_fd(), guard_page.cast_const(), a2 as usize)
                        };
                        if rc < 0 {
                            -(std::io::Error::last_os_error().raw_os_error().unwrap_or(9) as i64)
                        } else {
                            rc as i64
                        }
                    } else {
                        let mut buf = vec![0u8; a2 as usize];
                        uc.mem_read(a1, &mut buf).unwrap();
                        // SAFETY: Calls host Linux `write(2)` directly so 0-byte writes,
                        // directory-fd writes (`-EBADF`), and `MAX_LFS_FILESIZE` writes (`-EINVAL`)
                        // go through the real kernel syscall path.
                        let rc = unsafe {
                            host_write(file.as_raw_fd(), buf.as_ptr().cast::<c_void>(), buf.len())
                        };
                        if rc < 0 {
                            -(std::io::Error::last_os_error().raw_os_error().unwrap_or(9) as i64)
                        } else {
                            rc as i64
                        }
                    }
                }
            }
        }
        SYS_FSTAT => {
            if raw_fd_i32 < 0 {
                return -9;
            }
            let fs = fs_hook.borrow();
            match fs.fds.get(&guest_fd) {
                None => -9,
                Some(file) => match file.metadata() {
                    Err(e) => -(e.raw_os_error().unwrap_or(9) as i64),
                    Ok(meta) => {
                        let bytes = Aarch64LinuxStat::from_kernel_metadata(&meta);
                        uc.mem_write(a1, &bytes).unwrap();
                        0
                    }
                },
            }
        }
        other => panic!("unexpected syscall {other}"),
    }
}

fn run_aarch64_with_linux_fs(
    code_words: &[u32],
    entry_pc: u64,
    exit_pc: u64,
    init_sp: u64,
    init_mem: &[(u64, &[u8])],
    init_regs: &[(RegisterARM64, u64)],
    fs_state: Rc<RefCell<HostLinuxFs>>,
) -> (Unicorn<'static, ()>, u64) {
    let mut uc = Unicorn::new(Arch::ARM64, Mode::LITTLE_ENDIAN).expect("create Unicorn AArch64");
    uc.mem_map(0x1000, 0x1000, Permission::ALL)
        .expect("map code page");
    uc.mem_map(0x2000, 0x2000, Permission::ALL)
        .expect("map data page");
    uc.mem_map(0x7000, 0x2000, Permission::ALL)
        .expect("map stack page");

    let code_bytes: Vec<u8> = code_words.iter().flat_map(|w| w.to_le_bytes()).collect();
    uc.mem_write(entry_pc, &code_bytes).expect("write code");
    for (addr, data) in init_mem {
        uc.mem_write(*addr, data).expect("write init mem");
    }

    uc.reg_write(RegisterARM64::SP, init_sp).unwrap();
    uc.reg_write(RegisterARM64::X30, exit_pc).unwrap();
    for (reg, val) in init_regs {
        uc.reg_write(*reg, *val).unwrap();
    }

    let fs_hook = Rc::clone(&fs_state);
    uc.add_intr_hook(move |uc, _intno| {
        let sysno = uc.reg_read(RegisterARM64::X8).unwrap();
        let a0 = uc.reg_read(RegisterARM64::X0).unwrap();
        let a1 = uc.reg_read(RegisterARM64::X1).unwrap();
        let a2 = uc.reg_read(RegisterARM64::X2).unwrap();
        let a3 = uc.reg_read(RegisterARM64::X3).unwrap();
        let ret = dispatch_linux_fs_syscall(uc, &fs_hook, sysno, a0, a1, a2, a3);
        uc.reg_write(RegisterARM64::X0, ret as u64).unwrap();
    })
    .expect("add SVC hook");

    uc.emu_start(entry_pc, exit_pc, 0, 10_000)
        .expect("run Unicorn guest code to completion");
    let final_x0 = uc.reg_read(RegisterARM64::X0).unwrap();
    (uc, final_x0)
}

fn lean_diff_eval_bin() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("locate repo root");
    crate::ensure_diff_eval_bin(repo_root, None).expect("ensure `diff_eval` binary")
}

/// Executes the compiled 29-instruction AArch64 `c_read_file_loop` machine code against
/// real Linux kernel files (empty, 7B, exact 64B chunk boundary, 150B multi-chunk loop,
/// and missing path -> `-ENOENT`) and verifies exact agreement with the Lean model.
#[test]
fn c_read_file_loop_matches_linux_kernel() {
    let c_read_file_loop_words: [u32; 29] = [
        0xaa0003e1, 0x92800c60, 0x52800708, 0xaa1f03e2, 0xaa1f03e3, 0xd4000001, 0xaa0003e9,
        0xb7f80280, 0xd10103ff, 0xaa1f03eb, 0xaa0903e0, 0x910003e1, 0x528007e8, 0x52800802,
        0xd4000001, 0xaa0b03ea, 0xf100001f, 0x8b0b000b, 0x54ffff0c, 0xaa0903e0, 0x52800728,
        0xaa1f03e1, 0xaa1f03e2, 0xd4000001, 0x910103ff, 0xaa0a03e0, 0xd65f03c0, 0xaa0903e0,
        0xd65f03c0,
    ];

    let tmp = tempfile::tempdir().expect("create tempdir");
    for len in [0usize, 7, 64, 150] {
        let name = format!("sample_{len}.bin");
        let payload: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(13)).collect();
        fs::write(tmp.path().join(&name), &payload).expect("seed host file");

        let fs_state = Rc::new(RefCell::new(HostLinuxFs::new(tmp.path().to_path_buf())));
        let mut cstr = name.into_bytes();
        cstr.push(0);

        let (uc, ret) = run_aarch64_with_linux_fs(
            &c_read_file_loop_words,
            0x1000,
            0x1ffc,
            0x8000,
            &[(0x2000, &cstr)],
            &[(RegisterARM64::X0, 0x2000)],
            Rc::clone(&fs_state),
        );
        assert_eq!(ret, len as u64, "c_read_file_loop byte total for len={len}");
        assert_eq!(
            uc.reg_read(RegisterARM64::SP).unwrap(),
            0x8000,
            "SP restored"
        );
        assert!(
            fs_state.borrow().fds.is_empty(),
            "all file descriptors closed after loop"
        );
    }

    // Missing file returns -ENOENT (-2) and leaves FD table empty
    let fs_missing = Rc::new(RefCell::new(HostLinuxFs::new(tmp.path().to_path_buf())));
    let (_uc, err_ret) = run_aarch64_with_linux_fs(
        &c_read_file_loop_words,
        0x1000,
        0x1ffc,
        0x8000,
        &[(0x2000, b"does_not_exist\0")],
        &[(RegisterARM64::X0, 0x2000)],
        Rc::clone(&fs_missing),
    );
    assert_eq!(err_ret as i64, -2, "missing file returns -ENOENT (-2)");
    assert!(fs_missing.borrow().fds.is_empty());
}

/// Validates every modeled FS syscall (`ioctl`, `clock_gettime`, `openat`, `fstat`, `pread64`,
/// `read`, `lseek` across `SEEK_END`/`SEEK_CUR`/`SEEK_SET`, `close`, `write`, `fcntl` across
/// `F_GETFD`/`F_SETFD`) directly between real host Linux kernel syscalls and Lean's `execSyscall`
/// evaluator (`diff_eval --fs-diff-trace`).
#[test]
fn fs_syscall_trace_matches_linux_kernel() {
    // Prefer `/dev/shm` (`tmpfs`, where `sb->s_maxbytes == MAX_LFS_FILESIZE == LLONG_MAX`) over
    // `/tmp` (which on CI runners may be `ext4` with `s_maxbytes = 16 TiB < MAX_LFS_FILESIZE`).
    let tmp = tempfile::tempdir_in("/dev/shm")
        .or_else(|_| tempfile::tempdir())
        .expect("create tempdir");
    let path_a = tmp.path().join("a");
    let path_d = tmp.path().join("d");
    fs::write(&path_a, b"ABCDEFG").expect("seed a");
    fs::set_permissions(&path_a, Permissions::from_mode(0o644)).expect("chmod 0644 a");
    fs::create_dir(&path_d).expect("seed d");
    fs::set_permissions(&path_d, Permissions::from_mode(0o755)).expect("chmod 0755 d");

    let fs_state = Rc::new(RefCell::new(HostLinuxFs::new(tmp.path().to_path_buf())));
    let svc_ret = [0xd4000001u32, 0xd65f03c0u32]; // svc #0; ret

    let run_one = |sysno: u64, a0: i64, a1: u64, a2: i64, a3: u64| -> (Unicorn<'static, ()>, i64) {
        let (uc, x0) = run_aarch64_with_linux_fs(
            &svc_ret,
            0x1000,
            0x1ffc,
            0x8000,
            &[
                (0x2000, b"a\0"),
                (0x2010, b"b\0"),
                (0x2020, b"d\0"),
                (0x2030, b"missing/x\0"),
                (0x2050, b"a/x\0"),
                (0x2070, b"d/sub\0"),
                (0x2090, b".//d//sub\0"),
                (0x20b0, b"<stdin>\0"),
                (0x20c0, b"<stdout>\0"),
                (0x20d0, b"<stderr>\0"),
                (0x2180, b"xyz!"),
            ],
            &[
                (RegisterARM64::X8, sysno),
                (RegisterARM64::X0, a0 as u64),
                (RegisterARM64::X1, a1),
                (RegisterARM64::X2, a2 as u64),
                (RegisterARM64::X3, a3),
            ],
            Rc::clone(&fs_state),
        );
        (uc, x0 as i64)
    };

    // Probe directory `openat(O_RDONLY)` and `openat(O_RDONLY | O_CLOEXEC)` -> `fstat` ->
    // `read` (-EISDIR) -> `write` (-EBADF) -> `fcntl(F_GETFD / F_SETFD)` -> `close`
    // on empty `0755` directory `"d"` before creating `"d/sub"`, plus verify `openat` on
    // `"<stdin>"` / `"<stdout>"` / `"<stderr>"` returns `-ENOENT` (-2) on host Linux.
    let open_dir_d = run_one(SYS_OPENAT, -100, 0x2020, 0, 0).1;
    assert_eq!(open_dir_d, 3, "open host directory d for fstat probe");
    assert!(fs_state.borrow().fds.contains_key(&3));
    let (uc_dir_stat, dir_fstat_ret_i64) = run_one(SYS_FSTAT, 3, 0x2400, 0, 0);
    let mut dir_mode_bytes = [0u8; 4];
    let mut dir_nlink_bytes = [0u8; 4];
    let mut dir_blksize_bytes = [0u8; 4];
    uc_dir_stat.mem_read(0x2410, &mut dir_mode_bytes).unwrap();
    uc_dir_stat.mem_read(0x2414, &mut dir_nlink_bytes).unwrap();
    uc_dir_stat.mem_read(0x2438, &mut dir_blksize_bytes).unwrap();
    let dir_read_ret = run_one(SYS_READ, 3, 0x2100, 1, 0).1 as i128;
    let dir_read_unm_ret = run_one(SYS_READ, 3, 0x90000, 4, 0).1 as i128;
    let dir_read_efault_ret = run_one(SYS_READ, 3, 0x2100, (1u64 << 63) as i64, 0).1 as i128;
    assert_eq!(dir_read_unm_ret, -21, "in-range unmapped read on dir fd must return -EISDIR (-21)");
    assert_eq!(dir_read_efault_ret, -14, "out-of-range count=2^63 read on dir fd must return -EFAULT (-14)");
    let dir_write_ret = run_one(SYS_WRITE, 3, 0x2180, 1, 0).1 as i128;
    let dir_getfd0 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let dir_setfd1 = run_one(SYS_FCNTL, 3, 2, 1, 0).1 as i128;
    let dir_getfd1 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let dir_setfd0 = run_one(SYS_FCNTL, 3, 2, 0, 0).1 as i128;
    let dir_getfd2 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    assert_eq!(
        (dir_getfd0, dir_setfd1, dir_getfd1, dir_setfd0, dir_getfd2),
        (0, 0, 1, 0, 0),
        "host Linux fcntl F_GETFD/F_SETFD on O_RDONLY directory fd"
    );
    let dir_close_ret = run_one(SYS_CLOSE, 3, 0, 0, 0).1 as i128;
    assert_eq!(
        dir_close_ret, 0,
        "close temporary directory fd before O_CLOEXEC directory probe"
    );
    assert!(fs_state.borrow().fds.is_empty());
    let open_dir_d_clo = run_one(SYS_OPENAT, -100, 0x2020, 0x80000, 0).1 as i128;
    assert_eq!(open_dir_d_clo, 3, "open host directory d with O_RDONLY | O_CLOEXEC");
    assert!(fs_state.borrow().fds.contains_key(&3));
    let dir_clo_getfd0 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let dir_clo_setfd0 = run_one(SYS_FCNTL, 3, 2, 0, 0).1 as i128;
    let dir_clo_getfd1 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let dir_clo_setfd1 = run_one(SYS_FCNTL, 3, 2, 1, 0).1 as i128;
    let dir_clo_getfd2 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    assert_eq!(
        (dir_clo_getfd0, dir_clo_setfd0, dir_clo_getfd1, dir_clo_setfd1, dir_clo_getfd2),
        (1, 0, 0, 0, 1),
        "host Linux fcntl F_GETFD/F_SETFD on O_RDONLY | O_CLOEXEC directory fd"
    );
    let dir_clo_close_ret = run_one(SYS_CLOSE, 3, 0, 0, 0).1 as i128;
    assert_eq!(dir_clo_close_ret, 0, "close O_CLOEXEC directory fd before main trace");
    assert!(fs_state.borrow().fds.is_empty());
    let dir_clo_closed_get = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    assert_eq!(dir_clo_closed_get, -9, "F_GETFD on closed directory fd must return -EBADF (-9)");
    let open_stdin = run_one(SYS_OPENAT, -100, 0x20b0, 0, 0).1 as i128;
    let open_stdout = run_one(SYS_OPENAT, -100, 0x20c0, 0, 0).1 as i128;
    let open_stderr = run_one(SYS_OPENAT, -100, 0x20d0, 0, 0).1 as i128;

    let ioctl_closed = run_one(SYS_IOCTL, 3, 0x5401, 0x2100, 0).1 as i128;
    let clock_ret = run_one(SYS_CLOCK_GETTIME, 1, 0x2280, 0, 0).1 as i128;
    let open_miss = run_one(SYS_OPENAT, -100, 0x2010, 0, 0).1 as i128;
    let open_a = run_one(SYS_OPENAT, -100, 0x2000, 0, 0).1 as i128;
    let ioctl_open = run_one(SYS_IOCTL, 3, 0x5401, 0x2100, 0).1 as i128;

    let (uc_stat, fstat_ret_i64) = run_one(SYS_FSTAT, 3, 0x2200, 0, 0);
    let mut mode_bytes = [0u8; 4];
    let mut nlink_bytes = [0u8; 4];
    let mut size_bytes = [0u8; 8];
    let mut blksize_bytes = [0u8; 4];
    let mut blocks_bytes = [0u8; 8];
    uc_stat.mem_read(0x2210, &mut mode_bytes).unwrap();
    uc_stat.mem_read(0x2214, &mut nlink_bytes).unwrap();
    uc_stat.mem_read(0x2230, &mut size_bytes).unwrap();
    uc_stat.mem_read(0x2238, &mut blksize_bytes).unwrap();
    uc_stat.mem_read(0x2240, &mut blocks_bytes).unwrap();

    let (uc_pread, pread_ret) = run_one(SYS_PREAD64, 3, 0x2100, 4, 2);
    let mut pread_buf = [0u8; 4];
    uc_pread.mem_read(0x2100, &mut pread_buf).unwrap();
    assert_eq!(&pread_buf, b"CDEF");

    let (uc_r1, r1) = run_one(SYS_READ, 3, 0x2110, 5, 0);
    let mut r1_buf = [0u8; 5];
    uc_r1.mem_read(0x2110, &mut r1_buf).unwrap();
    assert_eq!(&r1_buf, b"ABCDE");

    let (uc_r2, r2) = run_one(SYS_READ, 3, 0x2120, 5, 0);
    let mut r2_buf = [0u8; 2];
    uc_r2.mem_read(0x2120, &mut r2_buf).unwrap();
    assert_eq!(&r2_buf, b"FG");

    let r3 = run_one(SYS_READ, 3, 0x2130, 5, 0).1;
    let lseek_end = run_one(SYS_LSEEK, 3, (-2i64) as u64, 2, 0).1;
    let lseek_cur = run_one(SYS_LSEEK, 3, (-1i64) as u64, 1, 0).1;
    let lseek_set = run_one(SYS_LSEEK, 3, 2, 0, 0).1;
    let close_ret = run_one(SYS_CLOSE, 3, 0, 0, 0).1;
    let read_closed = run_one(SYS_READ, 3, 0x2100, 1, 0).1;

    let open_creat = run_one(SYS_OPENAT, -100, 0x2010, 0x241, 0o644).1;
    let write_ret = run_one(SYS_WRITE, 3, 0x2180, 4, 0).1;
    let open_excl = run_one(SYS_OPENAT, -100, 0x2010, 0xc1, 0o644).1;

    let (uc_fstat_b, fstat_b_ret) = run_one(SYS_FSTAT, 3, 0x2300, 0, 0);
    uc_fstat_b.mem_read(0x2330, &mut size_bytes).unwrap();
    let fstat_b_size = u64::from_le_bytes(size_bytes) as i128;

    let fcntl_getfd0 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let fcntl_setfd = run_one(SYS_FCNTL, 3, 2, 1, 0).1 as i128;
    let fcntl_getfd1 = run_one(SYS_FCNTL, 3, 1, 0, 0).1 as i128;
    let fcntl_badfd = run_one(SYS_FCNTL, 9, 2, 1, 0).1 as i128;
    let open_miss_par = run_one(SYS_OPENAT, -100, 0x2030, 0x241, 0o644).1 as i128;
    let open_file_par = run_one(SYS_OPENAT, -100, 0x2050, 0x241, 0o644).1 as i128;
    let open_dir_sub = run_one(SYS_OPENAT, -100, 0x2070, 0x241, 0o644).1 as i128;
    let open_norm_sub = run_one(SYS_OPENAT, -100, 0x2090, 0x80000, 0).1 as i128;
    // A 0-byte write at an offset past the end leaves the file unchanged (no zero padding), and
    // `O_TRUNC` on an existing non-empty file (`b`, "xyz!") empties it.
    let lseek_past_end = run_one(SYS_LSEEK, 4, 10, 0, 0).1 as i128;
    let write_zero = run_one(SYS_WRITE, 4, 0x2180, 0, 0).1 as i128;
    let (uc_fstat_n, fstat_n_ret) = run_one(SYS_FSTAT, 4, 0x2600, 0, 0);
    let mut fstat_n_size = [0u8; 8];
    uc_fstat_n.mem_read(0x2630, &mut fstat_n_size).unwrap();
    let open_trunc = run_one(SYS_OPENAT, -100, 0x2010, 0x201, 0).1 as i128;
    let (uc_fstat_b2, fstat_b2_ret) = run_one(SYS_FSTAT, 6, 0x2680, 0, 0);
    let mut fstat_b2_size = [0u8; 8];
    uc_fstat_b2.mem_read(0x26b0, &mut fstat_b2_size).unwrap();
    let host_getfd_after_cloexec = run_one(SYS_FCNTL, 5, 1, 0, 0).1 as i128;
    assert_eq!(
        host_getfd_after_cloexec, 1,
        "host Linux F_GETFD after O_CLOEXEC open must return FD_CLOEXEC = 1"
    );
    // `FS_SAFE_MAX_FILESIZE - 1` (`0xfffffffe`) boundary: the model fails closed on `lseek` offsets
    // `>= FS_SAFE_MAX_FILESIZE` (the kernel's answer depends on the filesystem's `s_maxbytes`), so
    // only offsets below it are compared. A 0-byte write there returns 0 (even for an in-range
    // unmapped buffer), and an `O_APPEND` 1-byte write ignores `f_pos` and writes at EOF.
    let lseek_fs_safe = run_one(SYS_LSEEK, 4, 0xffff_fffe, 0, 0).1 as i128;
    let write_fs_safe_zero = run_one(SYS_WRITE, 4, 0x2180, 0, 0).1 as i128;
    let write_fs_safe_zero_unm = run_one(SYS_WRITE, 4, 0x90000, 0, 0).1 as i128;
    let open_append_b = run_one(SYS_OPENAT, -100, 0x2010, 0x401, 0).1 as i128;
    let lseek_append_fs_safe = run_one(SYS_LSEEK, 7, 0xffff_fffe, 0, 0).1 as i128;
    let write_append_fs_safe_one = run_one(SYS_WRITE, 7, 0x2180, 1, 0).1 as i128;
    assert_eq!(
        write_fs_safe_zero_unm, 0,
        "0-byte write with in-range unmapped buf must return 0, got {write_fs_safe_zero_unm}"
    );
    assert_eq!(
        write_append_fs_safe_one, 1,
        "1-byte O_APPEND write must write at EOF and return 1, got {write_append_fs_safe_one}"
    );

    let kernel_vals: Vec<i128> = vec![
        ioctl_closed,
        clock_ret,
        open_miss,
        open_a,
        ioctl_open,
        fstat_ret_i64 as i128,
        u32::from_le_bytes(mode_bytes) as i128,
        u32::from_le_bytes(nlink_bytes) as i128,
        i64::from_le_bytes(size_bytes_init_from_fstat(&uc_stat)) as i128,
        i32::from_le_bytes(blksize_bytes) as i128,
        i64::from_le_bytes(blocks_bytes) as i128,
        pread_ret as i128,
        r1 as i128,
        r2 as i128,
        r3 as i128,
        lseek_end as i128,
        lseek_cur as i128,
        lseek_set as i128,
        close_ret as i128,
        read_closed as i128,
        open_creat as i128,
        write_ret as i128,
        open_excl as i128,
        fstat_b_ret as i128,
        fstat_b_size,
        fcntl_getfd0,
        fcntl_setfd,
        fcntl_getfd1,
        fcntl_badfd,
        open_miss_par,
        open_file_par,
        open_dir_sub,
        open_norm_sub,
        lseek_past_end,
        write_zero,
        fstat_n_ret as i128,
        i64::from_le_bytes(fstat_n_size) as i128,
        open_trunc,
        fstat_b2_ret as i128,
        i64::from_le_bytes(fstat_b2_size) as i128,
        host_getfd_after_cloexec,
        open_dir_d as i128,
        dir_fstat_ret_i64 as i128,
        u32::from_le_bytes(dir_mode_bytes) as i128,
        u32::from_le_bytes(dir_nlink_bytes) as i128,
        i32::from_le_bytes(dir_blksize_bytes) as i128,
        dir_read_ret,
        dir_read_unm_ret,
        dir_read_efault_ret,
        dir_write_ret,
        dir_getfd0,
        dir_setfd1,
        dir_getfd1,
        dir_setfd0,
        dir_getfd2,
        dir_close_ret,
        open_dir_d_clo,
        dir_clo_getfd0,
        dir_clo_setfd0,
        dir_clo_getfd1,
        dir_clo_setfd1,
        dir_clo_getfd2,
        dir_clo_close_ret,
        dir_clo_closed_get,
        open_stdin,
        open_stdout,
        open_stderr,
        lseek_fs_safe,
        write_fs_safe_zero,
        write_fs_safe_zero_unm,
        open_append_b,
        lseek_append_fs_safe,
        write_append_fs_safe_one,
    ];

    let out = Command::new(lean_diff_eval_bin())
        .arg("--fs-diff-trace")
        .output()
        .expect("execute `Arm64/Testing/.lake/build/bin/diff_eval --fs-diff-trace`");
    assert!(
        out.status.success(),
        "diff_eval --fs-diff-trace failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8 stdout from diff_eval");
    let mut lines = stdout.trim().lines();
    let vals_line = lines.next().expect("Lean trace return values line");
    assert!(lines.next().is_none(), "unexpected extra lines from diff_eval");
    let lean_vals: Vec<i128> = vals_line
        .split(',')
        .map(|s| s.parse::<i128>().expect("parse integer from Lean trace"))
        .collect();

    assert_eq!(
        kernel_vals, lean_vals,
        "host Linux kernel FS syscall trace diverged from Lean execSyscall"
    );
}

fn size_bytes_init_from_fstat(uc: &Unicorn<'_, ()>) -> [u8; 8] {
    let mut b = [0u8; 8];
    uc.mem_read(0x2230, &mut b).unwrap();
    b
}

/// Run `diff_eval <flag>` and parse its comma-separated integer output.
fn lean_trace(flag: &str) -> Vec<i128> {
    let out = Command::new(lean_diff_eval_bin())
        .arg(flag)
        .output()
        .unwrap_or_else(|e| panic!("execute `Arm64/Testing/.lake/build/bin/diff_eval {flag}`: {e}"));
    assert!(
        out.status.success(),
        "diff_eval {flag} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8 stdout from diff_eval");
    stdout
        .trim()
        .split(',')
        .map(|s| s.parse::<i128>().expect("parse integer from Lean trace"))
        .collect()
}

unsafe extern "C" {
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64)
    -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut c_void, len: usize) -> i32;
    #[link_name = "write"]
    fn host_write(fd: i32, buf: *const c_void, count: usize) -> isize;
    fn sysconf(name: i32) -> i64;
    fn syscall(num: i64, ...) -> i64;
}

fn host_errno() -> i128 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0) as i128
}

/// Validates the musl mallocng guard-page memory syscalls (`mmap(PROT_NONE, MAP_FIXED)` over a
/// read/write mapping, `write` from a `PROT_NONE` page, `mprotect`, `mmap` with `len = 0`,
/// `munmap`) between the host Linux kernel, called natively from this test process, and Lean's
/// `execSyscall` evaluator (`diff_eval --mmap-diff-trace`, `dumpMmapDiffTrace`). The `mmap` flag
/// and protection values (`MAP_PRIVATE | MAP_ANONYMOUS = 0x22`, `MAP_FIXED = 0x10`, `PROT_NONE = 0`,
/// `PROT_READ | PROT_WRITE = 3`) and the checked behaviour are the same on x86-64 and AArch64
/// Linux; the test is skipped on hosts whose page size is not 4 KiB. Addresses are compared
/// relative to the base of the initial three-page mapping (the kernel picks it, the model uses
/// `0x50000`).
#[test]
fn mmap_guard_trace_matches_linux_kernel() {
    const PAGE: usize = 0x1000;
    const PROT_NONE: i32 = 0;
    const PROT_RW: i32 = 3;
    const MAP_PRIVATE_ANON: i32 = 0x22;
    const MAP_FIXED: i32 = 0x10;
    const SC_PAGESIZE: i32 = 30;
    // SAFETY: `sysconf(_SC_PAGESIZE)` has no preconditions.
    if unsafe { sysconf(SC_PAGESIZE) } != PAGE as i64 {
        eprintln!("skipping mmap_guard_trace_matches_linux_kernel: host page size is not 4 KiB");
        return;
    }

    let tmp = tempfile::tempdir().expect("create tempdir");
    let out = File::create(tmp.path().join("out")).expect("create output file");

    // SAFETY: every pointer dereferenced below lies in the three-page anonymous mapping created
    // by the first `mmap`, at a moment when its page is mapped read/write; the mapping is not
    // used after `munmap`. The `PROT_NONE` page is only passed to `write(2)`, which reports
    // `EFAULT` instead of faulting.
    let kernel_vals: Vec<i128> = unsafe {
        let base = mmap(null_mut(), 3 * PAGE, PROT_RW, MAP_PRIVATE_ANON, -1, 0);
        assert_ne!(base as isize, -1, "mmap of three read/write pages failed");
        let b = base as *mut u8;
        let rel = |p: *mut c_void| -> i128 {
            if p as isize == -1 {
                -host_errno()
            } else {
                (p as usize).wrapping_sub(base as usize) as isize as i128
            }
        };
        let rc = |r: i64| -> i128 { if r < 0 { -host_errno() } else { r as i128 } };
        write_volatile(b, 0x41);
        write_volatile(b.add(PAGE), 0x42);
        write_volatile(b.add(2 * PAGE), 0x43);

        let guard = b.add(PAGE).cast::<c_void>();
        let mmap_fixed = rel(mmap(
            guard,
            PAGE,
            PROT_NONE,
            MAP_PRIVATE_ANON | MAP_FIXED,
            -1,
            0,
        ));
        let write_guard = rc(host_write(out.as_raw_fd(), guard, 1) as i64);
        let mprotect_rw = rc(mprotect(guard, PAGE, PROT_RW) as i64);
        let guard_byte = read_volatile(b.add(PAGE)) as i128;
        let lower = read_volatile(b) as i128;
        let upper = read_volatile(b.add(2 * PAGE)) as i128;
        write_volatile(b.add(PAGE), 0x55);
        let mmap_fixed2 = rel(mmap(
            guard,
            PAGE,
            PROT_NONE,
            MAP_PRIVATE_ANON | MAP_FIXED,
            -1,
            0,
        ));
        let mprotect_rw2 = rc(mprotect(guard, PAGE, PROT_RW) as i64);
        let replaced_byte = read_volatile(b.add(PAGE)) as i128;
        let mmap_len0 = rel(mmap(
            guard,
            0,
            PROT_NONE,
            MAP_PRIVATE_ANON | MAP_FIXED,
            -1,
            0,
        ));
        let munmap_ret = rc(munmap(base, 3 * PAGE) as i64);
        vec![
            mmap_fixed,
            write_guard,
            mprotect_rw,
            guard_byte,
            lower,
            upper,
            mmap_fixed2,
            mprotect_rw2,
            replaced_byte,
            mmap_len0,
            munmap_ret,
        ]
    };

    assert_eq!(
        kernel_vals,
        lean_trace("--mmap-diff-trace"),
        "host Linux kernel guard-page memory syscall trace diverged from Lean execSyscall"
    );
}

#[repr(C)]
#[derive(Clone, Copy)]
struct HostStackT {
    ss_sp: u64,
    ss_flags: u32,
    ss_pad: u32,
    ss_size: u64,
}

/// Validates `MAP_STACK` (`0x20022`) `mmap` and `sigaltstack` (`do_sigaltstack` in `kernel/signal.c`:
/// `NULL` query, `< MINSIGSTKSZ` `-ENOMEM` skipping `uoss`, 32-bit `ss_flags` ignoring `+12` caller
/// padding and zeroing `+12` in `uoss`, `SS_AUTODISARM`, `SS_DISABLE` with non-zero `ss_size` and
/// `SS_AUTODISARM | SS_DISABLE` preserving `SS_AUTODISARM`, invalid flags `-EINVAL`, `PROT_NONE` `uss`
/// `-EFAULT`, and post-commit `uoss` `-EFAULT` ordering) between the live host Linux kernel and
/// Lean's `execSyscall` (`diff_eval --sigaltstack-diff-trace`).
#[test]
#[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
fn sigaltstack_and_map_stack_trace_matches_linux_kernel() {
    const PAGE: usize = 0x1000;
    const PROT_NONE: i32 = 0;
    const PROT_RW: i32 = 3;
    const MAP_PRIVATE_ANON_STACK: i32 = 0x20022;
    const SC_PAGESIZE: i32 = 30;
    const SS_DISABLE: u32 = 2;
    const SS_AUTODISARM: u32 = 1 << 31;
    #[cfg(target_arch = "x86_64")]
    const NR_SIGALTSTACK: i64 = 131;
    #[cfg(target_arch = "aarch64")]
    const NR_SIGALTSTACK: i64 = 132;

    if unsafe { sysconf(SC_PAGESIZE) } != PAGE as i64 {
        eprintln!(
            "skipping sigaltstack_and_map_stack_trace_matches_linux_kernel: host page size is not 4 KiB"
        );
        return;
    }

    let kernel_vals: Vec<i128> = unsafe {
        let base = mmap(null_mut(), 4 * PAGE, PROT_RW, MAP_PRIVATE_ANON_STACK, -1, 0);
        assert_ne!(base as isize, -1, "mmap(MAP_STACK) of four pages failed");
        let b = base as *mut u8;
        let guard = b.add(PAGE).cast::<c_void>();
        let alt_sp = b.add(2 * PAGE) as u64;
        let uss_ptr = b.cast::<HostStackT>();
        let uoss_ptr = b.add(0x40).cast::<HostStackT>();

        let rc = |r: i64| -> i128 { if r < 0 { -host_errno() } else { r as i128 } };
        let rel = |addr: u64| -> i128 {
            (addr as usize).wrapping_sub(base as usize) as isize as i128
        };
        let fill_uoss_ff = || {
            for i in 0..24 {
                write_volatile(b.add(0x40 + i), 0xff);
            }
        };

        // Save Rust test thread's current alternate signal stack and start from disabled state.
        let mut saved_ss = HostStackT {
            ss_sp: 0,
            ss_flags: 0,
            ss_pad: 0,
            ss_size: 0,
        };
        assert_eq!(syscall(NR_SIGALTSTACK, 0usize, &mut saved_ss as *mut HostStackT), 0);
        let init_dis = HostStackT {
            ss_sp: 0,
            ss_flags: SS_DISABLE,
            ss_pad: 0,
            ss_size: 0,
        };
        assert_eq!(syscall(NR_SIGALTSTACK, &init_dis as *const HostStackT, 0usize), 0);

        // 1. Convert `guard` page to `PROT_NONE`
        let prot_ret = rc(mprotect(guard, PAGE, PROT_NONE) as i64);

        // 2. Initial disabled query
        fill_uoss_ff();
        let q0_ret = rc(syscall(NR_SIGALTSTACK, 0usize, uoss_ptr));
        let q0 = read_volatile(uoss_ptr);

        // 3. `ss_size = 1024 < MINSIGSTKSZ` -> `-ENOMEM` (`uoss` untouched)
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: 0,
                ss_pad: 0,
                ss_size: 1024,
            },
        );
        fill_uoss_ff();
        let small_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, uoss_ptr));
        let small_uoss_b0 = read_volatile(b.add(0x40)) as i128;

        // 4. Install `{ sp = alt_sp, flags = 0, pad = 0xdeadbeef, size = 0x2000 }`
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: 0,
                ss_pad: 0xdead_beef,
                ss_size: 0x2000,
            },
        );
        fill_uoss_ff();
        let inst_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, uoss_ptr));
        let inst_old = read_volatile(uoss_ptr);

        // 5. Query active (`uss = 0`)
        fill_uoss_ff();
        let qact_ret = rc(syscall(NR_SIGALTSTACK, 0usize, uoss_ptr));
        let qact = read_volatile(uoss_ptr);

        // 6. Install `SS_AUTODISARM` + query
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: SS_AUTODISARM,
                ss_pad: 0,
                ss_size: 0x2000,
            },
        );
        let auto_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, 0usize));
        let qauto_ret = rc(syscall(NR_SIGALTSTACK, 0usize, uoss_ptr));
        let qauto = read_volatile(uoss_ptr);

        // 7. Disable with `SS_AUTODISARM | SS_DISABLE` and non-zero `size = 16` + query
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: SS_AUTODISARM | SS_DISABLE,
                ss_pad: 0,
                ss_size: 16,
            },
        );
        let autodis_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, 0usize));
        let qautodis_ret = rc(syscall(NR_SIGALTSTACK, 0usize, uoss_ptr));
        let qautodis = read_volatile(uoss_ptr);

        // 8. Disable with `SS_DISABLE` and non-zero `size = 0x41000` + query
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: SS_DISABLE,
                ss_pad: 0,
                ss_size: 0x41000,
            },
        );
        let dis_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, 0usize));
        let _ = syscall(NR_SIGALTSTACK, 0usize, uoss_ptr);
        let qdis = read_volatile(uoss_ptr);

        // 9. Invalid flags (`4` and `3`)
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: 4,
                ss_pad: 0,
                ss_size: 0x2000,
            },
        );
        let bad4_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, 0usize));
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: 3,
                ss_pad: 0,
                ss_size: 0x2000,
            },
        );
        let bad3_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, 0usize));

        // 10. `PROT_NONE` `uss = guard` -> `-EFAULT`
        let ef_uss_ret = rc(syscall(NR_SIGALTSTACK, guard, 0usize));

        // 11. Post-commit `uoss = guard` (`PROT_NONE`) `-EFAULT` ordering check + query
        write_volatile(
            uss_ptr,
            HostStackT {
                ss_sp: alt_sp,
                ss_flags: 0,
                ss_pad: 0,
                ss_size: 0x2000,
            },
        );
        let ef_uoss_ret = rc(syscall(NR_SIGALTSTACK, uss_ptr, guard));
        let _ = syscall(NR_SIGALTSTACK, 0usize, uoss_ptr);
        let qafter_ef = read_volatile(uoss_ptr);

        // Restore thread's saved alternate signal stack before unmapping `base`.
        let _ = syscall(NR_SIGALTSTACK, &init_dis as *const HostStackT, 0usize);
        if (saved_ss.ss_flags & SS_DISABLE) == 0 && saved_ss.ss_size > 0 {
            let restore_ss = HostStackT {
                ss_sp: saved_ss.ss_sp,
                ss_flags: saved_ss.ss_flags & SS_AUTODISARM,
                ss_pad: 0,
                ss_size: saved_ss.ss_size,
            };
            let _ = syscall(NR_SIGALTSTACK, &restore_ss as *const HostStackT, 0usize);
        }

        // 12. `munmap(base, 4 * PAGE)` -> `0`
        let unmap_ret = rc(munmap(base, 4 * PAGE) as i64);

        vec![
            prot_ret,
            q0_ret,
            q0.ss_sp as i128,
            q0.ss_flags as i128,
            q0.ss_pad as i128,
            q0.ss_size as i128,
            small_ret,
            small_uoss_b0,
            inst_ret,
            inst_old.ss_flags as i128,
            inst_old.ss_pad as i128,
            qact_ret,
            rel(qact.ss_sp),
            qact.ss_flags as i128,
            qact.ss_pad as i128,
            qact.ss_size as i128,
            auto_ret,
            qauto_ret,
            qauto.ss_flags as i128,
            autodis_ret,
            qautodis_ret,
            qautodis.ss_sp as i128,
            qautodis.ss_flags as i128,
            qautodis.ss_size as i128,
            dis_ret,
            qdis.ss_sp as i128,
            qdis.ss_flags as i128,
            qdis.ss_size as i128,
            bad4_ret,
            bad3_ret,
            ef_uss_ret,
            ef_uoss_ret,
            rel(qafter_ef.ss_sp),
            qafter_ef.ss_flags as i128,
            qafter_ef.ss_size as i128,
            unmap_ret,
        ]
    };

    assert_eq!(
        kernel_vals,
        lean_trace("--sigaltstack-diff-trace"),
        "host Linux kernel sigaltstack + MAP_STACK trace diverged from Lean execSyscall"
    );
}

/// Environment variable selecting the fresh-process signal probe run by
/// [`FRESH_SIGNAL_PROBE_CTOR`] in a child copy of this test binary.
const FRESH_SIGNAL_PROBE_ENV: &str = "ARM64_FRESH_SIGNAL_PROBE";

unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
    fn _exit(code: i32) -> !;
}

#[cfg(target_arch = "x86_64")]
const FRESH_NR_SIGALTSTACK: i64 = 131;
#[cfg(target_arch = "aarch64")]
const FRESH_NR_SIGALTSTACK: i64 = 132;
#[cfg(target_arch = "x86_64")]
const FRESH_NR_RT_SIGACTION: i64 = 13;
#[cfg(target_arch = "aarch64")]
const FRESH_NR_RT_SIGACTION: i64 = 134;

/// Runs from `.init_array` before Rust's `std` runtime (which may install its own
/// `sigaltstack`), so the probed alternate-stack state is exactly what `execve` left: `sas_ss_sp =
/// sas_ss_size = 0` (`fs/exec.c:1260`) with the raw `sas_ss_flags` inherited from the parent.
/// Prints `sigaltstack(&{0, 0, 0}, NULL)`, then the `sa_flags` read back via `oact` after
/// `rt_sigaction(SIGUSR1, &{SIG_IGN, sa_flags = !0}, NULL, 8)`, and exits without running `main`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = ".init_array")]
static FRESH_SIGNAL_PROBE_CTOR: extern "C" fn() = {
    extern "C" fn probe() {
        unsafe {
            if getenv(c"ARM64_FRESH_SIGNAL_PROBE".as_ptr()).is_null() {
                return;
            }
            let zero = [0u64; 3];
            let r_sas = syscall(FRESH_NR_SIGALTSTACK, zero.as_ptr(), 0usize);
            let r_sas = if r_sas < 0 { -(host_errno() as i64) } else { r_sas };
            // `struct sigaction` for raw `rt_sigaction`: handler, flags, restorer, mask.
            let act: [u64; 4] = [1, u64::MAX, 0, 0];
            let mut oact: [u64; 4] = [0; 4];
            let r1 = syscall(FRESH_NR_RT_SIGACTION, 10i64, act.as_ptr(), 0usize, 8usize);
            let r2 = syscall(FRESH_NR_RT_SIGACTION, 10i64, 0usize, oact.as_mut_ptr(), 8usize);
            let line = format!("{r_sas},{r1},{r2},{}\n", oact[1]);
            host_write(1, line.as_ptr().cast(), line.len());
            _exit(0);
        }
    }
    probe
};

/// Validates `do_sigaltstack`'s unchanged-settings early return (`kernel/signal.c:4486-4493`) and
/// `do_sigaction`'s `sa_flags &= UAPI_SA_FLAGS` (`kernel/signal.c:4401-4404`) in freshly
/// `execve`d copies of this test binary. Expected values are the ones pinned for Lean's
/// `execSyscall` by `sigaltstack_and_map_stack_ok` / `rt_sigaction_and_tkill_ok` in
/// `Arm64/Testing/Regression/StdSyscalls.lean`:
/// - raw inherited `sas_ss_flags = 0` (the model's initial `sigAltStack = {}`): `sigaltstack(&{0,
///   0, 0})` returns `0` although `ss_size = 0 < MINSIGSTKSZ`;
/// - inherited `SS_DISABLE` (the model after an `SS_DISABLE` store): it returns `-ENOMEM`;
/// - `sa_flags = !0` reads back as `UAPI_SA_FLAGS = 0xdc000807` (same value on x86-64 and arm64,
///   where `__ARCH_UAPI_SA_FLAGS = SA_RESTORER = 0x04000000`).
///
/// `QEMU` user mode implements neither (its `target_sigaltstack` has no early return and its
/// `do_sigaction` stores `sa_flags` verbatim), so these cases live here rather than in
/// `syscall_probe.elf`, whose outputs must match `qemu-aarch64` exactly. Skipped on hosts reporting
/// a kernel release older than 5.16.
#[test]
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn fresh_process_sigaltstack_early_return_and_sa_flags_mask_match_linux_kernel() {
    use std::os::unix::process::CommandExt;
    // The early return landed in Linux 5.16 and the mask in 5.11; older kernels and sandboxes
    // that report an older release (e.g. gVisor's `4.4.0`) are not the modeled kernel.
    let release = std::fs::read_to_string("/proc/sys/kernel/osrelease").unwrap_or_default();
    let mut nums = release.trim().split(|c: char| !c.is_ascii_digit()).map(|v| v.parse::<u32>());
    let (major, minor) = match (nums.next(), nums.next()) {
        (Some(Ok(a)), Some(Ok(b))) => (a, b),
        _ => (0, 0),
    };
    if (major, minor) < (5, 16) {
        eprintln!(
            "skipping fresh_process_sigaltstack_early_return_and_sa_flags_mask_match_linux_kernel: \
             host kernel release {:?} is older than 5.16",
            release.trim()
        );
        return;
    }
    const SS_DISABLE: u32 = 2;
    const ENOMEM: i64 = 12;
    let run = |inherited_flags: u32| -> Vec<i64> {
        let mut cmd = Command::new(std::env::current_exe().expect("current_exe"));
        cmd.env(FRESH_SIGNAL_PROBE_ENV, "1");
        unsafe {
            cmd.pre_exec(move || {
                // `SS_DISABLE` stores `{0, 0, SS_DISABLE}`; `ss_flags = 0` needs a valid stack
                // (`execve` then zeroes `sp`/`size` and keeps the raw flags).
                let ss = HostStackT {
                    ss_sp: 0x1000,
                    ss_flags: inherited_flags,
                    ss_pad: 0,
                    ss_size: 1 << 20,
                };
                if syscall(FRESH_NR_SIGALTSTACK, &ss as *const HostStackT, 0usize) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let out = cmd.output().expect("spawn fresh signal probe");
        assert!(out.status.success(), "fresh signal probe failed: {out:?}");
        String::from_utf8(out.stdout)
            .expect("utf8")
            .trim()
            .split(',')
            .map(|v| v.parse::<i64>().expect("integer"))
            .collect()
    };
    let uapi_sa_flags = 0xdc00_0807u64 as i64;
    assert_eq!(run(0), vec![0, 0, 0, uapi_sa_flags], "inherited raw sas_ss_flags = 0");
    assert_eq!(run(SS_DISABLE), vec![-ENOMEM, 0, 0, uapi_sa_flags], "inherited SS_DISABLE");
}
