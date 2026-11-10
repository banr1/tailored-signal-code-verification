/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Linux VFS Path Resolution, `openat`, & `close` Syscalls (`Arm64.Trusted.Syscalls.Fs.Open`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `fs/open.c:1430` (`SYSCALL_DEFINE4(openat, int, dfd, const char __user *, filename, int, flags, umode_t, mode)` -> `do_sys_open` -> `do_sys_openat2` -> `do_filp_open`)
  - `fs/open.c:1553` (`SYSCALL_DEFINE1(close, unsigned int, fd)` -> `close_fd`)
  - `fs/namei.c:2505` (`path_lookupat` / `link_path_walk` / `open_last_lookups`)
  - `include/uapi/asm-generic/fcntl.h:19` (`O_RDONLY .. O_CLOEXEC`, `AT_FDCWD = -100`)
  - `include/uapi/linux/limits.h:12` (`NAME_MAX = 255`), `include/uapi/linux/limits.h:13` (`PATH_MAX = 4096`)
  - `include/uapi/linux/stat.h:32` (`S_IRUSR | S_IWUSR = 0o600` owner read-write mode bits)
  - `fs/namei.c:4707` (`lookup_fast_for_open`: `O_CREAT` + trailing `'/'` on `LAST_NORM` -> `-EISDIR` before `NAME_MAX`)
  - `fs/libfs.c:71` (`simple_lookup`: component longer than `NAME_MAX` -> `-ENAMETOOLONG`)
  - `fs/open.c:1308` (`build_open_flags`: `O_TRUNC` only adds `MAY_WRITE`, so `O_RDONLY|O_TRUNC` truncates)
- **Purpose & Key Exports**: `SYS_OPENAT` (`56`), `SYS_CLOSE` (`57`), `PATH_MAX`, `AT_FDCWD_W32`,
  `NAME_MAX`, `O_CREAT_OWNER_RW_MASK`, `O_*` flags, `OPENAT_KNOWN_MASK`, `readCStringAux`,
  `readCString`, `FsResolve`, `hasTrailingSlash`, `endsWithSlashDot`, `trailingDir`,
  `trailingNormSlash`, `resolveCwdPath`, `ancestorWalkErrno?`, `strictAncestorWalkErrno?`,
  `OpenVerdict`, `checkOpenFlags`, `openatPure`, `applyOpenVerdict`, `execOpenat`, and `execClose`.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `openat` syscall number (`__NR_openat = 56`, `include/uapi/asm-generic/unistd.h:189`, `fs/open.c:1430`). -/
def SYS_OPENAT : BitVec 64 := 56#64

/-- Linux AArch64 `close` syscall number (`__NR_close = 57`, `include/uapi/asm-generic/unistd.h:191`, `fs/open.c:1553`). -/
def SYS_CLOSE : BitVec 64 := 57#64

/-- Maximum user pathname scan length including NUL (`PATH_MAX = 4096`;
    `include/uapi/linux/limits.h`, `fs/namei.c` `getname_flags`). -/
def PATH_MAX : Nat := 4096

/-- Linux AArch64 `openat` flags (`include/uapi/asm-generic/fcntl.h`, `arch/arm64/include/uapi/asm/fcntl.h`). -/
def AT_FDCWD_W32    : BitVec 32 := 0xffffff9c#32
def O_CREAT_W32     : BitVec 32 := 0x00040#32
def O_EXCL_W32      : BitVec 32 := 0x00080#32
def O_NOCTTY_W32    : BitVec 32 := 0x00100#32
def O_TRUNC_W32     : BitVec 32 := 0x00200#32
def O_APPEND_W32    : BitVec 32 := 0x00400#32
def O_NONBLOCK_W32  : BitVec 32 := 0x00800#32
def O_DIRECTORY_W32 : BitVec 32 := 0x04000#32
def O_NOFOLLOW_W32  : BitVec 32 := 0x08000#32
def O_LARGEFILE_W32 : BitVec 32 := 0x20000#32
def O_CLOEXEC_W32   : BitVec 32 := 0x80000#32

def OPENAT_KNOWN_MASK : BitVec 32 :=
  0x3#32 ||| O_CREAT_W32 ||| O_EXCL_W32 ||| O_NOCTTY_W32 ||| O_TRUNC_W32 |||
  O_APPEND_W32 ||| O_NONBLOCK_W32 ||| O_DIRECTORY_W32 ||| O_NOFOLLOW_W32 |||
  O_LARGEFILE_W32 ||| O_CLOEXEC_W32

/-- Outcome of reading or resolving a CWD-relative path against `FsState`. -/
inductive FsResolve (α : Type) where
  | ok (val : α)
  | errno (err : BitVec 64)
  | trap (msg : String)

/-- Read a NUL-terminated string of at most `fuel` bytes from user memory `m` starting at `ptr`
    (`fs/namei.c:137` `getname_flags`). Unmapped/unreadable bytes (`!(m.perm ptr).r`) return
    `-EFAULT` (`14`); readable `lazyFree` bytes fail closed (`.trap`) because `getname_flags`
    reads indeterminate old-or-zero bytes on Linux `7.3` rather than returning `-EFAULT`. -/
def readCStringAux (m : Memory) (ptr : BitVec 64) : Nat → List Char → FsResolve String
  | 0, _ => .errno ENAMETOOLONG
  | fuel + 1, acc =>
    if !(m.perm ptr).r then .errno 14#64
    else if !m.canRead ptr 1 then .trap "openat path in lazy-free memory"
    else
      let b := m.read8 ptr
      if b == 0#8 then .ok (String.ofList acc.reverse)
      else readCStringAux m (ptr + 1#64) fuel (Char.ofNat b.toNat :: acc)

def readCString (m : Memory) (ptr : BitVec 64) : FsResolve String :=
  readCStringAux m ptr PATH_MAX []

/-- True when `path` ends with `'/'`. -/
def hasTrailingSlash (path : String) : Bool :=
  path.toList.reverse.head? == some '/'

/-- True when `path` ends with `"/."`. -/
def endsWithSlashDot (path : String) : Bool :=
  match path.toList.reverse with
  | '.' :: '/' :: _ => true
  | _ => false

/-- True when `rawPath` syntactically designates a directory (`"."`, trailing `'/'`, or `"/."`). -/
def trailingDir (rawPath : String) : Bool :=
  rawPath == "." || hasTrailingSlash rawPath || endsWithSlashDot rawPath

/-- True when `rawPath` ends with `'/'` after a non-`"."` final segment (`LAST_NORM` +
    `LOOKUP_DIRECTORY` in Linux `fs/namei.c`, e.g. `"dir/"`, `"reg/"`, `"newslash/"`). -/
def trailingNormSlash (rawPath : String) : Bool :=
  if !hasTrailingSlash rawPath then false
  else
    match ((splitSlash rawPath).filter (!·.isEmpty)).reverse with
    | last :: _ => last != "."
    | [] => false

/-- Validate a working-directory-relative pathname for `openat(dfd, rawPath, ...)`:
    - empty `rawPath` returns `-ENOENT` (`getname_flags` in `fs/namei.c`);
    - non-`AT_FDCWD` `dfd` traps fail-closed (`"unmodeled non-AT_FDCWD dirfd"`);
    - leading `'/'` traps fail-closed (`"unmodeled absolute path"`);
    - `".."` segment traps fail-closed (`"unmodeled '..' path component"`);
    - otherwise returns canonical relative segments `normalizePath rawPath`. -/
def resolveCwdPath (dfd : BitVec 32) (rawPath : String) : FsResolve FsPath :=
  if rawPath.isEmpty then .errno ENOENT
  else if dfd != AT_FDCWD_W32 then .trap "unmodeled non-AT_FDCWD dirfd"
  else if hasLeadingSlash rawPath then .trap "unmodeled absolute path"
  else if hasDotDot rawPath then .trap "unmodeled '..' path component"
  else .ok (normalizePath rawPath)

/-- Maximum length in bytes of one pathname component (`NAME_MAX = 255`,
    `include/uapi/linux/limits.h:12`), enforced per component at lookup time (e.g.
    `simple_lookup` in `fs/libfs.c:71`). -/
def NAME_MAX : Nat := 255

/-- Walk the components of relative `rawPath` left-to-right from `AT_FDCWD` (matching
    `link_path_walk` + `open_last_lookups` in `fs/namei.c`):
    - each strict ancestor component, in order, returns `some ENAMETOOLONG` if it is longer than
      `NAME_MAX` bytes, `some ENOTDIR` if it is a regular file, or `some ENOENT` if it is missing;
    - after all ancestors resolve to directories, the final component returns
      `some ENAMETOOLONG` if it is longer than `NAME_MAX` bytes;
    - otherwise returns `none`.
    `readCStringAux` stores one `Char` per byte, so `String.length` is the byte length. -/
def ancestorWalkErrno? (fs : FsState) (rawPath : String) : Option (BitVec 64) :=
  let segs := (splitSlash rawPath).filter (!·.isEmpty)
  let rec walk (cur : FsPath) : List String → Option (BitVec 64)
    | [] => none
    | seg :: rest =>
      if seg.length > NAME_MAX then some ENAMETOOLONG
      else
        let cur' := if seg == "." then cur else cur ++ [seg]
        match fs.getEntry cur' with
        | some .dir      => walk cur' rest
        | some (.file _) => some ENOTDIR
        | none           => some ENOENT
  match walk [] segs.dropLast with
  | some err => some err
  | none => if segs.getLast?.any (·.length > NAME_MAX) then some ENAMETOOLONG else none

/-- Walk only the strict ancestor components (`segs.dropLast`) of relative `rawPath`
    left-to-right from `AT_FDCWD` (`link_path_walk` in `fs/namei.c:2360`, before
    `open_last_lookups`). -/
def strictAncestorWalkErrno? (fs : FsState) (rawPath : String) : Option (BitVec 64) :=
  ancestorWalkErrno?.walk fs [] ((splitSlash rawPath).filter (!·.isEmpty)).dropLast

/-- Owner read+write permission mask (`S_IRUSR | S_IWUSR = 0o600 = 0x180`,
    `include/uapi/linux/stat.h:32-33`) required on new regular-file creation in `FsState`
    (which models all regular files as owner-readable and owner-writable without per-file mode bits). -/
def O_CREAT_OWNER_RW_MASK : BitVec 32 := 0x180#32

/-- Outcome of `openat(dfd, rawPath, flags, mode)` against `fs : FsState`:
    - `opened fd fs' changedPath?`: allocates `fd` in `fs'`, optionally appending
      `TraceEvent.fileChanged path` when a file was newly created or truncated (`O_TRUNC`);
    - `errno err`: returns negative errno `-err` in `X0`, leaving `fs` and `trace` unchanged;
    - `trap msg`: sets `status := .Exception msg` when inputs fall outside the modeled scope. -/
inductive OpenVerdict where
  | opened (fd : BitVec 64) (fs' : FsState) (changedPath? : Option String)
  | errno  (err : BitVec 64)
  | trap   (msg : String)
  deriving Inhabited

/-- Validate `openat` `flags` before copying the user pathname (`fs/open.c:1402` `do_sys_openat2` ->
    `build_open_flags` before `getname_flags`):
    - returns `some (.trap "unmodeled openat flags")` on unknown flag bits or invalid access mode `3`;
    - returns `some (.errno EINVAL)` when both `O_CREAT` and `O_DIRECTORY` are set;
    - returns `none` when `flags` pass pre-`getname_flags` validation. -/
def checkOpenFlags (flags : BitVec 32) : Option OpenVerdict :=
  if (flags &&& ~~~OPENAT_KNOWN_MASK) != 0#32 || (flags &&& 3#32) == 3#32 then
    some (.trap "unmodeled openat flags")
  else if (flags &&& O_CREAT_W32) != 0#32 && (flags &&& O_DIRECTORY_W32) != 0#32 then
    some (.errno EINVAL)
  else
    none

/-- Pure working-directory `openat(dfd, rawPath, flags, mode)` decision tree over `fs : FsState`
    once `rawPath` has been read from user memory. Defaults `mode` to `0o666` (`0x1b6#32`, as passed
    by `std::fs::OpenOptions::new()` and standard libc callers); creating a missing regular file
    with `(mode &&& O_CREAT_OWNER_RW_MASK) != O_CREAT_OWNER_RW_MASK` fails closed (`.trap`) because
    `FsState` does not track per-inode permission bits for subsequent opens. -/
def openatPure (fs : FsState) (dfd : BitVec 32) (rawPath : String) (flags : BitVec 32)
    (mode : BitVec 32 := 0o666#32) : OpenVerdict :=
  match checkOpenFlags flags with
  | some v => v
  | none =>
    let acc : FdAccessMode :=
      if (flags &&& 3#32) == 0#32 then .rdonly
      else if (flags &&& 3#32) == 1#32 then .wronly
      else .rdwr
    let hasCreat   := (flags &&& O_CREAT_W32) != 0#32
    let hasExcl    := (flags &&& O_EXCL_W32) != 0#32
    let hasTrunc   := (flags &&& O_TRUNC_W32) != 0#32
    let hasAppend  := (flags &&& O_APPEND_W32) != 0#32
    let hasDir     := (flags &&& O_DIRECTORY_W32) != 0#32
    let hasCloexec := (flags &&& O_CLOEXEC_W32) != 0#32
    match resolveCwdPath dfd rawPath with
    | .trap msg => .trap msg
    | .errno err => .errno err
    | .ok segs =>
      match strictAncestorWalkErrno? fs rawPath with
      | some err => .errno err
      | none =>
        let isTrailDir := trailingDir rawPath
        let isTrailNormSlash := trailingNormSlash rawPath
        if hasCreat && isTrailNormSlash then .errno EISDIR
        else if ((splitSlash rawPath).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) then
          .errno ENAMETOOLONG
        else
          match fs.getEntry segs with
          | some .dir =>
            if hasCreat && hasExcl && !isTrailNormSlash then .errno EEXIST
            else if acc != .rdonly || hasTrunc || hasCreat then .errno EISDIR
            else match fs.allocFd with
              | none => .errno EMFILE
              | some fd =>
                let fs' := fs.setFd fd
                  (some { path := rawPath, accMode := .rdonly, append := hasAppend,
                          cloexec := hasCloexec, offset := 0, kind := .localDir })
                .opened fd fs' none
          | some (.file oldBytes) =>
            if isTrailDir || hasDir then .errno ENOTDIR
            else if hasCreat && hasExcl then .errno EEXIST
            else match fs.allocFd with
              | none => .errno EMFILE
              | some fd =>
                let bs' := if hasTrunc then [] else oldBytes
                let fs' := (fs.setEntry segs (some (.file bs'))).setFd fd
                  (some { path := rawPath, accMode := acc, append := hasAppend, cloexec := hasCloexec, offset := 0 })
                .opened fd fs' (if hasTrunc then some segs.toPathString else none)
          | none =>
            if !hasCreat then .errno ENOENT
            else match fs.allocFd with
              | none => .errno EMFILE
              | some fd =>
                if (mode &&& O_CREAT_OWNER_RW_MASK) != O_CREAT_OWNER_RW_MASK then
                  .trap "unmodeled non-owner-rw O_CREAT mode"
                else
                  let fs' := (fs.setEntry segs (some (.file []))).setFd fd
                    (some { path := rawPath, accMode := acc, append := hasAppend, cloexec := hasCloexec, offset := 0 })
                  .opened fd fs' (some segs.toPathString)

/-- Apply an `OpenVerdict` to machine state `s`. -/
def applyOpenVerdict (s : State) : OpenVerdict → State
  | .opened fd fs' none     => ((s.setFs fs').writeReg64 Reg.x0 fd).advancePC
  | .opened fd fs' (some p) => (((s.setFs fs').appendTrace [.fileChanged p]).writeReg64 Reg.x0 fd).advancePC
  | .errno err              => (s.writeReg64 Reg.x0 (-err)).advancePC
  | .trap msg               => s.setStatus (.Exception msg)

/-- `openat(dfd, filename, flags, mode)` (`__NR_openat = 56`, `fs/open.c:1430` `SYSCALL_DEFINE4(openat)` ->
    `do_sys_openat2` -> `do_filp_open`) over the working-directory tree:
    - `[INTENTIONAL_SCOPE]`: requires `dfd = AT_FDCWD`, relative paths without leading `'/'` or `".."`
      components, and owner read-write `mode` (`(mode &&& 0o600) == 0o600`) when creating a missing
      regular file (failing closed with `.Exception` outside scope);
    - walks strict ancestors via `strictAncestorWalkErrno?`, rejects `O_CREAT` + trailing `'/'` on
      a non-`"."` final segment with `-EISDIR` before checking `NAME_MAX` on the final segment
      (`fs/namei.c:4707` `lookup_fast_for_open`), and returns `-ENAMETOOLONG` when the final
      component exceeds `NAME_MAX`;
    - rejects directory write/create/trunc opens with `-EEXIST`/`-EISDIR` and opens directories
      with `O_RDONLY` (`!O_CREAT`, `!O_TRUNC`) as `.localDir` descriptors;
    - records `O_CLOEXEC` in `FdEntry.cloexec`, and emits canonical `TraceEvent.fileChanged` on
      file creation or `O_TRUNC` truncation (any access mode, including `O_RDONLY|O_TRUNC`,
      `fs/open.c:1308`);
    - `[OVERPINNED_BEHAVIOR]`: validates `flags` (`checkOpenFlags` / `build_open_flags`) before
      copying `filename` (`readCString` / `getname_flags`) and walking path components
      (`openatPure` / `do_filp_open`), matching `fs/open.c:1402`. -/
def execOpenat (s : State) : State :=
  let dfd   := s.readReg32 Reg.x0
  let fname := s.readReg64 Reg.x1
  let flags := s.readReg32 Reg.x2
  let mode  := s.readReg32 Reg.x3
  match checkOpenFlags flags with
  | some v => applyOpenVerdict s v
  | none =>
    match readCString s.mem fname with
    | .trap msg => s.setStatus (.Exception msg)
    | .errno err => (s.writeReg64 Reg.x0 (-err)).advancePC
    | .ok rawPath => applyOpenVerdict s (openatPure s.fs dfd rawPath flags mode)

/-- `close(fd)` (`__NR_close = 57`, `fs/open.c:1553` `SYSCALL_DEFINE1(close)` -> `close_fd`):
    - `[INTENTIONAL_SCOPE]`: Closes open `.localFile` and `.localDir` descriptors (`fd >= 3`); fails
      closed with `.Exception` on `.stdio` descriptors (`fd < 3`). -/
def execClose (s : State) : State :=
  let rawFd := s.readReg32 Reg.x0
  if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
    | some desc =>
      if desc.kind != .localFile && desc.kind != .localDir then
        s.setStatus (.Exception "unmodeled non-file fd")
      else ((s.setFs (s.fs.setFd fd none)).writeReg64 Reg.x0 0#64).advancePC

end Arm64
