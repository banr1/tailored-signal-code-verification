#!/usr/bin/env python3
# Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
# See `third_party/libsignal/README.md`.

r"""Static worst-case stack depth of an aarch64 Rust function, from rlibs (untrusted tooling).

Usage: stackdepth.py <root-substring> <rlib>... [--terminal REGEX]... [--fmt-not-terminal]
Environment: LLVM_BIN (default /usr/lib/llvm-19/bin); WATCH=<regex> also prints the maximal entry
depth (and callers) of every reached function matching the regex.

Example (the `spqr::recv` budget `spqrRecvStack` of
`LibsignalBinary/Specifications/LibsignalTripleRatchet.lean`; rlibs from
`cargo build --release --target aarch64-unknown-linux-gnu` of this crate with the image profile, as
built by `lake`):

    D=third_party/libsignal/libsignal-session/target/aarch64-unknown-linux-gnu/release/deps
    SR=$(rustc +1.98.1 --print sysroot)/lib/rustlib/aarch64-unknown-linux-gnu/lib
    python3 third_party/libsignal/libsignal-session/tools/stackdepth.py 'spqr::recv' $D/*.rlib \
      $SR/libcore-*.rlib $SR/liballoc-*.rlib $SR/libcompiler_builtins-*.rlib \
      $SR/libstd-*.rlib $SR/libstd_detect-*.rlib
    # WORST-CASE DEPTH: 18160 bytes (17.7 KiB), 199 functions, no recursion


Method:
* extract every object of the given rlibs; index defined symbols (llvm-nm);
* disassemble (llvm-objdump -dr) only the objects needed, lazily from the root;
* frame of a function = sum of all `sp` decrements in its body (pre-index `stp/str ..., [sp, #-N]!`
  and `sub sp, sp, #N` / `#N, lsl #12`); a `sub sp, sp, xN` (dynamic) is flagged;
* edges = R_AARCH64_CALL26 (`bl`) and R_AARCH64_JUMP26 (`b`, tail call: counted like a call,
  conservative) relocations to symbols or `.text.<sym>` sections; `blr` / `br xN` are listed;
* depth(f) = frame(f) + max depth(callee); panic / alloc-error entry points are terminal (the run
  ends there; panic=abort); undefined symbols are reported.
"""
import atexit, os, re, shutil, subprocess, sys, tempfile, collections, functools

LLVM_BIN = os.environ.get("LLVM_BIN", "/usr/lib/llvm-19/bin")
OBJDUMP = os.path.join(LLVM_BIN, "llvm-objdump")
NM = os.path.join(LLVM_BIN, "llvm-nm")
AR = os.path.join(LLVM_BIN, "llvm-ar")
FILT = os.path.join(LLVM_BIN, "llvm-cxxfilt")

args = sys.argv[1:]
terminal = [r"core::panicking::", r"core::option::unwrap_failed", r"core::option::expect_failed",
            r"core::result::unwrap_failed", r"alloc::alloc::handle_alloc_error",
            r"alloc::raw_vec::handle_error", r"raw_vec::capacity_overflow",
            r"core::slice::index::", r"core::str::slice_error_fail", r"rust_begin_unwind",
            r"core::cell::panic_already", r"::assert_failed", r"core::slice::<impl \[T\]>::copy_from_slice::len_mismatch_fail",
            r"core::fmt::", r"<.* as core::fmt::Debug>::fmt", r"<.* as core::fmt::Display>::fmt",
            r"log::__private_api", r"log::logger"]
root = None
if "--fmt-not-terminal" in args:
    args.remove("--fmt-not-terminal")
    terminal = [t for t in terminal if "fmt" not in t]
rlibs = []
i = 0
while i < len(args):
    if args[i] == "--terminal":
        terminal.append(args[i + 1]); i += 2; continue
    if root is None:
        root = args[i]
    else:
        rlibs.append(args[i])
    i += 1
term_re = re.compile("|".join(terminal))

work = tempfile.mkdtemp(prefix="stackdepth-")
atexit.register(shutil.rmtree, work, True)
objs = []
for k, r in enumerate(rlibs):
    d = os.path.join(work, str(k))
    os.makedirs(d)
    subprocess.check_call([AR, "x", os.path.abspath(r)], cwd=d)
    for f in os.listdir(d):
        if f.endswith(".o"):
            objs.append(os.path.join(d, f))

# defined text symbols -> object
defs = {}
for o in objs:
    out = subprocess.run([NM, "--defined-only", o], capture_output=True, text=True).stdout
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3 and p[1] in "TtWw":
            defs.setdefault(p[2], o)

def demangle(names):
    if not names:
        return {}
    out = subprocess.run([FILT], input="\n".join(names), capture_output=True, text=True).stdout
    return dict(zip(names, out.splitlines()))

FN_RE = re.compile(r"^[0-9a-f]+ <(.+)>:$")
INS_RE = re.compile(r"^\s*([0-9a-f]+):\s+(.*)$")
REL_RE = re.compile(r"^\s*[0-9a-f]+:\s+(R_AARCH64_\w+)\s+(\S+)")
parsed = {}   # obj -> {sym: info}

def parse_obj(o):
    if o in parsed:
        return parsed[o]
    out = subprocess.run([OBJDUMP, "-dr", "--no-show-raw-insn", o], capture_output=True, text=True).stdout
    fns = {}
    cur = None
    last_ins = ""
    for line in out.splitlines():
        m = FN_RE.match(line)
        if m:
            cur = {"frame": 0, "subs": [], "dyn": False, "calls": [], "ind": [], "n": 0}
            fns[m.group(1)] = cur
            continue
        if cur is None:
            continue
        r = REL_RE.match(line)
        if r:
            kind, tgt = r.group(1), r.group(2)
            tgt = re.sub(r"\+0x[0-9a-f]+$", "", tgt)
            if tgt.startswith(".text."):
                tgt = tgt[len(".text."):]
            tgt = re.sub(r"^(unlikely|hot|startup|exit|split)\.", "", tgt)
            if kind in ("R_AARCH64_CALL26", "R_AARCH64_JUMP26"):
                cur["calls"].append((tgt, kind == "R_AARCH64_JUMP26"))
            continue
        m = INS_RE.match(line)
        if not m:
            continue
        ins = m.group(2).split("//")[0].strip()
        cur["n"] += 1
        mm = re.match(r"(stp|str|stur)\s+.*\[sp, #-(0x[0-9a-f]+|\d+)\]!", ins)
        if mm:
            v = int(mm.group(2), 0); cur["frame"] += v; cur["subs"].append(v)
        mm = re.match(r"sub\s+sp, sp, #(0x[0-9a-f]+|\d+)(, lsl #12)?$", ins)
        if mm:
            v = int(mm.group(1), 0) << (12 if mm.group(2) else 0); cur["frame"] += v; cur["subs"].append(v)
        if re.match(r"sub\s+sp, sp, x", ins) or re.match(r"mov\s+sp, x(?!29)", ins):
            cur["dyn"] = True
        if re.match(r"(blr|br)\s+x", ins):
            cur["ind"].append(ins)
    parsed[o] = fns
    return fns

def info(sym):
    o = defs.get(sym)
    if o is None:
        return None
    return parse_obj(o).get(sym)

DMAP = demangle(list(defs))
@functools.lru_cache(maxsize=None)
def dm(s):
    return DMAP.get(s) or demangle([s]).get(s, s)

# find root
cands = [s for s in defs if re.sub(r"::h[0-9a-f]{16}$", "", dm(s)) == root]
if not cands:
    cands = [s for s in defs if root in dm(s)]
if len(cands) != 1:
    print("root candidates:", [dm(c) for c in cands][:20]); sys.exit(1)
R = cands[0]

undefined, dyn, indirect, cycles, terms = set(), set(), {}, set(), set()
memo, onstack = {}, set()
sys.setrecursionlimit(100000)

def depth(s):
    if s in memo:
        return memo[s]
    d = dm(s)
    if term_re.search(d):
        terms.add(d); memo[s] = (0, [d + "  [terminal]"]); return memo[s]
    f = info(s)
    if f is None:
        undefined.add(d); memo[s] = (0, [d + "  [undefined]"]); return memo[s]
    if s in onstack:
        cycles.add(d); return (0, [d + "  [cycle]"])
    onstack.add(s)
    if f["dyn"]:
        dyn.add(d)
    if f["ind"]:
        indirect[d] = f["ind"]
    best, bp = 0, []
    for (t, tail) in f["calls"]:
        if t == s:
            cycles.add(d); continue
        cd, cp = depth(t)
        if cd > best:
            best, bp = cd, cp
    onstack.discard(s)
    memo[s] = (f["frame"] + best, ["%s  [frame %d]" % (d, f["frame"])] + bp)
    return memo[s]

tot, path = depth(R)
print("root:", dm(R))
print("WORST-CASE DEPTH: %d bytes (%.1f KiB)" % (tot, tot / 1024))
print("functions reached:", len([k for k in memo if info(k)]))
print("\nworst path:")
for p in path:
    print("  ", p)
big = sorted(((info(k)["frame"], dm(k)) for k in memo if info(k)), reverse=True)[:12]
print("\nlargest frames:")
for fr, n in big:
    print("  %6d  %s" % (fr, n))
print("\ndynamic sp adjustments:", sorted(dyn) or "none")
print("cycles (recursion):", sorted(cycles) or "none")
print("indirect calls:")
for k, v in sorted(indirect.items()):
    print("   %s: %s" % (k, v))
print("undefined:", sorted(undefined))
print("terminal (not followed):", len(terms))

# forward pass: max stack depth at ENTRY of each reached function (bytes below the root's entry sp)
order, seen = [], set()
def post(s):
    if s in seen: return
    seen.add(s)
    f = info(s)
    if f is None or term_re.search(dm(s)): return
    for (t, _) in f["calls"]:
        if t != s: post(t)
    order.append(s)
post(R)
entry = collections.defaultdict(int); entry[R] = 0
callers = collections.defaultdict(set)
for s in reversed(order):
    f = info(s)
    for (t, _) in f["calls"]:
        if t == s: continue
        callers[t].add(s)
        entry[t] = max(entry[t], entry[s] + f["frame"])
watch = os.environ.get("WATCH")
if watch:
    print("\nentry depth (max over paths) of functions matching WATCH, + own frame:")
    for s in order:
        if re.search(watch, dm(s)):
            print("  entry %6d  frame %5d  %s  callers: %s" % (entry[s], info(s)["frame"], dm(s)[:150], [dm(c)[:90] for c in callers[s]][:4]))
    for t in list(entry):
        if info(t) is None and re.search(watch, dm(t)):
            print("  entry %6d  [undefined] %s  callers: %s" % (entry[t], dm(t)[:120], [dm(c)[:80] for c in callers[t]][:3]))
