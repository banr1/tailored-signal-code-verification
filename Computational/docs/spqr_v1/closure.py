#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Call-closure measurement on the REAL rung-7b image (`GeneratedLean/LibsignalSessionObj.{lean,code.bin}`).
Untrusted tooling (numbers only). A copy of `third_party/libsignal/libsignal-session/tools/closure.py`
whose `reach` matches root names exactly instead of as substrings. `closure.txt` next to it is

    closure.py .GeneratedLean/GeneratedLean reach 'spqr::send::<libsignal_session::HookRng>' 'spqr::recv'

on the image whose `LibsignalSessionObj.code.bin` has SHA-256 prefix `ded40fcf5568`.

usage: closure.py GENDIR list SUBSTR            # list functions matching
       closure.py GENDIR reach ROOT... [--stop SUBSTR]...   # closure from roots (exact names)
       closure.py GENDIR fn SUBSTR             # per-function detail (callees, loops)
Closure stops at extern stubs (hooks) and at --stop substrings (already-verified / hooked).
"""
import re, sys, os, subprocess, json, hashlib, collections, shutil

gen = sys.argv[1]
mode = sys.argv[2]
args = sys.argv[3:]
here = os.environ.get("CLOSURE_CACHE", "/tmp")
objl = open(os.path.join(gen, "LibsignalSessionObj.lean")).read()
code = open(os.path.join(gen, "LibsignalSessionObj.code.bin"), "rb").read()
h = hashlib.sha256(code).hexdigest()[:16]
elf = os.path.join(here, f"s2code_{h}.elf")
def llvm_objcopy():
    """`$LLVM_OBJCOPY`, else `llvm-objcopy` on PATH, else the rustup 1.98.1 x86_64 host copy."""
    return (os.environ.get("LLVM_OBJCOPY") or shutil.which("llvm-objcopy") or os.path.expanduser(
        "~/.rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objcopy"))
if not os.path.exists(elf):
    subprocess.check_call([
        llvm_objcopy(),
        "-I", "binary", "-O", "elf64-littleaarch64",
        "--rename-section", ".data=.text,alloc,code,load,readonly",
        os.path.join(gen, "LibsignalSessionObj.code.bin"), elf])
cache = elf + ".dis"
if not os.path.exists(cache):
    out = subprocess.check_output(["llvm-objdump", "-d", "--no-show-raw-insn", elf], text=True)
    open(cache, "w").write(out)
dis = {}
for line in open(cache):
    m = re.match(r"\s+([0-9a-f]+):\s+(\S+)\s*(.*)", line)
    if m:
        dis[int(m.group(1), 16)] = (m.group(2), m.group(3))

syms = re.findall(r'^\s*\("((?:[^"\\]|\\.)*)", (\d+)\),?\]?$', objl, re.M)
stubnames = set()
# stubs are the zero-size externs at the end of code (4-byte trampolines)
ext = set(re.findall(r'^\* `(.*)` \((?:func|object), \d+ bytes\)', objl, re.M))
byoff = collections.defaultdict(list)
for n, o in syms:
    byoff[int(o)].append(n)
offs = sorted(byoff)
funcs = {}
for i, o in enumerate(offs):
    end = offs[i + 1] if i + 1 < len(offs) else len(code)
    for n in byoff[o]:
        funcs[n] = (o, end - o)
def name_at(o):
    return byoff[o][0] if o in byoff else None
def is_stub(n):
    return n in ext

def analyse(n):
    o, sz = funcs[n]
    calls, tails, blr, br, back, odd = [], [], 0, 0, 0, collections.Counter()
    for a in range(o, o + sz, 4):
        if a not in dis:
            odd["<undecoded>"] += 1
            continue
        mn, ops = dis[a]
        tgt = None
        mm = re.findall(r"(?<!#)0x([0-9a-f]+)", ops); m = mm[-1] if mm else None
        if mn in ("bl",) and m:
            calls.append(int(m, 16))
        elif mn == "blr":
            blr += 1
        elif mn == "br":
            br += 1
        elif (mn == "b" or mn.startswith("b.") or mn in ("cbz", "cbnz", "tbz", "tbnz")) and m:
            t = int(m, 16)
            if o <= t < o + sz:
                if t <= a:
                    back += 1
            elif mn == "b":
                tails.append(t)
            else:
                tails.append(t)
        if re.match(r"(ldadd|ldxr|stxr|ldaxr|stlxr|cas|swp|ldset|ldclr|pmull|aes|sha|dmb|dsb|isb|svc|hvc|mrs|msr|ld1|st1|ld2|st2|ld4|st4|tbl|ext|rev64|eor3|udf|hint|brk)", mn):
            odd[mn] += 1
    return dict(off=o, insns=sz // 4, calls=calls, tails=tails, blr=blr, br=br, back=back, odd=odd)

def short(n, k=110):
    return n if len(n) <= k else n[:k] + "…"

if mode == "list":
    for n, (o, sz) in sorted(funcs.items(), key=lambda x: x[1][0]):
        if all(s in n for s in args):
            print(f"{o:#07x} {sz//4:5d} {'STUB ' if is_stub(n) else ''}{short(n,200)}")
elif mode == "fn":
    for n in funcs:
        if args[0] in n:
            a = analyse(n)
            print(f"# {n} @ {a['off']:#x}: {a['insns']} insns, blr {a['blr']}, br {a['br']}, back-edges {a['back']}, odd {dict(a['odd'])}")
            for t in collections.Counter(a["calls"]):
                print("   bl ", short(name_at(t) or hex(t)))
            for t in set(a["tails"]):
                print("   b→ ", short(name_at(t) or hex(t)))
elif mode == "reach":
    roots, stops = [], []
    it = iter(args)
    for x in it:
        if x == "--stop":
            stops.append(next(it))
        else:
            roots.append(x)
    todo = []
    for r in roots:
        c = [n for n in funcs if r == n and not is_stub(n)]
        if not c:
            sys.exit(f"no root {r}")
        todo += c
    seen, hooks, stopped = {}, collections.Counter(), collections.Counter()
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        a = analyse(n)
        seen[n] = a
        for t in a["calls"] + a["tails"]:
            m = name_at(t)
            if m is None:
                hooks["<unnamed " + hex(t) + ">"] += 1
                continue
            if is_stub(m):
                hooks[m] += 1
            elif any(s in m for s in stops):
                stopped[m] += 1
            else:
                todo.append(m)
    tot = sum(a["insns"] for a in seen.values())
    print(f"## closure: {len(seen)} functions, {tot} insns, bl {sum(len(a['calls']) for a in seen.values())}, "
          f"blr {sum(a['blr'] for a in seen.values())}, br {sum(a['br'] for a in seen.values())}, "
          f"loops-in {sum(1 for a in seen.values() if a['back'])} fns ({sum(a['back'] for a in seen.values())} back-edges)")
    odd = collections.Counter()
    for a in seen.values():
        odd.update(a["odd"])
    print("## odd mnemonics:", dict(odd))
    for n, a in sorted(seen.items(), key=lambda x: -x[1]["insns"]):
        print(f"{a['insns']:5d} blr{a['blr']} br{a['br']} back{a['back']:2d} {short(n,150)}")
        if os.environ.get("FULLNAMES"): open(os.environ["FULLNAMES"], "a").write(n + "\n")
    print("## hooks (extern stubs) reached:")
    for n, c in hooks.most_common():
        print(f"  {c:3d} {short(n,150)}")
    print("## stopped at (verified/hooked boundary):")
    for n, c in stopped.most_common():
        print(f"  {c:3d} {short(n,150)}")
