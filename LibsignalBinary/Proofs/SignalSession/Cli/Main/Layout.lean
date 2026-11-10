/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top

/-!
# Stack Frame and Data Layouts for `signal-session` `main`

Separation-logic layouts for `main`'s 0x4e0-byte stack frame, `argv` slice buffers, 56-byte `Call`
enum, 320-byte `Stores` struct, installed coins globals, `.rodata` path literals (`mainLits`), and
`run`'s 0x158-byte `Result<(Stores, Vec<u8>), Rejected>` slot.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## Arguments -/

/-- A 16-byte `&[u8]` / `&str` fat pointer at `a` (pointer @0, length @8). -/
def sliceRefAt (a p : BitVec 64) (len : Nat) : SepProp :=
  (a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 len)

/-- Null-terminated `argv` array at `a` paired with each C string `(p, s)`. -/
def argvAtP : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ 0#64
  | a, (p, s) :: ps => (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAtP (a + 8#64) ps

/-- Heap buffer of `args: Vec<&[u8]>` holding `(pointer, length)` pairs for `argv[1..]`. -/
def argsBuf (A : RustAlloc) (cap buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) :
    SepProp :=
  vecBuf A 16 8 (fun pb a => sliceRefAt a pb.1 pb.2.length) cap buf ps

/-! ## `main`'s frame -/

/-- Total stack frame size of `main` (`0x60` saved registers + `0x480` locals = `0x4e0` bytes). -/
abbrev mainFrameSize : Nat := 0x4e0

/-- Callee-saved registers (`x19..x30`) stored at `s0.sp - 0x60 .. s0.sp` by `main`'s prologue. -/
def mainSaved (s0 : State) : SepProp :=
  let b := s0.sp - 0x60#64
  let w (k : Nat) (r : Reg) := (b + BitVec.ofNat 64 k) ↦₆₄ s0.readReg64 r
  w 0x00 .fp ∗ w 0x08 .lr ∗ w 0x10 (.gpr 28#5) ∗ w 0x18 (.gpr 27#5) ∗ w 0x20 (.gpr 26#5) ∗
    w 0x28 (.gpr 25#5) ∗ w 0x30 (.gpr 24#5) ∗ w 0x38 (.gpr 23#5) ∗ w 0x40 (.gpr 22#5) ∗
    w 0x48 (.gpr 21#5) ∗ w 0x50 (.gpr 20#5) ∗ w 0x58 (.gpr 19#5)

/-- Partition of `main`'s 0x480-byte local frame at `fsp = s0.sp - 0x4e0` into ordered non-overlapping
`(offset, size, P)` pieces separated by `memRegion` gaps. -/
def localsFrom (fsp : BitVec 64) : Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [] => memRegion (fsp + BitVec.ofNat 64 off) (0x480 - off)
  | off, (o, n, P) :: cs =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ P ∗ localsFrom fsp (o + n) cs

abbrev locals (fsp : BitVec 64) (cs : List (Nat × Nat × SepProp)) : SepProp :=
  localsFrom fsp 0 cs

abbrev cell (fsp : BitVec 64) (o : Nat) (v : BitVec 64) : Nat × Nat × SepProp :=
  (o, 8, (fsp + BitVec.ofNat 64 o) ↦₆₄ v)

/-! ## Owned Buffers and `Call` -/

/-- Heap payload of an owned `Vec<u8>` or `String` with header words `(cap, ptr, len)`. -/
def ownedBytes (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- Seven 64-bit words of `enum Call` (56 bytes). -/
structure CallW where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64

/-- Heap and padding invariant of a `ProtocolAddress` in four words `(cap, ptr, len, dev)`. -/
def addrWords (A : RustAlloc) (a : AddrV) (cap ptr len dev : BitVec 64) : SepProp :=
  ownedBytes A cap ptr len a.name ∗ ⌜dev.setWidth 8 = a.device⌝

/-- Heap ownership of `enum Call` given its seven words `w` (`Keygen` tag `2^63`, `Init` dataful
variant, `Send` tag `2^63 + 2`, `Recv` tag `2^63 + 3`). -/
def callHeap (A : RustAlloc) (w : CallW) : CallV → SepProp
  | .keygen me n =>
    ⌜w.w0 = 0x8000000000000000#64 ∧ w.w5.setWidth 32 = BitVec.ofNat 32 n⌝ ∗
      addrWords A me w.w1 w.w2 w.w3 w.w4
  | .init peer bundle =>
    addrWords A peer w.w0 w.w1 w.w2 w.w3 ∗ ownedBytes A w.w4 w.w5 w.w6 bundle
  | .send peer => ⌜w.w0 = 0x8000000000000002#64⌝ ∗ addrWords A peer w.w1 w.w2 w.w3 w.w4
  | .recv peer => ⌜w.w0 = 0x8000000000000003#64⌝ ∗ addrWords A peer w.w1 w.w2 w.w3 w.w4

def callAt (A : RustAlloc) (a : BitVec 64) (c : CallV) : SepProp :=
  ∃∗ w : CallW,
    (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
      ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗
      callHeap A w c

/-! ## Stores, Coins, and Read-Only Literals -/

/-- Layout of `Stores` at `a` (320 bytes): eight 40-byte `Dir` fields in commit order (`own`,
`peers`, `signed`, `kyberOneTime`, `kyberLastResort`, `oneTime`, `sessions`, `public`). -/
def storesAt (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A a g.identity.own ∗ dirAt A (a + 0x28#64) g.identity.peers ∗
    dirAt A (a + 0x50#64) g.signed ∗ dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗ dirAt A (a + 0xc8#64) g.oneTime ∗
    dirAt A (a + 0xf0#64) g.sessions ∗ dirAt A (a + 0x118#64) g.pub

/-- Installed PRNG coins state (`NEXT` pointer and `LEFT` byte count pointing to leaked `coins`). -/
def coinsInstalled (img : Obj.Image) (p : BitVec 64) (coins : List (BitVec 8)) : SepProp :=
  ((img.base + coinsNextOff) ↦₆₄ p) ∗
    ((img.base + coinsLeftOff) ↦₆₄ BitVec.ofNat 64 coins.length) ∗ (p ↦ₛ coins)

/-- Image offset of the `.rodata` string literal `"coins"`. -/
abbrev coinsLitOff : BitVec 64 := 0x991a8#64

/-- Image offsets and strings of the seven nonempty `Dir` path literals opened by `Stores::open()`. -/
def dirLits : List (BitVec 64 × String) :=
  [(0x98dd0#64, "identities"), (0x98d73#64, "signed-pre-keys"),
    (0x98d93#64, "one-time-kyber-pre-keys"), (0x98daa#64, "last-resort-kyber-pre-keys"),
    (0x98d82#64, "one-time-pre-keys"), (0x98dda#64, "sessions"), (0x98de2#64, "public")]

/-- Read-only `.rodata` literals (`↦ᵣ`) passed by address in `main`: `"coins"` and `dirLits`. -/
def mainLits (img : Obj.Image) : SepProp :=
  ((img.base + coinsLitOff) ↦ᵣ utf8 "coins") ∗
    (dirLits.foldr (fun l P => ((img.base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp)

/-! ## `run` Result Slot -/

/-- Byte size (`0x158`) of `run`'s `Result<(Stores, Vec<u8>), Rejected>` slot at `fsp + 0x1b8`. -/
abbrev runResSize : Nat := 0x158

/-- `Ok((stores, output))` layout at `r`: `storesAt` @0 (320 bytes) and `vecU8` @0x140 (24 bytes);
`Err(Rejected)` uses niche word 0 `= -1`. -/
def runOkAt (A : RustAlloc) (r : BitVec 64) (g : StoresGhost) (out : List (BitVec 8)) : SepProp :=
  storesAt A r g ∗ vecU8 A (r + 0x140#64) out

/-- Converts `(pathBytes, contents)` store writes into UTF-8 `(String, List (BitVec 8))` pairs. -/
def namedWrites (ws : List (List (BitVec 8) × List (BitVec 8))) : List (String × List (BitVec 8)) :=
  ws.map fun w => (String.fromUTF8! ⟨w.1.toArray.map fun b => b.toNat.toUInt8⟩, w.2)

/-- Layout of `run`'s result slot at `r` for `RunAnswer` (`Err` = word 0 `-1`; `Ok` = `runOkAt` with
named writes matching `a` and paths satisfying `wrOk`). -/
def runResAt (A : RustAlloc) (wrOk : List (BitVec 8) → Prop) (r : BitVec 64) : RunAnswer → SepProp
  | some none => (r ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (r + 8#64) (runResSize - 8)
  | some (some (w, out)) => ∃∗ g : StoresGhost,
      ⌜namedWrites g.writes = w ∧ ∀ pw ∈ g.writes, wrOk pw.1⌝ ∗ runOkAt A r g out
  | none => ⌜False⌝

end CryptoVerification.SignalSession.Cli.MainHops
