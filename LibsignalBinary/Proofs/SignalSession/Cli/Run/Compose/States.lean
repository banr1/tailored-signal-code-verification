/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Specifications.AsmConstants

/-!
# Machine-Level Hop States, Frame Splits, and Side-Condition Bridges for `signal_session::run`

Defines the named machine cut-point states (`AtRunEntry`, `AtDispatch`, `AtInit1`, `AtInit2`,
`AtJoin`, `AtReject`), stack-frame split/rejoin lemmas (`0x2a50` = `0x29f0` locals + `0x60` saved
registers), and semantic side-condition bridges used to decompose `signal_session::run`:

| State | Offset (`R+k`) | First instruction | Reached from |
|---|---|---|---|
| `AtRunEntry` | `R+0x0` | `stp x29, x30, [sp, #-0x60]!` | caller |
| `AtDispatch` | `R+0x214` | `cmp x8, #0x1` | `run_hop_pre` |
| `AtInit1` | `R+0x74c` | `ldr x26, [sp, #0x1c8]` | `run_hop_init1` (`IdentityKey::decode` `Ok`) |
| `AtInit2` | `R+0x28f0` | `bl signal_session_handshake::initiate` | `run_hop_init2` (`cliBundleAt` built) |
| `AtJoin` | `R+0xf8c` | `add x0, sp, #0x4d0` | `Send`, `Init3`, `RecvW`, `RecvP` accept |
| `AtReject` | `R+0x124` / `R+0x2c7c` | pre- or post-dispatch `drop_stores` + epilogue | `"address"` read `Err` (`0x124`) or arm reject (`0x2c7c`) |
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec

/-! ## 1. Program PCs, frame constants, and saved-register / local-frame combinators -/

/-- Local scratch region of `run`'s stack frame (`0x2a50 - 0x60 = 0x29f0 = 10736` bytes), below the
96-byte saved-register area `[s0.sp - 0x60 .. s0.sp)`. -/
abbrev runLocalBytes : Nat := 0x29f0

/-- Address `k` bytes past `signal_session::run`'s entry point in `mProg img ext`. -/
noncomputable abbrev runPc (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    BitVec 64 :=
  (mProg img ext).fnAddr runName + BitVec.ofNat 64 k

theorem runPc_zero (img : Obj.Image) (ext : String → Option (State → State)) :
    runPc img ext 0 = (mProg img ext).fnAddr runName := by
  simp [runPc]

/-- `run`'s 12 saved register words `[s0.sp - 0x60 .. s0.sp)` (`stp x29, x30, [sp, #-0x60]!` ..
`stp x20, x19, [sp, #0x50]` at `R+0x0..R+0x14`), identical layout to `main`'s prologue. -/
abbrev runSaved (s0 : State) : SepProp := MainHops.mainSaved s0

/-- `run`'s frame pointer value `s0.sp - 0x2a50#64` after the prologue (`R+0x0..R+0x2c`). -/
abbrev runFsp (s0 : State) : BitVec 64 := s0.sp - 0x2a50#64

/-- OOM continuation of every hop of `run`: vacuous (allocator failures route to `onPanic`). -/
def runOom (_s0 : State) : State → SepProp := fun _ => ⌜False⌝

/-- Panic predicate of `run`: either the abstract semantics panics (`g.a = none`) or an allocation
failed since `s0`. -/
def runPanicProp (g : RunCall) (s0 sf : State) : Prop :=
  g.a = none ∨ allocFailedIn s0 sf

/-- Common post-prologue machine invariant inside `run` at offset `R + k`. -/
structure InRun (img : Obj.Image) (ext : String → Option (State → State)) (s0 s : State)
    (k : Nat) : Prop where
  pc : s.pc = runPc img ext k
  run : s.status = .Running
  sp : s.sp = runFsp s0
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

theorem InRun.spAligned_cur {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : InRun img ext s0 s k) : s.spAligned = true := by
  have hs0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  have hfsp : (s0.sp - 0x2a50#64) &&& 15#64 = 0#64 := by
    bv_bits
  simp only [State.spAligned, h.sp, runFsp, hfsp, beq_self_eq_true]

/-- Owned pieces of `run`'s `0x29f0`-byte local frame at `fsp = runFsp s0`: `(offset, size, P)` in
non-overlapping increasing order, with `memRegion` filling all gaps up to `0x29f0`. -/
def runLocalsFrom (fsp : BitVec 64) : Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [] => memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off)
  | off, (o, n, P) :: cs =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ P ∗ runLocalsFrom fsp (o + n) cs

/-- `run`'s `0x29f0`-byte local frame starting at offset `0`. -/
abbrev runLocals (fsp : BitVec 64) (cs : List (Nat × Nat × SepProp)) : SepProp :=
  runLocalsFrom fsp 0 cs

/-- Well-formedness of a `runLocalsFrom` descriptor list: offsets are non-overlapping and bounded by
`runLocalBytes = 0x29f0`. -/
def RunLocalsFromWf : Nat → List (Nat × Nat × SepProp) → Prop
  | off, [] => off ≤ runLocalBytes
  | off, (o, n, _) :: cs => off ≤ o ∧ RunLocalsFromWf (o + n) cs

theorem runLocalsFrom_le {off : Nat} {cs : List (Nat × Nat × SepProp)}
    (hwf : RunLocalsFromWf off cs) : off ≤ runLocalBytes := by
  induction cs generalizing off with
  | nil => exact hwf
  | cons c cs ih =>
    rcases c with ⟨o, n, P⟩
    have hle : off ≤ o := hwf.1
    have hrest : o + n ≤ runLocalBytes := ih hwf.2
    omega

theorem runLocals_empty_eq (fsp : BitVec 64) :
    runLocals fsp [] = memRegion fsp runLocalBytes := by
  simp [runLocals, runLocalsFrom]

theorem runLocalsFrom_to_memRegion (fsp : BitVec 64) :
    ∀ (off : Nat) (cs : List (Nat × Nat × SepProp)),
      RunLocalsFromWf off cs →
      (∀ c ∈ cs, c.2.2 ⊢ memRegion (fsp + BitVec.ofNat 64 c.1) c.2.1) →
      runLocalsFrom fsp off cs ⊢
        memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off)
  | off, [], _, _ => Entails.refl _
  | off, (o, n, P) :: cs, hwf, hcells => by
    have hlb : runLocalBytes = 0x29f0 := rfl
    rcases hwf with ⟨hle, hwf'⟩
    have hon : o + n ≤ runLocalBytes := runLocalsFrom_le hwf'
    have hP : P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n :=
      hcells (o, n, P) (.head _)
    have htail : runLocalsFrom fsp (o + n) cs ⊢
        memRegion (fsp + BitVec.ofNat 64 (o + n)) (runLocalBytes - (o + n)) :=
      runLocalsFrom_to_memRegion fsp (o + n) cs hwf' (fun c hc => hcells c (.tail _ hc))
    have hstep1 :
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (runLocalBytes - (o + n)) =
        memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) := by
      have hsplit := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o) n
        (runLocalBytes - (o + n)) (by omega)
      have hlen : n + (runLocalBytes - (o + n)) = runLocalBytes - o := by omega
      have haddr : fsp + BitVec.ofNat 64 o + BitVec.ofNat 64 n =
          fsp + BitVec.ofNat 64 (o + n) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]
      simpa only [hlen, haddr] using hsplit.symm
    have hstep2 :
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) =
        memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off) := by
      have hsplit := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 off) (o - off)
        (runLocalBytes - o) (by omega)
      have hlen : (o - off) + (runLocalBytes - o) = runLocalBytes - off := by omega
      have haddr : fsp + BitVec.ofNat 64 off + BitVec.ofNat 64 (o - off) =
          fsp + BitVec.ofNat 64 o := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show off + (o - off) = o by omega]
      simpa only [hlen, haddr] using hsplit.symm
    rw [show runLocalsFrom fsp off ((o, n, P) :: cs) =
      memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ P ∗ runLocalsFrom fsp (o + n) cs from rfl,
      ← hstep2, ← hstep1]
    exact sepConj_mono_right (sepConj_mono hP htail)

/-- Collapse any well-formed local frame descriptor `cs` back to `runLocals fsp []`. -/
theorem runLocals_rejoin_empty (fsp : BitVec 64) (cs : List (Nat × Nat × SepProp))
    (hwf : RunLocalsFromWf 0 cs)
    (hcells : ∀ c ∈ cs, c.2.2 ⊢ memRegion (fsp + BitVec.ofNat 64 c.1) c.2.1) :
    runLocals fsp cs ⊢ runLocals fsp [] := by
  simpa [runLocals, runLocalsFrom] using runLocalsFrom_to_memRegion fsp 0 cs hwf hcells

/-! ## 2. Full `0x2a50` stack split, saved-register region, and stack rejoin -/

/-- Each `↦₆₄` cell entails its 8-byte `memRegion`. -/
theorem pointsTo64_entails_memRegion (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight]
  exact Entails.sepExists_intro v

private theorem memRegion_step8 (b : BitVec 64) (k : Nat) (hk : 8 + k ≤ 2 ^ 64) :
    memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
  ProofLib.memRegion_split b 8 k hk

/-- The 12 saved-register words at `s0.sp - 0x60#64` entail `memRegion (s0.sp - 0x60#64) 0x60`. -/
theorem runSaved_entails_memRegion (s0 : State) :
    runSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  let b := s0.sp - 0x60#64
  have split12 :
      memRegion b 0x60 =
        memRegion b 8 ∗ memRegion (b + 0x08#64) 8 ∗ memRegion (b + 0x10#64) 8 ∗
        memRegion (b + 0x18#64) 8 ∗ memRegion (b + 0x20#64) 8 ∗ memRegion (b + 0x28#64) 8 ∗
        memRegion (b + 0x30#64) 8 ∗ memRegion (b + 0x38#64) 8 ∗ memRegion (b + 0x40#64) 8 ∗
        memRegion (b + 0x48#64) 8 ∗ memRegion (b + 0x50#64) 8 ∗ memRegion (b + 0x58#64) 8 := by
    rw [memRegion_step8 b 88 (by decide),
      memRegion_step8 _ 80 (by decide),
      memRegion_step8 _ 72 (by decide),
      memRegion_step8 _ 64 (by decide),
      memRegion_step8 _ 56 (by decide),
      memRegion_step8 _ 48 (by decide),
      memRegion_step8 _ 40 (by decide),
      memRegion_step8 _ 32 (by decide),
      memRegion_step8 _ 24 (by decide),
      memRegion_step8 _ 16 (by decide),
      memRegion_step8 _ 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  change MainHops.mainSaved s0 ⊢ memRegion b 0x60
  rw [split12]
  simp only [MainHops.mainSaved, BitVec.add_zero]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))

/-- Prologue stack split (`R+0x0..R+0x2c`): `stackAt s0.sp resStack` splits cleanly into the
callee stack `stackAt (runFsp s0) (resStack - runFrame)`, the `0x29f0`-byte local frame
`memRegion (runFsp s0) runLocalBytes`, and the `0x60`-byte saved-register area
`memRegion (s0.sp - 0x60#64) 0x60`. -/
theorem stackAt_run_split (s0 : State) {resStack : Nat}
    (hframe : runFrame ≤ resStack) (h64 : resStack ≤ 2 ^ 64) :
    stackAt s0.sp resStack =
      stackAt (runFsp s0) (resStack - runFrame) ∗
        memRegion (runFsp s0) runLocalBytes ∗
        memRegion (s0.sp - 0x60#64) 0x60 := by
  have hrf : runFrame = 0x2a50 := rfl
  have hbot := ProofLib.stackAt_split_bottom s0.sp runFrame (resStack - runFrame) (by omega)
  have hsum : runFrame + (resStack - runFrame) = resStack := by omega
  rw [hsum] at hbot
  have hsub_stack :
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - runFrame) =
        stackAt (runFsp s0) (resStack - runFrame) := by
    unfold stackAt runFsp
    have haddr : s0.sp - BitVec.ofNat 64 resStack =
        s0.sp - 0x2a50#64 - BitVec.ofNat 64 (resStack - runFrame) := by
      have : resStack = 0x2a50 + (resStack - runFrame) := by omega
      rw [this, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
  have htop :
      stackAt s0.sp runFrame =
        memRegion (runFsp s0) runLocalBytes ∗ memRegion (s0.sp - 0x60#64) 0x60 := by
    unfold stackAt runFsp
    have hsp := ProofLib.memRegion_split (s0.sp - 0x2a50#64) runLocalBytes 0x60 (by decide)
    have haddr : s0.sp - 0x2a50#64 + BitVec.ofNat 64 runLocalBytes = s0.sp - 0x60#64 := by
      have : runLocalBytes = 0x29f0 := rfl
      rw [this]
      bv_omega
    simpa only [show runFrame = runLocalBytes + 0x60 from rfl, BitVec.ofNat_eq_ofNat, haddr]
      using hsp
  rw [hbot, hsub_stack, htop]

/-- Epilogue stack rejoin (`R+0x2c84..R+0x2ca4` and `R+0x184..R+0x1a0`): `runSaved s0`, the local
frame `runLocals (runFsp s0) []`, and `stackAt (runFsp s0) (resStack - runFrame)` rejoin to the
caller's full `stackAt s0.sp resStack` with zero leaked bytes. -/
theorem stackAt_run_rejoin (s0 : State) {resStack : Nat}
    (hframe : runFrame ≤ resStack) (h64 : resStack ≤ 2 ^ 64) :
    runSaved s0 ∗ runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame) ⊢
      stackAt s0.sp resStack := by
  rw [runLocals_empty_eq, stackAt_run_split s0 hframe h64]
  have hperm :
      stackAt (runFsp s0) (resStack - runFrame) ∗
          memRegion (runFsp s0) runLocalBytes ∗ memRegion (s0.sp - 0x60#64) 0x60 =
        memRegion (s0.sp - 0x60#64) 0x60 ∗
          memRegion (runFsp s0) runLocalBytes ∗ stackAt (runFsp s0) (resStack - runFrame) := by
    ac_rfl
  rw [hperm]
  exact sepConj_mono_left (runSaved_entails_memRegion s0)

/-! ## 3. Decomposing and rejoining `protocolAddressAt` and 32-byte `IdentityKey` words -/

/-- Heap-only ownership of `meG.name` (separated from the 24-byte `Vec` header). -/
def addrNameHeap (A : RustAlloc) (g : AddrGhost) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
    if g.name.cap = 0 then emp
    else A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length)

/-- The upper 16 bytes `[a + 16 .. a + 32)` of `protocolAddressAt A g a` (`len` word at `+0`,
`device` byte at `+8`, 7 padding bytes at `+9 .. +16`), which `run` copies with `ldr q0` / `str q0`
between `[sp + 0x1760]`, `[sp + 0x1d0]`, `[sp + 0x260]`, and the call-site `ProtocolAddress` slot. -/
def addrUpperAt (a : BitVec 64) (g : AddrGhost) : SepProp :=
  (a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
    ((a + 8#64) ↦₈ g.device) ∗
    memRegion (a + 9#64) 7

theorem addrUpperAt_entails_memRegion (a : BitVec 64) (g : AddrGhost) :
    addrUpperAt a g ⊢ memRegion a 16 := by
  unfold addrUpperAt
  have h1 : ((a + 8#64) ↦₈ g.device) ⊢ memRegion (a + 8#64) 1 := by
    rw [Path.Helpers.memRegion_1_eq_pointsTo8]
    exact Entails.sepExists_intro g.device
  have h8 : memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 7 = memRegion (a + 8#64) 8 := by
    have hs := ProofLib.memRegion_split (a + 8#64) 1 7 (by decide)
    have ha : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
    simpa only [BitVec.ofNat_eq_ofNat, ha] using hs.symm
  have h16 : memRegion a 8 ∗ memRegion (a + 8#64) 8 = memRegion a 16 :=
    (ProofLib.memRegion_split a 8 8 (by decide)).symm
  rw [← h16, ← h8]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_left h1)

/-- Exact split & rejoin equivalence between `protocolAddressAt A g a` and `(cap, ptr)` words plus
`addrUpperAt (a + 16#64) g` plus `addrNameHeap A g`. -/
theorem protocolAddressAt_eq_parts (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        addrUpperAt (a + 16#64) g ∗ addrNameHeap A g := by
  unfold protocolAddressAt vecGhostAt vecU8At vecHeader addrUpperAt addrNameHeap
  have ha24 : a + 16#64 + 8#64 = a + asm64% addrDeviceOff := by bv_omega
  have ha25 : a + 16#64 + 9#64 = a + asm64% (addrDeviceOff + 1) := by bv_omega
  rw [ha24, ha25]
  ac_rfl

/-- Four 64-bit words holding a 32-byte key slice (`IdentityKey::decode` output words read at
`R+0x714..R+0x720` and written to `cliBundleAt` at `R+0x284c, R+0x287c, R+0x2884, R+0x288c`). -/
def Words32Eq (bs : Bytes) (w0 w1 w2 w3 : BitVec 64) : Prop :=
  ∀ a : BitVec 64,
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) =
      (a ↦ₛ bs)

/-! ## 4. Callee stack-budget bounds from `runNeed` -/

private theorem foldr_max_le {l : List Nat} {m : Nat}
    (h : l.foldr max 0 ≤ m) : ∀ k ∈ l, k ≤ m := by
  induction l with
  | nil => intro _ hk; cases hk
  | cons a l ih =>
    have hmax : max a (l.foldr max 0) ≤ m := h
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hmem
    · exact Nat.le_trans (Nat.le_max_left _ _) hmax
    · exact ih (Nat.le_trans (Nat.le_max_right _ _) hmax) k hmem

/-- Every direct callee budget in `runCalleeNeed` (plus `< 2^63` / `≤ 2^64`) follows from
`runNeed B (slotsOf A img S needs) ≤ resStack` and `resStack ≤ 2 ^ 63`. -/
theorem runNeed_bounds {A : RustAlloc} {img : Obj.Image} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    let sub := resStack - runFrame
    runFrame ≤ resStack ∧
      sub ≤ 2 ^ 63 ∧
      sub ≤ 2 ^ 64 ∧
      0xB0 + extHookStack ≤ sub ∧
      finishGrowStackX ≤ sub ∧
      B.readFile ≤ sub ∧
      pathNeed ≤ sub ∧
      B.dirGetNeed ≤ sub ∧
      B.bundleReadNeed ≤ sub ∧
      splitIdNeed ≤ sub ∧
      splitSignedNeed ≤ sub ∧
      0x60 ≤ sub ∧
      smallRootStack ≤ sub ∧
      CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ sub ∧
      32 + extHookStack ≤ sub ∧
      96 + extHookStack ≤ sub ∧
      extHookStack ≤ sub ∧
      needs.encrypt ≤ sub ∧
      needs.decryptSignal ≤ sub ∧
      needs.initiate ≤ sub ∧
      needs.decryptPrekey ≤ sub ∧
      48 + extHookStack ≤ sub := by
  have hrf : runFrame ≤ resStack := Nat.le_trans (Nat.le_add_right _ _) hres
  have hcn : runCalleeNeed B (slotsOf A img S needs) ≤ resStack - runFrame := by
    unfold runNeed at hres
    omega
  have hm := foldr_max_le hcn
  have hkem : (slotsOf A img S needs).kemDeserialize.need = 48 + extHookStack := rfl
  refine ⟨hrf, by omega, by omega,
    hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp),
    hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp),
    hm _ (by simp), hm _ (by simp), hm _ (by simp), hm _ (by simp),
    hm _ (by simp), hm _ (by simp),
    hm _ (by simp [slotsOf, mkSlot]), hm _ (by simp [slotsOf, mkSlot]),
    hm _ (by simp [slotsOf, mkSlot]), hm _ (by simp [slotsOf, mkSlot]),
    hkem ▸ hm _ (by simp)⟩

/-! ## 5. Named machine boundary states of `signal_session::run` -/

/-- Entry state at `R + 0x0`: `run`'s ABI registers and precondition assertions from
`(runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img`. -/
structure AtRunEntry (S : RunSem) (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (s0 : State) : Prop where
  pc : s0.pc = runPc img ext 0
  run : s0.status = .Running
  inv : ImgCallInv img s0
  spAligned : s0.spAligned = true
  rel : runRel S g.i g.a
  parse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c
  x0 : s0.readReg64 .x0 = g.res
  x1 : s0.readReg64 .x1 = g.call
  x2 : s0.readReg64 .x2 = g.stores
  x3 : s0.readReg64 .x3 = g.inp
  x4 : s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length
  fs : s0.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s0.trace = []

/-- Entry spatial footprint of `run`. -/
def runEntryMem (A : RustAlloc) (img : Obj.Image) (g : RunCall) (s0 : State)
    (resStack : Nat) : SepProp :=
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
    A.pool ∗ stackAt s0.sp resStack

/-- Outcome of `E0` (`me = address(&s.identity.address()?)`) when execution reaches `AtDispatch`
(`R+0x214`): either `address` parsed `ownB` into `(meV, meG)`, or `address` returned `None`.
(`Dir::get("address")` returning `Err` branches earlier at `R+0x74` straight to pre-dispatch
`AtReject` at `R + 0x124`.) -/
inductive MeAtDispatch : Type where
  | none : MeAtDispatch
  | some (meV : AddrV) (meG : AddrGhost) : MeAtDispatch

/-- Local stack cells live at `AtDispatch` (`R + 0x214`): `[fsp + 0x1d0 .. fsp + 0x1e0)` holds the
upper 16 bytes of `meG` when `me = some (meV, meG)`, and nothing when `me = none`. -/
def dispatchCells (fsp : BitVec 64) : MeAtDispatch → List (Nat × Nat × SepProp)
  | .none => []
  | .some _ meG => [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)]

/-- Extra heap ownership carried at `AtDispatch` (`meG.name`'s buffer when `me = some`). -/
def dispatchMeHeap (A : RustAlloc) : MeAtDispatch → SepProp
  | .none => emp
  | .some _ meG => addrNameHeap A meG

/-- Post-own-address-check dispatch state at `R + 0x214` (`cmp x8, #0x1`): `x8 = g.c.tag`,
`x19 = g.stores`, `x20 = g.res`, `x23 = g.inp`, `x24 = (inputOf g.i g.c).length`, `x25 = g.call`,
`x26 = fsp + 0x4d0`, `x27 = fsp + 0x1750`, with `ownB` read from `"address"` and parsed as `me`. -/
structure AtDispatch (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (me : MeAtDispatch) (s0 s : State) : Prop where
  base : InRun img ext s0 s 0x214
  x8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.c.tag
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x23 : s.readReg64 (.gpr 23#5) = g.inp
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length
  x25 : s.readReg64 (.gpr 25#5) = g.call
  x26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64
  x27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64
  meRegs : match me with
    | .none => s.readReg64 (.gpr 21#5) = noneCap
    | .some meV meG =>
      s.readReg64 (.gpr 21#5) = meG.name.cap ∧
        s.readReg64 (.gpr 28#5) = meG.name.ptr ∧
        meG.name.bytes = meV.name ∧
        meG.name.cap = BitVec.ofNat 64 meV.name.length ∧
        meG.device = meV.device
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      match me with
      | .none => addrParse uuidTryParse ownB = Option.none
      | .some meV _ => addrParse uuidTryParse ownB = Option.some meV
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtDispatch` (`R + 0x214`). -/
def dispatchMem (A : RustAlloc) (img : Obj.Image) (g : RunCall) (me : MeAtDispatch)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
    dispatchMeHeap A me ∗
    runSaved s0 ∗ runLocals fsp (dispatchCells fsp me) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool

/-- Ghost state at `AtInit1` (`R + 0x74c`): `Call.init peerV dir` unpacked, `me` parsed, and
`identity-key` decoded to `idKey` with its 32-byte public key split across
`(ikW0 @ 0x180, ikW1 @ 0x1a8, ikW2 in x22, ikW3 @ 0x190)`. -/
structure Init1Data where
  peerV : AddrV
  peerG : AddrGhost
  meV : AddrV
  meG : AddrGhost
  dir : Bytes
  dirCap : BitVec 64
  dirPtr : BitVec 64
  idKey : IdentityKey
  ikW0 : BitVec 64
  ikW1 : BitVec 64
  ikW2 : BitVec 64
  ikW3 : BitVec 64

/-- Live local stack slots at `AtInit1` (`R+0x74c`), in strictly increasing offset order. -/
def init1Cells (A : RustAlloc) (fsp : BitVec 64) (d : Init1Data) : List (Nat × Nat × SepProp) :=
  [ (0x180, 8,  (fsp + 0x180#64) ↦₆₄ d.ikW0),
    (0x190, 8,  (fsp + 0x190#64) ↦₆₄ d.ikW3),
    (0x1a8, 8,  (fsp + 0x1a8#64) ↦₆₄ d.ikW1),
    (0x1b0, 4,  (fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32),
    (0x1b8, 8,  (fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr),
    (0x1c0, 8,  (fsp + 0x1c0#64) ↦₆₄ d.dirCap),
    (0x1c8, 8,  (fsp + 0x1c8#64) ↦₆₄ d.dirPtr),
    (0x260, 16, addrUpperAt (fsp + 0x260#64) d.meG),
    (0x2a0, 32, protocolAddressAt A d.peerG (fsp + 0x2a0#64)) ]

/-- Init checkpoint 1 (`R + 0x74c`): reached after `read("identity-key")` and
`IdentityKey::decode` succeed (`R1a` → `R1b` seam). -/
structure AtInit1 (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (d : Init1Data) (s0 s : State) : Prop where
  base : InRun img ext s0 s 0x74c
  callEq : g.c = .init d.peerV d.dir
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  x22 : s.readReg64 (.gpr 22#5) = d.ikW2
  x28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length
  peerVal : d.peerG.val = addrValOf d.peerV
  meVal : d.meG.val = addrValOf d.meV
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      addrParse uuidTryParse ownB = some d.meV
  ikSem : ∃ ikB : Bytes,
    bundleFile (runFiles g.i) d.dir "identity-key" = some ikB ∧
      exceptOpt (decodeIdentityKey ikB) = some d.idKey
  ikWords : Words32Eq d.idKey.publicKey.bytes.toList d.ikW0 d.ikW1 d.ikW2 d.ikW3
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtInit1` (`R + 0x74c`). -/
def init1Mem (A : RustAlloc) (img : Obj.Image) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
    addrNameHeap A d.meG ∗
    ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
    runSaved s0 ∗ runLocals fsp (init1Cells A fsp d) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool

/-- Ghost state at `AtInit2` (`R + 0x28f0`): `PreKeyBundle` (`b : BundleV`) assembled as
`cliBundleAt` at `fsp + 0x4d0`, with the three heap allocations (`spkSigPtr`, `kpkSigPtr`,
`kpkPtr`) live for deallocation after `initiate`. -/
structure Init2Data where
  peerV : AddrV
  peerG : AddrGhost
  meV : AddrV
  meG : AddrGhost
  dir : Bytes
  dirCap : BitVec 64
  dirPtr : BitVec 64
  bundle : BundleV
  spkSigPtr : BitVec 64
  kpkSigPtr : BitVec 64
  kpkPtr : BitVec 64

/-- Live local stack slots at `AtInit2` (`R+0x28f0: bl signal_session_handshake::initiate`), in
strictly increasing offset order. -/
def init2Cells (A : RustAlloc) (fsp : BitVec 64) (d : Init2Data) : List (Nat × Nat × SepProp) :=
  [ (0x000, 4,   fsp ↦₃₂ 0#32),
    (0x110, 8,   (fsp + 0x110#64) ↦₆₄ d.spkSigPtr),
    (0x120, 8,   (fsp + 0x120#64) ↦₆₄ 64#64),
    (0x138, 8,   (fsp + 0x138#64) ↦₆₄ d.kpkSigPtr),
    (0x140, 8,   (fsp + 0x140#64) ↦₆₄ 1568#64),
    (0x158, 8,   (fsp + 0x158#64) ↦₆₄ 64#64),
    (0x178, 8,   (fsp + 0x178#64) ↦₆₄ d.kpkPtr),
    (0x1b8, 8,   (fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr),
    (0x1c0, 8,   (fsp + 0x1c0#64) ↦₆₄ d.dirCap),
    (0x1c8, 8,   (fsp + 0x1c8#64) ↦₆₄ d.dirPtr),
    (0x2a0, 32,  protocolAddressAt A d.peerG (fsp + 0x2a0#64)),
    (0x320, 32,  protocolAddressAt A d.meG (fsp + 0x320#64)),
    (0x4d0, 192, cliBundleAt (fsp + 0x4d0#64) d.bundle d.spkSigPtr d.kpkSigPtr d.kpkPtr),
    (0x23b0, 48, memRegion (fsp + 0x23b0#64) 48) ]

/-- Init checkpoint 2 (`R + 0x28f0`): ABI registers staged for `initSlotSpec`, `readBundleV`
succeeded with `d.bundle`, and the three heap buffers have lengths `(64, 64, 1568)` (`R1b` → `R1c`
seam). -/
structure AtInit2 (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (d : Init2Data) (s0 s : State) : Prop where
  base : InRun img ext s0 s 0x28f0
  callEq : g.c = .init d.peerV d.dir
  x0 : s.readReg64 .x0 = runFsp s0 + 0x2a0#64
  x1 : s.readReg64 .x1 = runFsp s0 + 0x320#64
  x2 : s.readReg64 .x2 = g.stores + 0xf0#64
  x3 : s.readReg64 .x3 = sessVt img
  x4 : s.readReg64 .x4 = g.stores
  x5 : s.readReg64 .x5 = idVt img
  x6 : s.readReg64 .x6 = runFsp s0 + 0x4d0#64
  x7 : s.readReg64 .x7 = 0#64
  x8 : s.readReg64 .x8 = runFsp s0 + 0x23b0#64
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  peerVal : d.peerG.val = addrValOf d.peerV
  meVal : d.meG.val = addrValOf d.meV
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      addrParse uuidTryParse ownB = some d.meV
  bundleSem : readBundleV (runFiles g.i) d.dir d.peerV.device = some d.bundle
  ptrsNeZero : d.spkSigPtr ≠ 0 ∧ d.kpkSigPtr ≠ 0 ∧ d.kpkPtr ≠ 0
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtInit2` (`R + 0x28f0`). -/
def init2Mem (A : RustAlloc) (img : Obj.Image) (g : RunCall) (d : Init2Data)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
    A.live d.spkSigPtr 64 1 ∗ A.live d.kpkSigPtr 64 1 ∗ A.live d.kpkPtr 1568 1 ∗
    ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
    runSaved s0 ∗ runLocals fsp (init2Cells A fsp d) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool

/-- History invariant on exit paths of `run` (`AtJoin`, `AtReject`, `runPost`): files are
`runFiles i` (`(initFsState (cliInputs i)).files`) and stdout is empty. -/
abbrev RunHistOk (i : Inputs) (_s0 s : State) : Prop :=
  s.fs.files = runFiles i ∧
    ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Accept join point (`R + 0xf8c`): arm temporaries have been freed, `storesAt A g.stores g'` is
in `x19`, `out` is in `[fsp + 0x208 .. fsp + 0x220)`, and `x20 = g.res` before copying into `g.res`
and branching to the shared epilogue (`R+0x2c84..R+0x2ca4`). -/
structure AtJoin (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (g' : StoresGhost) (out : Bytes) (s0 s : State) : Prop where
  base : InRun img ext s0 s 0xf8c
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  trace : s0.trace <+: s.trace
  hist : RunHistOk g.i s0 s
  ans : g.a = some (some (namedWrites g'.writes, out))
  wrOk : ∀ pw ∈ g'.writes, cliWrOk pw.1

/-- Spatial footprint at `AtJoin` (`R + 0xf8c`). -/
def joinMem (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (out : Bytes)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    runSaved s0 ∗ runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) out)] ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap

/-- Selects between `run`'s two reject epilogues:
* `.preDispatch` (`R + 0x124`): reached when `Dir::get("address")` returns `Err` before `Call` is
  unpacked;
* `.postDispatch` (`R + 0x2c7c`): reached after `-1` is written to `[g.res]` and `Call`'s heap
  fields are freed. -/
inductive RejectKind : Type where
  | preDispatch : RejectKind
  | postDispatch : RejectKind

/-- PC offset of each `RejectKind`. -/
def RejectKind.pcOff : RejectKind → Nat
  | .preDispatch => 0x124
  | .postDispatch => 0x2c7c

/-- Reject cut-point state (`R + 0x2c7c` or `R + 0x124`). -/
structure AtReject (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (g' : StoresGhost) (rk : RejectKind) (s0 s : State) : Prop where
  base : InRun img ext s0 s rk.pcOff
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  preRegs : rk = .preDispatch →
    s.readReg64 (.gpr 20#5) = g.res ∧ s.readReg64 (.gpr 25#5) = g.call
  trace : s0.trace <+: s.trace
  hist : RunHistOk g.i s0 s
  ans : g.a = some none

/-- Spatial footprint at `AtReject`. -/
def rejectMem (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (rk : RejectKind)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  let resCall : SepProp :=
    match rk with
    | .preDispatch => memRegion g.res runResSize ∗ callAt A g.call g.c
    | .postDispatch => runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56
  resCall ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    runSaved s0 ∗ runLocals fsp [] ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap

/-- Concrete normal-return postcondition established by `run_hop_join` at `s0.readReg64 .lr`. -/
def runPost (A : RustAlloc) (img : Obj.Image) (g : RunCall) (resStack : Nat)
    (s0 sf : State) (Pf : SepProp) : Prop :=
  ImgCallInv img sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    s0.trace <+: sf.trace ∧ RunHistOk g.i s0 sf ∧
    ∃ a' : RunAnswer, a' ≠ none ∧ a' = g.a ∧
      (Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ A.pool ∗ stackAt s0.sp resStack ∗
        runResAt A cliWrOk g.res a' ∗ anyHeap)

/-! ## 6. Entry / Exit `Spec.inImage` Bridge Lemmas -/

/-- Postcondition weakening for `ProofLib.SepWPp` along normal returns (`Q → Q'`). -/
theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : ProofLib.SepWPp prog ret s P Q Qp oom) :
    ProofLib.SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hp⟩ | hrest⟩ := h R hm hL
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hp⟩⟩
  · exact ⟨sf, hs, Or.inr hrest⟩

theorem runEntry_of_inImage_pre {S : RunSem} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {resStack : Nat} {R : SepProp}
    {s0 : State}
    (hpc : s0.pc = (mProg img ext).fnAddr runName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).pre g s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntry S img ext g s0 ∧ (s0.mem ⊨ runEntryMem A img g s0 resStack ∗ R) := by
  simp only [Spec.inImage, runSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout, _hspb⟩, hmem⟩
  refine ⟨⟨?_, hrun, hinv, hsp, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout⟩, ?_⟩
  · simpa [runPc] using hpc
  · simpa only [runEntryMem, sepConj_assoc] using hmem

theorem inImage_post_of_runPost {S : RunSem} {A : RustAlloc} {img : Obj.Image}
    {g : RunCall} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPost A img g resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨ ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).post g s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  rcases hp with ⟨_, hsp, hcs, htr, ⟨hf, ho⟩, a', ha_ne, ha_eq, hent⟩
  refine ⟨?_, hsp, hcs⟩
  have hex :
      runResAt A cliWrOk g.res a' ⊢
        ∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A cliWrOk g.res a'' :=
    Entails.sepExists_right a' (Entails.pure_right ⟨ha_ne, ha_eq⟩ (Entails.refl _))
  have hent' :
      Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool ∗ stackAt s0.sp resStack ∗
        (∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A cliWrOk g.res a'') ∗
        anyHeap :=
    Entails.trans hent
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex))))))
  have hmem1 := Satisfies.mono (sepConj_mono_left hent') hmf
  simp only [Spec.inImage, runSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr, hf.trans hfs0.symm, ho.trans hout0.symm⟩, by simpa only [sepConj_assoc] using hmem1⟩

theorem inImage_onPanic_of_runPanic {S : RunSem} {A : RustAlloc} {img : Obj.Image}
    {g : RunCall} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).onPanic g s0 sf ∗ R := by
  simp only [Spec.inImage, runSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpan, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf⟩

theorem inImage_onOom_eq {S : RunSem} {A : RustAlloc} {img : Obj.Image}
    (g : RunCall) (resStack : Nat) (s0 : State) :
    ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).onOom g s0 =
      runOom s0 := rfl

/-! ## 7. Pure Side-Condition & Semantics Extraction Lemmas -/

/-- Monotonicity of `allocFailedIn` along a trace prefix (`s0.trace <+: s1.trace`). -/
theorem allocFailedIn_of_prefix {s0 s1 sf : State}
    (hpre : s0.trace <+: s1.trace) (hf : allocFailedIn s1 sf) : allocFailedIn s0 sf := by
  rcases hpre with ⟨mid, hmid⟩
  unfold allocFailedIn at hf ⊢
  rw [← hmid, List.length_append, ← List.drop_drop] at hf
  exact List.mem_of_mem_drop hf

/-- Every `readBundleV F dir dev = some b` satisfies `cliBundleAt`'s three exact slice-length
obligations (`64`, `64`, `1568`). -/
theorem splitSigned_sig_length {bs : Bytes} {id : BitVec 32} {key sig : Bytes}
    (h : splitSigned bs = some (id, key, sig)) : sig.length = 64 := by
  unfold splitSigned at h
  rcases hsid : splitId bs with _ | ⟨pid, prest⟩
  · simp [hsid] at h
  rw [hsid] at h; dsimp only at h
  by_cases hge : 64 ≤ prest.length
  · simp [hge] at h
    rcases h with ⟨_, _, rfl⟩
    rw [List.length_drop]; omega
  · simp [hge] at h

theorem kemPkDeserialize_length {bs kpk : Bytes}
    (h : (match RunProofs.kemPkDeserialize bs with
          | .ok key => some key
          | _ => none) = some kpk) : kpk.length = 1568 := by
  unfold RunProofs.kemPkDeserialize at h
  cases bs with
  | nil => simp at h
  | cons t rest =>
    dsimp only at h
    by_cases ht : t ≠ 8#8
    · simp [ht] at h
    · by_cases hlen : rest.length ≠ RunProofs.kemPkLen
      · simp [ht, hlen] at h
      · simp [ht, hlen] at h; subst h; exact Decidable.of_not_not hlen

theorem readBundleV_slice_lengths {F : FsFiles} {dir : Bytes} {dev : BitVec 8} {b : BundleV}
    (hb : readBundleV F dir dev = some b) :
    b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 := by
  simp only [readBundleV, bind, Option.bind_eq_some_iff, Option.some.injEq] at hb
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, _, _⟩, hspk, _, _, ⟨_, _, _⟩, hkpk,
    _, _, _, _, _, _, kpk, hk, rfl⟩
  dsimp only at hk
  exact ⟨splitSigned_sig_length hspk, splitSigned_sig_length hkpk, kemPkDeserialize_length hk⟩

/-- `DomainArgv` rules out `CallV.keygen` on every `runRel` input (`g.c.tag ≠ 0`). -/
theorem runRel_not_keygen {S : RunSem} {g : RunCall}
    (hrel : runRel S g.i g.a)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    g.c.tag ≠ 0 := by
  rcases parseArgs_domain hrel.1 with ⟨c', hc', htag⟩
  rw [hparse] at hc'
  exact Option.some.inj hc' ▸ htag

/-- Coins length `< 2 ^ 63` (`slotFrame`'s pure bound) and ASCII own-address bytes (`from_utf8`'s
precondition) from `AtRunEntry`. -/
theorem AtRunEntry.bounds_pre {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {s0 : State}
    (he : AtRunEntry S img ext g s0) :
    (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      (∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok bs →
        ∀ b ∈ bs, b.toNat < 128) :=
  ⟨he.rel.2.1.1, he.rel.2.1.2.2.2.1⟩

/-- If `Dir::get("address")` returns `Err`, `g.a = some none` (reject). -/
theorem AtRunEntry.reject_of_own_err {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {s0 : State}
    (he : AtRunEntry S img ext g s0)
    (herr : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .error ()) :
    g.a = some none := by
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [he.parse, herr]

/-- If `me = .none` at `AtDispatch` (`address` returned `None`), `g.a = some none` (reject). -/
theorem AtDispatch.reject_of_me_none {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g .none s0 s) :
    g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hnone⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [he.parse, hget, hnone]

/-- Call-site side conditions for `run_hop_send` (`encSlotSpec` precondition and answer link). -/
theorem AtDispatch.send_facts {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV}
    {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g (.some meV meG) s0 s)
    (hc : g.c = .send peerV) :
    g.i.stdin.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      S.encOk (runFiles g.i) (addrValOf peerV) (MainHops.coinsOf g.i) ∧
      g.a = finish (S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (MainHops.coinsOf g.i)) ctWire := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
    hc ▸ he.parse
  refine ⟨he.rel.2.1.2.1 peerV hparse, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.send peerV) peerV ownB meV hparse rfl hget hme,
    he.rel.2.2.2.1 peerV ownB meV hparse hget hme, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme]

/-- Bundle-file path well-formedness (`cliWrOk`) for `run_hop_init1` and `run_hop_init2`. -/
theorem AtRunEntry.init_bundlePaths_ok {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {s0 : State}
    (he : AtRunEntry S img ext g s0) (hc : g.c = .init peerV dir) :
    ∀ name ∈ bundleNames, cliWrOk (bundlePath dir name) :=
  he.rel.2.1.2.2.2.2 peerV dir (hc ▸ he.parse)

/-- Call-site side conditions for `run_hop_init3` (`initSlotSpec` precondition, slice lengths, and
`runAns` answer link) from `AtRunEntry` and `AtInit2`. -/
theorem AtInit2.init_facts {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {d : Init2Data} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hi : AtInit2 img ext g d s0 s) :
    (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      d.bundle.spkSig.length = 64 ∧
      d.bundle.kpkSig.length = 64 ∧
      d.bundle.kpk.length = 1568 ∧
      S.filesOk (runFiles g.i) d.peerG.val d.meG.val ∧
      S.initOk (runFiles g.i) d.peerG.val d.meG.val ∧
      g.a = finish (S.initiate (runFiles g.i) d.peerG.val d.meG.val
        d.bundle (MainHops.coinsOf g.i)) (fun _ => []) := by
  rcases hi.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init d.peerV d.dir) :=
    hi.callEq ▸ he.parse
  have hlen := readBundleV_slice_lengths hi.bundleSem
  refine ⟨he.rel.2.1.1, hi.fs, hlen.1, hlen.2.1, hlen.2.2, ?_, ?_, ?_⟩
  · rw [hi.peerVal, hi.meVal]
    exact he.rel.2.2.1 (.init d.peerV d.dir) d.peerV ownB d.meV hparse rfl hget hme
  · rw [hi.peerVal, hi.meVal]
    exact he.rel.2.2.2.2.1.1 d.peerV d.dir ownB d.meV hparse hget hme
  · rw [he.rel.2.2.2.2.2, hi.peerVal, hi.meVal]
    unfold runAns
    simp [hparse, hget, hme, hi.bundleSem]

/-- Call-site side conditions for `run_hop_recvW` (wire byte `2`, `SignalMessage`). -/
theorem AtDispatch.recvW_facts {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV}
    {meV : AddrV} {meG : AddrGhost} {rest : Bytes} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g (.some meV meG) s0 s)
    (hc : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest) :
    rest.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      g.a = (match SignalMessage.tryFrom protoSignalCodec rest with
        | .ok m => finish (S.decryptSignal (runFiles g.i) (addrValOf peerV) (addrValOf meV)
            m (MainHops.coinsOf g.i)) id
        | .error _ => some none) := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ he.parse
  have htail : g.i.stdin.tail.length < 2 ^ 32 := he.rel.2.1.2.2.1 peerV hparse
  rw [hstdin] at htail
  refine ⟨htail, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.recv peerV) peerV ownB meV hparse rfl hget hme, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme, hstdin]; rfl

/-- Call-site side conditions for `run_hop_recvP` (wire byte `3`, `PreKeySignalMessage`). -/
theorem AtDispatch.recvP_facts {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV}
    {meV : AddrV} {meG : AddrGhost} {rest : Bytes} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g (.some meV meG) s0 s)
    (hc : g.c = .recv peerV)
    (hstdin : g.i.stdin = 3#8 :: rest) :
    rest.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      (∀ pm, S.pksmParse rest = some pm →
        S.decPkOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) pm) ∧
      g.a = (match S.pksmParse rest with
        | some m => finish (S.decryptPrekey (runFiles g.i) (addrValOf peerV) (addrValOf meV)
            m (MainHops.coinsOf g.i)) id
        | none => some none) := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ he.parse
  have htail : g.i.stdin.tail.length < 2 ^ 32 := he.rel.2.1.2.2.1 peerV hparse
  rw [hstdin] at htail
  refine ⟨htail, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.recv peerV) peerV ownB meV hparse rfl hget hme,
    fun pm hpm => he.rel.2.2.2.2.1.2 peerV ownB meV rest pm hparse hget hme hstdin hpm, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme, hstdin]; rfl

/-- Reject answer `g.a = some none` for `run_hop_recvBad` (empty `stdin` or leading byte
`∉ {2#8, 3#8}`). -/
theorem AtDispatch.recvBad_reject {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State}
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hc : g.c = .recv peerV)
    (hbad : g.i.stdin = [] ∨ ∃ t rest, g.i.stdin = t :: rest ∧ t ≠ 2#8 ∧ t ≠ 3#8) :
    g.a = some none := by
  cases me with
  | none => exact hd.reject_of_me_none he
  | some meV meG =>
    rcases hd.ownSem with ⟨ownB, hget, hme⟩
    have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
      hc ▸ he.parse
    rw [he.rel.2.2.2.2.2]
    unfold runAns
    rcases hbad with hnil | ⟨t, rest, hcons, ht2, ht3⟩
    · simp [hparse, hget, hme, hnil]
    · simp [hparse, hget, hme, hcons, ht2, ht3]

end CryptoVerification.SignalSession.Cli.RunCompose
