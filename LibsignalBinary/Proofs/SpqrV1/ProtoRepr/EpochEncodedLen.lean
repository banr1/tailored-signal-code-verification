/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import ProofLib.GenPlacedFetches
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Fetch
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Verification of `Epoch::encoded_len` (`0x38abc`, `0x664fc`)

Parameterized symbolic execution of `send` and `recv` (`Option<EpochDirection>`) field encoding
lengths and `subroutine_ok` proofs for both copies of
`<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len` (`[local#1]` at
`0x38abc` / Block `171`, `[local#2]` at `0x664fc` / Block `399`).
-/

@[expose] public section


namespace CryptoVerification
set_option maxRecDepth 2000000
gen_ls_blk 171
gen_ls_blk 399
end CryptoVerification

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem zeroExtend64_beq_zero32 (x : BitVec 32) : (BitVec.zeroExtend 64 x == 0#64) = (x == 0#32) := by bv_bits
@[local simp, local arm64_norm]
theorem ofNat_countLeadingZeros_64 (x : BitVec 64) : BitVec.ofNat 64 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 63
@[local simp, local arm64_norm]
theorem ofNat_countLeadingZeros_32 (x : BitVec 32) : BitVec.ofNat 32 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 31
@[local simp, local arm64_norm]
theorem truncate32_ofNat64 (n : Nat) : BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp

@[local simp, local arm64_norm]
theorem hwVarintLen_eq_ofNat_varintLen_norm (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (varintLen v) :=
  hwVarintLen_eq_ofNat_varintLen v

@[local simp, local arm64_norm]
theorem hwVarintLen_bvShift_eq_ofNat_varintLen_norm (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (varintLen v) :=
  hwVarintLen_bvShift_eq_ofNat_varintLen v

/-- The contract program rebased at address `b` with hooks `Rust.withPanics ext`. -/
noncomputable abbrev tripleRatchetProgAtExt (b : BitVec 64)
    (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

def EpochEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal1Name) (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal1Name) (epochEncodedLenSpec A)
def EpochEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr epochEncodedLenLocal1Name) (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr epochEncodedLenLocal1Name) (epochEncodedLenSpec A)

def EpochEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal2Name) (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal2Name) (epochEncodedLenSpec A)
def EpochEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr epochEncodedLenLocal2Name) (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr epochEncodedLenLocal2Name) (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics ext)) (blkPl_171).base (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics ext)) (blkPl_171).base (epochEncodedLenSpec A)
def EpochEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_171).base (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_171).rebase (blkPl_171).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_171).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics ext)) (blkPl_399).base (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics ext)) (blkPl_399).base (epochEncodedLenSpec A)
def EpochEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_399).base (epochEncodedLenPinnedSpec A)
def EpochEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_399).rebase (blkPl_399).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_399).base (epochEncodedLenSpec A)

/-- Entry address predicate for `[local#1]` (`0x38abc` / block `171`) or `[local#2]` (`0x664fc` / block `399`). -/
def IsEpochEncLenEntry (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr epochEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr epochEncodedLenLocal2Name = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@blkPC_171).rebase (@blkPl_171 inst).base H ∧ entry = (@blkPl_171 inst).base) ∨
    (prog = (@blkPC_399).rebase (@blkPl_399 inst).base H ∧ entry = (@blkPl_399 inst).base))

theorem epochEncLen_fetch_entry {prog : Program} {entry : BitVec 64}
    (hfn : IsEpochEncLenEntry prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr epochEncodedLenLocal1Name) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr epochEncodedLenLocal2Name) = some ins)
    (h3 : ∀ [LibsignalPlacement] H,
      ((blkPC_171).rebase (blkPl_171).base H).fetch ((blkPl_171).base + 0#64) = some ins)
    (h4 : ∀ [LibsignalPlacement] H,
      ((blkPC_399).rebase (blkPl_399).base H).fetch ((blkPl_399).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · simpa using @h3 inst H
  · simpa using @h4 inst H

theorem epochEncLen_fetch_add {prog : Program} {entry : BitVec 64}
    (hfn : IsEpochEncLenEntry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr epochEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr epochEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ [LibsignalPlacement] H,
      ((blkPC_171).rebase (blkPl_171).base H).fetch ((blkPl_171).base + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ [LibsignalPlacement] H,
      ((blkPC_399).rebase (blkPl_399).base H).fetch ((blkPl_399).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact @h3 inst H
  · exact @h4 inst H

open Lean Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` (byte offsets from function entry `entry`) when
    `hfn : IsEpochEncLenEntry prog entry`. -/
elab "epoch_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let off1 := 0x38ba0
  let off2 := 0x61104
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x38ba0
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x61104
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str
      s!"spqrEpochEncLenBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str
      s!"spqrEpochEncLenBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let blk1 := mkIdent (Name.mkSimple s!"blkPC_171_rebase_fetch_0x{hexK}")
    let blk2 := mkIdent (Name.mkSimple s!"blkPC_399_rebase_fetch_0x{hexK}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := epochEncLen_fetch_entry $hfn
          (fun b H => $fetchEntry (b := b) (H := H) $fnOff1 (by decide) $dec1)
          (fun b H => $fetchEntry (b := b) (H := H) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $blk1 _ H)
          (fun [LibsignalPlacement] H => $blk2 _ H)))
    else
      evalTactic (← `(tactic|
        have := epochEncLen_fetch_add $hfn (k := $kq)
          (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $fnOff1 (by decide) $dec1)
          (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $blk1 _ H)
          (fun [LibsignalPlacement] H => $blk2 _ H)))

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "epochEncLen_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    arm64_norm, *]
  done))

/-! ## Field layout decomposition for `chainEpochPBPinnedAt` -/

/-- The heap buffer of a `Vec<u8>` detached from its 24-byte `vecHeader`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

/-- First 64-bit word of `optEpochDirectionPBPinnedAt`: `noneCap` when `none`, `g.next.cap` when `some`. -/
def optEpochDirCap (g : EpochDirectionPBGhost) : Option EpochDirectionPB → BitVec 64
  | none => noneCap
  | some _ => g.next.cap

/-- Remaining 48 bytes + heap buffers of `optEpochDirectionPBPinnedAt`. -/
def optEpochDirPayload (A : RustAlloc) (g : EpochDirectionPBGhost) (p : BitVec 64) :
    Option EpochDirectionPB → SepProp
  | none => memRegion (p + 8#64) 48
  | some d =>
    ((p + 8#64) ↦₆₄ g.next.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      vecU8Buf A g.next.cap g.next.ptr d.next ∗
      ((p + 24#64) ↦₆₄ g.prev.cap) ∗ ((p + 32#64) ↦₆₄ g.prev.ptr) ∗
      ((p + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
      vecU8Buf A g.prev.cap g.prev.ptr d.prev ∗
      ((p + 48#64) ↦₃₂ d.ctr) ∗
      memRegion (p + 52#64) 4

theorem optEpochDirectionPBPinnedAt_eq (A : RustAlloc) (g : EpochDirectionPBGhost) (p : BitVec 64)
    (opt : Option EpochDirectionPB) :
    optEpochDirectionPBPinnedAt A g p opt =
      (p ↦₆₄ optEpochDirCap g opt) ∗ optEpochDirPayload A g p opt := by
  cases opt with
  | none => rfl
  | some d =>
    simp only [optEpochDirectionPBPinnedAt, epochDirectionPBPinnedAt, optEpochDirCap,
      optEpochDirPayload, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc, arm64_norm]

def epochUnpacked (A : RustAlloc) (g : ChainEpochPBGhost) (a : BitVec 64)
    (ep : ChainEpochPB) : SepProp :=
  (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
    ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗ optEpochDirPayload A g.recv (a + 56#64) ep.recv

theorem chainEpochPBPinnedAt_eq_unpacked (A : RustAlloc) (g : ChainEpochPBGhost) (a : BitVec 64)
    (ep : ChainEpochPB) :
    chainEpochPBPinnedAt A g a ep = epochUnpacked A g a ep := by
  unfold chainEpochPBPinnedAt epochUnpacked
  rw [optEpochDirectionPBPinnedAt_eq A g.send a, optEpochDirectionPBPinnedAt_eq A g.recv (a + 56#64)]
  ac_rfl

theorem vecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  omega

theorem cap_add_one_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  simp [bne, cap_add_one_beq_zero_false h]

theorem ofNat_length_beq_zero_of_lt {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length == 0#64) = bs.isEmpty ∧
      (BitVec.ofNat 64 bs.length != 0#64) = !bs.isEmpty := by
  cases bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b rest =>
    simp only [List.isEmpty_cons, Bool.not_false]
    have hne : BitVec.ofNat 64 (b :: rest).length ≠ 0#64 := by
      intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h1
      rw [Nat.mod_eq_of_lt hlt] at h1
      simp only [List.length_cons] at h1
      omega
    exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Bounds extracted from `optEpochDirPayload` in memory. -/
def OptEpochDirBounds (g : EpochDirectionPBGhost) (opt : Option EpochDirectionPB) : Prop :=
  (optEpochDirCap g opt + 1#64 == 0#64) = !opt.isSome ∧
  (optEpochDirCap g opt + 1#64 != 0#64) = opt.isSome ∧
  ∀ d, opt = some d →
    d.next.length < 2 ^ 63 ∧
    d.prev.length < 2 ^ 63 ∧
    (BitVec.ofNat 64 d.next.length == 0#64) = d.next.isEmpty ∧
    (BitVec.ofNat 64 d.next.length != 0#64) = !d.next.isEmpty ∧
    (BitVec.ofNat 64 d.prev.length == 0#64) = d.prev.isEmpty ∧
    (BitVec.ofNat 64 d.prev.length != 0#64) = !d.prev.isEmpty

theorem optEpochDirPayload_bounds {A : RustAlloc} {g : EpochDirectionPBGhost} {p : BitVec 64}
    {opt : Option EpochDirectionPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEpochDirPayload A g p opt ∗ R) :
    OptEpochDirBounds g opt := by
  cases opt with
  | none =>
    simp only [OptEpochDirBounds, optEpochDirCap]
    refine ⟨by decide, by decide, ?_⟩
    intro _ h; cases h
  | some d =>
    simp only [optEpochDirPayload] at hm
    have hnext_m : m ⊨ vecU8Buf A g.next.cap g.next.ptr d.next ∗
        (((p + 8#64) ↦₆₄ g.next.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
         ((p + 24#64) ↦₆₄ g.prev.cap) ∗ ((p + 32#64) ↦₆₄ g.prev.ptr) ∗
         ((p + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
         vecU8Buf A g.prev.cap g.prev.ptr d.prev ∗
         ((p + 48#64) ↦₃₂ d.ctr) ∗ memRegion (p + 52#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have hprev_m : m ⊨ vecU8Buf A g.prev.cap g.prev.ptr d.prev ∗
        (((p + 8#64) ↦₆₄ g.next.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
         vecU8Buf A g.next.cap g.next.ptr d.next ∗
         ((p + 24#64) ↦₆₄ g.prev.cap) ∗ ((p + 32#64) ↦₆₄ g.prev.ptr) ∗
         ((p + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
         ((p + 48#64) ↦₃₂ d.ctr) ∗ memRegion (p + 52#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨hn_le, hn_cap⟩ := vecU8Buf_bounds hnext_m
    have ⟨hp_le, hp_cap⟩ := vecU8Buf_bounds hprev_m
    have hn_lt : d.next.length < 2 ^ 63 := Nat.lt_of_le_of_lt hn_le hn_cap
    have hp_lt : d.prev.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
    have hn_z := ofNat_length_beq_zero_of_lt (by omega : d.next.length < 2 ^ 64)
    have hp_z := ofNat_length_beq_zero_of_lt (by omega : d.prev.length < 2 ^ 64)
    refine ⟨cap_add_one_beq_zero_false hn_cap, cap_add_one_bne_zero_true hn_cap, ?_⟩
    intro d' hd'
    cases hd'
    exact ⟨hn_lt, hp_lt, hn_z.1, hn_z.2, hp_z.1, hp_z.2⟩

theorem epochUnpacked_bounds {A : RustAlloc} {g : ChainEpochPBGhost} {a : BitVec 64}
    {ep : ChainEpochPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ epochUnpacked A g a ep ∗ R) :
    OptEpochDirBounds g.send ep.send ∧ OptEpochDirBounds g.recv ep.recv := by
  unfold epochUnpacked at hm
  have hs : m ⊨ optEpochDirPayload A g.send a ep.send ∗
      ((a ↦₆₄ optEpochDirCap g.send ep.send) ∗
       ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
       optEpochDirPayload A g.recv (a + 56#64) ep.recv ∗ R) := by
    convert hm using 1; ac_rfl
  have hr : m ⊨ optEpochDirPayload A g.recv (a + 56#64) ep.recv ∗
      ((a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
       ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗ R) := by
    convert hm using 1; ac_rfl
  exact ⟨optEpochDirPayload_bounds hs, optEpochDirPayload_bounds hr⟩

@[local simp, local arm64_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl

@[local simp, local arm64_norm]
theorem noneCap_add_one_bne_zero : (noneCap + 1#64 != 0#64) = false := rfl

@[local simp, local arm64_norm]
theorem zext64_truncate32 (v : BitVec 32) : (BitVec.zeroExtend 64 v).truncate 32 = v := by
  bv_bits

/-! ## Arithmetic & Flag Lemmas for `Epoch::encoded_len` -/

theorem bv_u32VarintField_nonzero {v : BitVec 32} (hv : v ≠ 0#32) :
    BitVec.ofNat 64 (varintLen (v.zeroExtend 64)) + 1#64 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen v) := by
  unfold u32VarintFieldEncodedLen
  simp only [hv, ↓reduceIte, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_bytesField_nonempty {bs : List (BitVec 8)} (hbs : bs.isEmpty = false) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 bs.length)) + 1#64 =
      BitVec.ofNat 64 (bytesFieldEncodedLen bs) := by
  unfold bytesFieldEncodedLen
  simp only [hbs, Bool.false_eq_true, ↓reduceIte, ← BitVec.ofNat_add]
  congr 1
  omega

theorem bv_optEpochDirField_some (d : EpochDirectionPB) :
    BitVec.ofNat 64 (epochDirectionPBEncodedLen d) +
      BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))) + 1#64 =
      BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen (some d)) := by
  unfold optEpochDirectionPBFieldEncodedLen
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

theorem bv_add_ofNat_comm (a b : Nat) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_eq (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

@[local simp, local arm64_norm]
theorem ule_zero_64 (x : BitVec 64) : BitVec.ule 0#64 x = true := by
  bv_bits

@[local simp, local arm64_norm]
theorem ult_zero_64 (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  bv_bits

theorem ule_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 (a + b)) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ult_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem adds_no_overflow_of_eq {a b c : Nat} (heq : b + a = c) (hlt : c < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 c ∧
      (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 a) = false ∧
      (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 c) = true ∧
      (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 b) = false ∧
      (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 c) = true := by
  subst heq
  exact ⟨bv_add_ofNat_comm b a, ult_ofNat_add_of_lt hlt, ule_ofNat_add_of_lt hlt,
    by rw [Nat.add_comm] at hlt ⊢; exact ult_ofNat_add_of_lt hlt,
    by rw [Nat.add_comm] at hlt ⊢; exact ule_ofNat_add_of_lt hlt⟩

theorem cmp_ls_false_of_lt {vlen tot : Nat} (hlt : vlen < tot) (htot : tot < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true ∧
    BitVec.ule (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false ∧
    BitVec.ult (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false ∧
    (BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen == 0#64) = false ∧
    (BitVec.ofNat 64 tot == BitVec.ofNat 64 vlen) = false := by
  have h1 : BitVec.ule (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true := by
    rw [BitVec.ule_eq_decide, decide_eq_true_eq]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
      Nat.mod_eq_of_lt htot]
    omega
  have h2 : BitVec.ule (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false := by
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
      Nat.mod_eq_of_lt htot]
    omega
  have h3 : BitVec.ult (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false := by
    rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
      Nat.mod_eq_of_lt htot]
    omega
  have hne : BitVec.ofNat 64 tot ≠ BitVec.ofNat 64 vlen := by
    intro heq
    have h := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
      Nat.mod_eq_of_lt htot] at h
    omega
  have hsub : BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen ≠ 0#64 := by
    intro heq
    apply hne
    have : BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen + BitVec.ofNat 64 vlen =
        0#64 + BitVec.ofNat 64 vlen := congrArg (· + BitVec.ofNat 64 vlen) heq
    simpa [BitVec.sub_add_cancel] using this
  exact ⟨h1, h2, h3, beq_eq_false_iff_ne.mpr hsub, beq_eq_false_iff_ne.mpr hne⟩

/-! ## Callee-Saved Preservation Helper -/

def EpochEncLenCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧ s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EpochEncLenCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EpochEncLenCalleeSaved s0 s1) (h2 : EpochEncLenCalleeSaved s1 s2) :
    EpochEncLenCalleeSaved s0 s2 := by
  reg_chain

/-! ## Step Lemmas for `send` (`a + 0x00`) -/

/-- `ep.send = none`: from `entry` (`+0x000`) via `+0x170..+0x17c` to
    `if ep.recv.isSome then entry + 192#64 else entry + 384#64`. -/
theorem step_epoch_send_none (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB)
    (hsend : ep.send = none)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 0 20
  epoch_fetches_range hfn 368 384
  have hrecv_beq := hrecv_b.1
  have hrecv_bne := hrecv_b.2.1
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ noneCap) ∗ optEpochDirPayload A g.send a none ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap]
  rw [hP1]
  apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
  wp_steps
  apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
  rw [← hP1]
  exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all [optEpochDirectionPBFieldEncodedLen])
    (by simp_all [EpochEncLenCalleeSaved])

/-- `ep.send = some ds`, part A (`+0x000..+0x03c` and `+0x194..+0x19c`):
    Prologue + test `send.cap` + `ds.ctr` (`+0x30`) + load `ds.next.len` (`+0x10`). -/
theorem step_epoch_send_some_a (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB)
    (hsend : ep.send = some ds)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ds.next.isEmpty then entry + 416#64 else entry + 64#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen ds.ctr) →
      sm.readReg64 .x9 = BitVec.ofNat 64 ds.next.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 0 64
  epoch_fetches_range hfn 404 416
  have hcap_beq : (g.send.next.cap + 1#64 == 0#64) = false := by
    have h := hsend_b.1
    rwa [hsend, Option.isSome_some, Bool.not_true, optEpochDirCap] at h
  obtain ⟨_, _, hnext_beq, hnext_bne, _, _⟩ := hsend_b.2.2 ds hsend
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ g.send.next.cap) ∗ ((a + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ds.next.length) ∗
      vecU8Buf A g.send.next.cap g.send.next.ptr ds.next ∗
      ((a + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ds.prev.length) ∗
      vecU8Buf A g.send.prev.cap g.send.prev.ptr ds.prev ∗
      ((a + 48#64) ↦₃₂ ds.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap, optEpochDirPayload, sepConj_assoc]
  rw [hP1]
  by_cases hctr : ds.ctr = 0#32
  · apply SepWPp.of_sepWP (mid := if ds.next.isEmpty then entry + 416#64 else entry + 64#64)
    wp_steps
    apply SepWP.done (by cases ds.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
      (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  · have hctr_beq : (ds.ctr == 0#32) = false := beq_eq_false_iff_ne.mpr hctr
    have henc := bv_u32VarintField_nonzero hctr
    apply SepWPp.of_sepWP (mid := if ds.next.isEmpty then entry + 416#64 else entry + 64#64)
    wp_steps
    apply SepWP.done (by cases ds.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `ep.send = some ds`, part B (`+0x040..+0x064` and `+0x1a0..+0x1ac`):
    `ds.next` field length + load `ds.prev.len` (`+0x28`). -/
theorem step_epoch_send_some_b (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB) (s1 : Nat)
    (hsend : ep.send = some ds)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if ds.next.isEmpty then entry + 416#64 else entry + 64#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ds.next.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ds.prev.isEmpty then entry + 132#64 else entry + 104#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + bytesFieldEncodedLen ds.next) →
      sm.readReg64 .x9 = BitVec.ofNat 64 ds.prev.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 64 104
  epoch_fetches_range hfn 416 432
  obtain ⟨_, _, _, _, hprev_beq, hprev_bne⟩ := hsend_b.2.2 ds hsend
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ g.send.next.cap) ∗ ((a + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ds.next.length) ∗
      vecU8Buf A g.send.next.cap g.send.next.ptr ds.next ∗
      ((a + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ds.prev.length) ∗
      vecU8Buf A g.send.prev.cap g.send.prev.ptr ds.prev ∗
      ((a + 48#64) ↦₃₂ ds.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap, optEpochDirPayload, sepConj_assoc]
  rw [hP1]
  cases hne : ds.next.isEmpty with
  | true =>
    simp only [hne, ↓reduceIte] at hpc
    cases hpe : ds.prev.isEmpty with
    | true =>
      apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesFieldEncodedLen])
        (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesFieldEncodedLen])
        (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hne
    have hadd := bv_add_ofNat_comm s1 (bytesFieldEncodedLen ds.next)
    apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
    wp_steps
    apply SepWP.done (by cases ds.prev.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.prev.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `ep.send = some ds`, part C (`+0x068..+0x0bc`):
    `ds.prev` field length + `send` total length (`optEpochDirectionPBFieldEncodedLen ep.send`)
    + test `ep.recv` (`+0x38`). -/
theorem step_epoch_send_some_c (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB)
    (hsend : ep.send = some ds)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    (hfit : optEpochDirectionPBFieldEncodedLen (some ds) < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if ds.prev.isEmpty then entry + 132#64 else entry + 104#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ds.prev.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 104 192
  have hrecv_beq := hrecv_b.1
  have hbody_lt : epochDirectionPBEncodedLen ds < 2 ^ 64 := by
    dsimp [optEpochDirectionPBFieldEncodedLen] at hfit
    omega
  have htot := bv_optEpochDirField_some ds
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (epochDirectionPBEncodedLen ds)))
    (tot := optEpochDirectionPBFieldEncodedLen (some ds))
    (by dsimp [optEpochDirectionPBFieldEncodedLen]; omega) hfit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := rfl
  rw [hP1]
  cases hpe : ds.prev.isEmpty with
  | true =>
    simp only [hpe, ↓reduceIte] at hpc
    have hprev_len : ds.prev.length = 0 := List.isEmpty_iff.mp hpe |> congrArg List.length
    have hbody_true : u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next =
        epochDirectionPBEncodedLen ds := by
      dsimp [epochDirectionPBEncodedLen, bytesFieldEncodedLen]
      simp [hpe]
    rw [hprev_len] at hx9
    rw [hbody_true] at hx8
    apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
    wp_steps
    apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hpe
    obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen ds.prev)
        (b := u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next)
        (c := epochDirectionPBEncodedLen ds) rfl hbody_lt
    apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
    wp_steps
    apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-! ## Step Lemmas for `recv` (`a + 0x38`) -/

/-- `ep.recv = none`: from `entry + 384#64` (`+0x180`) via `+0x168..+0x16c` to `s0.readReg64 .lr`. -/
theorem step_epoch_recv_none (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a sp : BitVec 64) (ep : ChainEpochPB)
    (hrecv : ep.recv = none)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (epochUnpacked A g a ep ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  epoch_fetches_range hfn 360 368
  epoch_fetches_range hfn 384 392
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all [chainEpochPBEncodedLen, optEpochDirectionPBFieldEncodedLen])
    (by epochEncLen_cc_close)

/-- `ep.recv = some dr`, part A (`+0x0c0..+0x0e8` and `+0x1b0..+0x1b8`):
    `dr.ctr` (`+0x68`) + load `dr.next.len` (`+0x48`). -/
theorem step_epoch_recv_some_a (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB)
    (hrecv : ep.recv = some dr)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if dr.next.isEmpty then entry + 444#64 else entry + 236#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen dr.ctr) →
      sm.readReg64 .x10 = BitVec.ofNat 64 dr.next.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 192 236
  epoch_fetches_range hfn 432 444
  obtain ⟨_, _, hnext_beq, hnext_bne, _, _⟩ := hrecv_b.2.2 dr hrecv
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ g.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 dr.next.length) ∗
      vecU8Buf A g.recv.next.cap g.recv.next.ptr dr.next ∗
      ((a + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 dr.prev.length) ∗
      vecU8Buf A g.recv.prev.cap g.recv.prev.ptr dr.prev ∗
      ((a + 104#64) ↦₃₂ dr.ctr) ∗ memRegion (a + 108#64) 4 := by
    simp only [epochUnpacked, hrecv, optEpochDirCap, optEpochDirPayload, arm64_norm]
  rw [hP1]
  by_cases hctr : dr.ctr = 0#32
  · apply SepWPp.of_sepWP (mid := if dr.next.isEmpty then entry + 444#64 else entry + 236#64)
    wp_steps
    apply SepWP.done (by cases dr.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [u32VarintFieldEncodedLen]) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])
  · have hctr_beq : (dr.ctr == 0#32) = false := beq_eq_false_iff_ne.mpr hctr
    have henc := bv_u32VarintField_nonzero hctr
    apply SepWPp.of_sepWP (mid := if dr.next.isEmpty then entry + 444#64 else entry + 236#64)
    wp_steps
    apply SepWP.done (by cases dr.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `ep.recv = some dr`, part B (`+0x0ec..+0x110` and `+0x1bc..+0x1c8`):
    `dr.next` field length + load `dr.prev.len` (`+0x60`). -/
theorem step_epoch_recv_some_b (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB) (r1 : Nat)
    (hrecv : ep.recv = some dr)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if dr.next.isEmpty then entry + 444#64 else entry + 236#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 r1)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 dr.next.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if dr.prev.isEmpty then entry + 304#64 else entry + 276#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (r1 + bytesFieldEncodedLen dr.next) →
      sm.readReg64 .x10 = BitVec.ofNat 64 dr.prev.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range hfn 236 276
  epoch_fetches_range hfn 444 460
  obtain ⟨_, _, _, _, hprev_beq, hprev_bne⟩ := hrecv_b.2.2 dr hrecv
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ g.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 dr.next.length) ∗
      vecU8Buf A g.recv.next.cap g.recv.next.ptr dr.next ∗
      ((a + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 dr.prev.length) ∗
      vecU8Buf A g.recv.prev.cap g.recv.prev.ptr dr.prev ∗
      ((a + 104#64) ↦₃₂ dr.ctr) ∗ memRegion (a + 108#64) 4 := by
    simp only [epochUnpacked, hrecv, optEpochDirCap, optEpochDirPayload, arm64_norm]
  rw [hP1]
  cases hne : dr.next.isEmpty with
  | true =>
    simp only [hne, ↓reduceIte] at hpc
    cases hpe : dr.prev.isEmpty with
    | true =>
      apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [bytesFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [bytesFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hne
    have hadd := bv_add_ofNat_comm r1 (bytesFieldEncodedLen dr.next)
    apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
    wp_steps
    apply SepWP.done (by cases dr.prev.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.prev.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `ep.recv = some dr`, part C (`+0x114..+0x16c`):
    `dr.prev` field length + `recv` total length + `send + recv` + epilogue (`ldp`, `ret`). -/
theorem step_epoch_recv_some_c (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a sp : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB)
    (hrecv : ep.recv = some dr)
    (hfit : chainEpochPBEncodedLen ep < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if dr.prev.isEmpty then entry + 304#64 else entry + 276#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hx9 : s.readReg64 .x9 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 dr.prev.length)
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (epochUnpacked A g a ep ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  epoch_fetches_range hfn 276 368
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hrecv_fit : optEpochDirectionPBFieldEncodedLen (some dr) < 2 ^ 64 := by
    unfold chainEpochPBEncodedLen at hfit
    rw [hrecv] at hfit
    omega
  have hbody_lt : epochDirectionPBEncodedLen dr < 2 ^ 64 := by
    dsimp [optEpochDirectionPBFieldEncodedLen] at hrecv_fit
    omega
  have htot := bv_optEpochDirField_some dr
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (epochDirectionPBEncodedLen dr)))
    (tot := optEpochDirectionPBFieldEncodedLen (some dr))
    (by dsimp [optEpochDirectionPBFieldEncodedLen]; omega) hrecv_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  have hfinal_eq :
      optEpochDirectionPBFieldEncodedLen ep.send +
        optEpochDirectionPBFieldEncodedLen (some dr) =
      chainEpochPBEncodedLen ep := by
    unfold chainEpochPBEncodedLen
    rw [hrecv]
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optEpochDirectionPBFieldEncodedLen (some dr))
      (b := optEpochDirectionPBFieldEncodedLen ep.send)
      (c := chainEpochPBEncodedLen ep) hfinal_eq hfit
  subst hP
  cases hpe : dr.prev.isEmpty with
  | true =>
    simp only [hpe, ↓reduceIte] at hpc
    have hprev_len : dr.prev.length = 0 := List.isEmpty_iff.mp hpe |> congrArg List.length
    have hbody_true : u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next =
        epochDirectionPBEncodedLen dr := by
      dsimp [epochDirectionPBEncodedLen, bytesFieldEncodedLen]
      simp [hpe]
    rw [hprev_len] at hx10
    rw [hbody_true] at hx9
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | false =>
    simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hpe
    obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen dr.prev)
        (b := u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next)
        (c := epochDirectionPBEncodedLen dr) rfl hbody_lt
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-! ## Combined `send` and `recv` Phases and Top-Level Theorems -/

theorem stackAt_epochEncodedLen_eq (sp : BitVec 64) :
    stackAt sp epochEncodedLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
  simp only [stackAt, epochEncodedLenStack]
  change memRegion (sp - 16#64) (8 * 2) = _
  rw [memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold

/-- Combined `send` phase: from `entry` (`+0x000`) to
    `if ep.recv.isSome then entry + 192#64 else entry + 384#64`. -/
theorem step_epoch_send (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    (hfit : chainEpochPBEncodedLen ep < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  cases hsend : ep.send with
  | none =>
    exact step_epoch_send_none prog A entry hfn g a sp v16 v8 ep hsend hrecv_b
      hpc hrun hsp halign hx0 hP hnext
  | some ds =>
    have hsend_fit : optEpochDirectionPBFieldEncodedLen (some ds) < 2 ^ 64 := by
      unfold chainEpochPBEncodedLen at hfit; rw [hsend] at hfit; omega
    refine step_epoch_send_some_a prog A entry hfn g a sp v16 v8 ep ds hsend hsend_b
      hpc hrun hsp halign hx0 hP ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
    let FSave : SepProp :=
      ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr) ∗ F
    have hP_save :
        (epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F =
        epochUnpacked A g a ep ∗ FSave := by
      dsimp [FSave]; ac_rfl
    refine step_epoch_send_some_b (F := FSave) prog A entry hfn g a ep ds
      (u32VarintFieldEncodedLen ds.ctr) hsend hsend_b
      hpc1 hrun1 hx0_1 hx8_1 hx9_1 hP_save ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hcs2
    refine step_epoch_send_some_c (F := FSave) prog A entry hfn g a ep ds
      hsend hrecv_b hsend_fit
      hpc2 hrun2 hx0_2 hx8_2 hx9_2 hP_save ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    exact hnext s3 hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) (by rw [htr3, htr2, htr1])
      hx0_3 hx8_3 (hcs1.trans (hcs2.trans hcs3))

/-- Shared `subroutine_ok` proof for any `(prog, entry)` satisfying `IsEpochEncLenEntry prog entry`. -/
theorem epochEncodedLen_entry_pinned_ok (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsEpochEncLenEntry prog entry) :
    subroutine_ok prog entry (epochEncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, ep⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
    stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  unfold EpochEncodedLenFits at hfit
  have hmem0 : s0.mem ⊨
      (epochUnpacked A g a ep ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  obtain ⟨hsend_b, hrecv_b⟩ := epochUnpacked_bounds hpre
  refine ⟨(epochUnpacked A g a ep ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_epoch_send (F := R) prog A entry hfn g a s0.sp v16 v8 ep
    hsend_b hrecv_b hfit hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  cases hrecv : ep.recv with
  | none =>
    simp only [hrecv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_epoch_recv_none (F := R) prog A entry hfn g a s0.sp ep hrecv
      hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
      stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  | some dr =>
    simp only [hrecv, Option.isSome_some, ↓reduceIte] at hpc1
    let FSave : SepProp :=
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
    have hP_save :
        (epochUnpacked A g a ep ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R =
        epochUnpacked A g a ep ∗ FSave := by
      dsimp [FSave]; ac_rfl
    refine step_epoch_recv_some_a (F := FSave) prog A entry hfn g a ep dr hrecv hrecv_b
      hpc1 hrun1 hx0_1 hx8_1 hP_save ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hx10_2 hcs2
    refine step_epoch_recv_some_b (F := FSave) prog A entry hfn g a ep dr
      (u32VarintFieldEncodedLen dr.ctr) hrecv hrecv_b
      hpc2 hrun2 hx0_2 hx8_2 hx9_2 hx10_2 hP_save ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hx9_3 hx10_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_epoch_recv_some_c (F := R) prog A entry hfn g a s0.sp ep dr
      hrecv hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hx9_3 hx10_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
      stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem epochEncodedLen_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr epochEncodedLenLocal2Name = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (epochEncodedLenPinnedSpec A) :=
  epochEncodedLen_entry_pinned_ok _ A entry (Or.inl ⟨b, ext, rfl, hfn⟩)

/-- Bridge from `epochEncodedLenPinnedSpec A` to unpinned `epochEncodedLenSpec A`. -/
theorem epochEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (epochEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (epochEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, ep⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [epochEncodedLenSpec, chainEpochPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, ep⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [epochEncodedLenSpec, chainEpochPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### `[local#1]` (`0x38abc` / Block `171`) and `[local#2]` (`0x664fc` / Block `399`) Corollaries -/

theorem epochEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PinnedOkExt b A ext :=
  epochEncodedLen_entry_pinned_ok_ext b A ext _ (Or.inl rfl)
theorem epochEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1OkExt b A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local1_pinned_ok_ext b A ext)
theorem epochEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal1PinnedOk b C A ctl abs :=
  epochEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem epochEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal1Ok b C A ctl abs :=
  epochEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PinnedOkExt b A ext :=
  epochEncodedLen_entry_pinned_ok_ext b A ext _ (Or.inr rfl)
theorem epochEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2OkExt b A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local2_pinned_ok_ext b A ext)
theorem epochEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal2PinnedOk b C A ctl abs :=
  epochEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem epochEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal2Ok b C A ctl abs :=
  epochEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkExt A ext :=
  epochEncodedLen_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)
theorem epochEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkExt A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local1_pinned_placed_ok_ext A ext)
theorem epochEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem epochEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOk C A ctl abs :=
  epochEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PinnedPlacedOkExt A ext :=
  epochEncodedLen_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr ⟨rfl, rfl⟩⟩)
theorem epochEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PlacedOkExt A ext :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local2_pinned_placed_ok_ext A ext)
theorem epochEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem epochEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : EpochEncodedLenLocal2PlacedOk C A ctl abs :=
  epochEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
