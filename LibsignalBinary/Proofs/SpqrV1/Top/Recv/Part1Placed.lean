/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp

/-!
# Relocatable Preamble & Common Epilogue for `spqr::recv`

Relocatable postconditions, shared epilogue (`+1040..+1072`), `Err(MsgDecode)` exit, and
preamble varint decoding (`+96..+312`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Postconditions and `SepWPpLS` Lifting Helpers -/

/-- Relocatable core postcondition of `spqr::recv` without the no-panic conjunct. -/
abbrev spqrRecvPlacedCorePost0 (A : RustAlloc) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
    spqrRecvRoPlacedAt ∗
    st.at A ∗
    msg.at A ∗
    recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
    A.pool ∗
    stackAt s0.sp spqrRecvStack

abbrev spqrRecvPlacedPost0 (A : RustAlloc) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spqrRecvPlacedCorePost0 A M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Relocatable core postcondition of `spqr::recv` with `¬ M.recvPanics st.bytes msg.bytes`. -/
abbrev spqrRecvPlacedCorePost (A : RustAlloc) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace ∧ ¬ M.recvPanics st.bytes msg.bytes⌝ ∗
    spqrRecvRoPlacedAt ∗
    st.at A ∗
    msg.at A ∗
    recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
    A.pool ∗
    stackAt s0.sp spqrRecvStack

abbrev spqrRecvPlacedPost (A : RustAlloc) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spqrRecvPlacedCorePost A M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem spqrRecvPlacedPost_of_post0 {A : RustAlloc} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp} {sf : State} {P_f : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : spqrRecvPlacedPost0 A M st msg ret s0 R sf P_f) :
    spqrRecvPlacedPost A M st msg ret s0 R sf P_f :=
  ⟨fun hm => satisfies_pure_and_of_pure (h.1 hm) hnp, h.2⟩

theorem sepWP_spqrRecvPlacedPost_of_post0 {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {A : RustAlloc} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : SepWP prog target_pc s P (spqrRecvPlacedPost0 A M st msg ret s0 R)) :
    SepWP prog target_pc s P (spqrRecvPlacedPost A M st msg ret s0 R) :=
  SepWP.mono h (fun _ _ _ _ hq => spqrRecvPlacedPost_of_post0 hnp hq)

/-! ## 2. Common Epilogue (`+1040 .. +1072`) and `Err(MsgDecode)` Exit (`+276 .. +288`) -/

/-- Relocatable shared epilogue (`+1040 .. +1072`, 9 instructions) for Block `329`
    (`spqr::recv`). -/
theorem step_epilogue_placed (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hpc : s.pc = spqrRecvPlacedEntry + 1040#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    sp_sub_96_aligned s0 hs0A
  subst hP hpost
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, spqrRecvPlacedPost0, spqrRecvPlacedCorePost0] at hpc ⊢
  generalize hsp0 : s0.sp = sp0 at hsp hsp96A ⊢
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0]
  unfold decodeStateSavedAt
  wp_steps 9
  have hrestore := stack_restore_spqrRecv sp0 s0
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0] at hrestore
  refine SepWP.fold hrestore (by
    unfold decodeStateSavedAt
    sep_focus) ?_
  wp_done

/-- Relocatable `Err(MsgDecode)` exit (`+276 .. +288 -> +1040 .. +1072`) for Block `329`
    (`spqr::recv`). -/
theorem step_err_msgDecode_placed (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
  rw [ret_48_split ret]
  wp_pull_exists
  rename_i r3 r2 r1 r0
  wp_steps 4
  have hfold := recv_err_msgDecode_foldX A ret r2 r3
  rw [← herr] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  exact step_epilogue_placed A M ext st msg ret s0 _ _ R post hpost
    (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Lift `step_err_msgDecode_placed` into `SepWPpLS`. -/
theorem step_err_msgDecode_wppLS (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = spqrRecvPlacedEntry + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost0 A M st msg ret s0 R)
      (spqrRecvPanicPost M st msg s0 R) :=
  SepWPpLS.of_sepWPp (SepWPp.of_sepWP_ret
    (step_err_msgDecode_placed A M ext st msg ret s0 s P R _ rfl herr hpc hrun hsp hs0A htr hx19 hP))

/-! ## 3. Preamble Varint Decoding (`+96 .. +276`, `+312`) -/

/-- Relocatable frame invariant throughout `+0 .. +312` (after the prologue). -/
abbrev spqrRecvPlacedPreambleFrame (A : RustAlloc) (st msg : VecArg)
    (ret : BitVec 64) (s0 : State) : SepProp :=
  spqrRecvRoPlacedAt ∗
  st.at A ∗
  msg.at A ∗
  memRegion ret 48 ∗
  A.pool ∗
  stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
  memRegion (s0.sp - 4992#64) 0x1320 ∗
  spqrRecvSavedRegs (s0.sp - 4992#64) s0

/-- Relocatable continuation hypothesis at `+276` (`Err(MsgDecode)`). -/
abbrev PreamblePlacedErrTail (A : RustAlloc) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .error .msgDecode →
    s1.pc = spqrRecvPlacedEntry + 276#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x19 = ret →
    P1 = spqrRecvPlacedPreambleFrame A st msg ret s0 →
    SepWP (spqrRecvPlacedProg ext) target_pc s1 P1 post

/-- Relocatable continuation hypothesis at `+312` (`Ok(pre)`). -/
abbrev PreamblePlacedOkTail (A : RustAlloc) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg msgPtr pre.remaining →
    s1.pc = spqrRecvPlacedEntry + 312#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x0 = st.v →
    s1.readReg64 .x19 = ret →
    s1.readReg64 .x21 = pre.index.zeroExtend 64 →
    s1.readReg64 .x22 = pre.epoch →
    s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s1.readReg64 .x24 = msgPtr →
    s1.readReg64 .x25 = pre.version.zeroExtend 64 →
    s1.readReg64 .x29 = s0.sp - 96#64 →
    P1 = spqrRecvPlacedPreambleFrame A st msg ret s0 →
    SepWP (spqrRecvPlacedProg ext) target_pc s1 P1 post

set_option maxHeartbeats 800000 in
/-- Relocatable steps from `+252` after decoding `(index, rest')`. -/
theorem step_after_index_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch index : BitVec 64)
    (pre₁ pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8) (j : Nat)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hsplit : msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest')
    (hpre2 : pre₂.length = j)
    (hpre : msgPreamble msg.bytes =
      if index.toNat < 2 ^ 32 then
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      else
        .error .msgDecode)
    (hpc : s.pc = spqrRecvPlacedEntry + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j + 1))
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = index)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A st msg ret s0) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hlen_eq : msg.bytes.length = 1 + pre₁.length + j + 1 + rest'.length := by
    rw [hsplit]; simp [hpre2]; omega
  have hrem := rem_len_add_not hlen_eq hlen_lt
  clear hlen_eq
  have hvalid : MsgRemValid msg
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1))) rest' := by
    right
    refine ⟨(version :: pre₁ ++ pre₂) ++ [byteJ], ?_, ?_⟩
    · rw [hsplit]; simp [List.append_assoc]
    · have hlen_p : ((version :: pre₁ ++ pre₂) ++ [byteJ]).length = 1 + (pre₁.length + j + 1) := by
        simp [List.length_cons, List.length_append, List.length_singleton, hpre2]; omega
      rw [hlen_p]
      simp only [BitVec.ofNat_add]
  clear hsplit
  dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail ⊢
  wp_steps
  wp_if hhi
  · have hnlt : ¬ index.toNat < 2 ^ 32 := by bv_omega
    have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp only [hpre, hnlt, ↓reduceIte]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hlt : index.toNat < 2 ^ 32 := by bv_omega
    have hok : msgPreamble msg.bytes =
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' } := by
      simp only [hpre, hlt, ↓reduceIte]
    wp_steps 4
    exact hok_tail
      { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1)))
      _ P hok hvalid
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx21, arm64_norm, zeroExtend_setWidth32_of_lt hlt])
      (by simp [hx22, arm64_norm])
      (by simp [hx9, hx10, hrem, arm64_norm])
      (by simp [hx8, hx10, arm64_norm]; bv_arith)
      (by simp [hx25, arm64_norm])
      (by simp [hx29, arm64_norm])
      hP

set_option maxHeartbeats 1600000 in
/-- Relocatable index varint loop (`+192 .. +248`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_index_loop_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch : BitVec 64)
    (pre₁ rest1 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest' →
      rest1 = pre₂ ++ byteJ :: rest' →
      pre₂.length = j →
      (msgPreamble msg.bytes =
        match LibsignalSpqrV1.decodeVarintLoop j out (byteJ :: rest') with
        | none => .error .msgDecode
        | some (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else
            .error .msgDecode) →
      s.pc = spqrRecvPlacedEntry + 192#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x22 = epoch →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j) →
      s.readReg64 .x11 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x12 = BitVec.ofNat 64 (pre₁.length - 1 + j) →
      s.readReg64 .x13 = BitVec.ofNat 64 (min rest1.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (msg.bytes.length - 2) →
      s.readReg64 .x15 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x21 = out →
      P = spqrRecvPlacedPreambleFrame A st msg ret s0 →
      SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₂ rest' byteJ s P hjk hj hsplit hrest1 hpre2 hpre
      hpc hrun hsp htr hx0 hx19 hx22 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx21 hP
    have hafter := step_after_index_placed A ext st msg ret target_pc version epoch
      (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
      pre₁ pre₂ rest' byteJ j s0
    have hmsg_ge : pre₁.length + j + 2 ≤ msg.bytes.length := by
      rw [hsplit]; simp [hpre2]
    have hne_bounds := index_bounds_ne hpre1 hmsg_ge hlen_lt
    have hoff : msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j)) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁ ++ pre₂).length := by
      simp only [List.length_cons, List.length_append, hpre2]; bv_omega
    have hexp := msg_expose_byte A msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest1_symm := hrest1.symm; clear hrest1
    subst hP
    dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry, spqrRecvPlacedPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    wp_steps
    wp_if hbounds
    · exact False.elim (hne_bounds hbounds)
    clear hbounds
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest1.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest1_symm.symm hpre2 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := rest' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by ac_rfl)
    · have hlt : j + 1 < min rest1.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest'', rfl⟩ := varint_cont_of_lt hrest1_symm.symm hpre2 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match LibsignalSpqrV1.decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest'') with
            | none => .error .msgDecode
            | some (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: pre₁ ++ (pre₂ ++ [byteJ])) ++ b' :: rest'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest1' : rest1 = (pre₂ ++ [byteJ]) ++ b' :: rest'' := by
          rw [← hrest1_symm]; simp [List.append_assoc]
        have hpre2' : (pre₂ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre2]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₂ ++ [byteJ]) rest'' b' _ _ (by omega) hj1 hsplit' hrest1' hpre2' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx13, arm64_norm]) (by simp [hx14, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := b' :: rest'' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        wp_steps 1
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable steps from `+144` after decoding `(epoch, rest1)`. -/
theorem step_after_epoch_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (pre₁ rest1 : List (BitVec 8)) (epoch : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hmsg_eq : msg.bytes = version :: (pre₁ ++ rest1))
    (hpre : msgPreamble msg.bytes =
      if epoch == 0#64 then .error .msgDecode
      else
        match LibsignalSpqrV1.decodeVarint rest1 with
        | .error e => .error e
        | .ok (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else .error .msgDecode)
    (hpc : s.pc = spqrRecvPlacedEntry + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (1 + pre₁.length))
    (hx22 : s.readReg64 .x22 = epoch)
    (hP : P = spqrRecvPlacedPreambleFrame A st msg ret s0) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hidx_loop := step_index_loop_placed A ext st msg ret target_pc version epoch pre₁ rest1
    s0 post herr_tail hok_tail hpre1 hlen_lt 10 0 0#64 []
  have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
  dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hidx_loop ⊢
  wp_steps
  wp_if hepoch
  · have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp [hpre, hepoch]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hepoch_f : (epoch == 0#64) = false := beq_false_of_ne hepoch
    wp_steps
    wp_if hls
    · have hrest1_nil := rest1_nil_of_ule hmsg_symm.symm hlen_lt hls
      have herr : msgPreamble msg.bytes = .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_nil]; rfl
      exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
    · wp_steps 9
      obtain ⟨b₀, rest1', hrest1_cons⟩ := rest1_cons_of_not_ule hmsg_symm.symm hlen_lt hls
      have hlen_eq : msg.bytes.length = 1 + pre₁.length + rest1.length := by
        rw [← hmsg_symm, List.length_cons, List.length_append]
        omega
      have hpre1_lt : 1 + pre₁.length < 2 ^ 63 := by omega
      have hlen_ge : 2 ≤ msg.bytes.length := by
        rw [← hmsg_symm, hrest1_cons]; simp; omega
      have hsplit0 : msg.bytes = (version :: pre₁ ++ []) ++ b₀ :: rest1' := by
        rw [← hmsg_symm, hrest1_cons]; simp
      have hrest1_0 : rest1 = [] ++ b₀ :: rest1' := hrest1_cons
      have hpre0 : msgPreamble msg.bytes =
          match LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b₀ :: rest1') with
          | none => .error .msgDecode
          | some (index, rest2) =>
            if index.toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
            else .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_cons]
        dsimp only [LibsignalSpqrV1.decodeVarint, decode_varint, Bool.false_eq_true, ↓reduceIte]
        cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b₀ :: rest1') <;> rfl
      exact hidx_loop rest1' b₀ _ P (by omega) (by omega) hsplit0 hrest1_0 rfl hpre0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
        (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        hP

set_option maxHeartbeats 1600000 in
/-- Relocatable epoch varint loop (`+96 .. +140`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_epoch_loop_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (rest0 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₁ rest0' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁) ++ byteJ :: rest0' →
      rest0 = pre₁ ++ byteJ :: rest0' →
      pre₁.length = j →
      (msgPreamble msg.bytes =
        match LibsignalSpqrV1.decodeVarintLoop j out (byteJ :: rest0') with
        | none => .error .msgDecode
        | some (epoch, rest1) =>
          if epoch == 0#64 then .error .msgDecode
          else
            match LibsignalSpqrV1.decodeVarint rest1 with
            | .error e => .error e
            | .ok (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode) →
      s.pc = spqrRecvPlacedEntry + 96#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x11 = msg.ptr →
      s.readReg64 .x12 = BitVec.ofNat 64 (min rest0.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x22 = out →
      P = spqrRecvPlacedPreambleFrame A st msg ret s0 →
      SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₁ rest0' byteJ s P hjk hj hsplit hrest0 hpre1 hpre
      hpc hrun hsp htr hx0 hx19 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx14 hx22 hP
    have hafter := step_after_epoch_placed A ext st msg ret target_pc version
      (pre₁ ++ [byteJ]) rest0' (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) s0
    have hoff : msg.ptr + BitVec.ofNat 64 (j + 1) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁).length := by
      simp only [List.length_cons, hpre1]
    have hexp := msg_expose_byte A msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest0_symm := hrest0.symm; clear hrest0
    subst hP
    dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry, spqrRecvPlacedPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest0.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest0_symm.symm hpre1 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match LibsignalSpqrV1.decodeVarint rest0' with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ rest0') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
    · have hlt : j + 1 < min rest0.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest0'', rfl⟩ := varint_cont_of_lt hrest0_symm.symm hpre1 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match LibsignalSpqrV1.decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest0'') with
            | none => .error .msgDecode
            | some (epoch, rest1) =>
              if epoch == 0#64 then .error .msgDecode
              else
                match LibsignalSpqrV1.decodeVarint rest1 with
                | .error e => .error e
                | .ok (index, rest2) =>
                  if index.toNat < 2 ^ 32 then
                    .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
                  else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: (pre₁ ++ [byteJ])) ++ b' :: rest0'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest0' : rest0 = (pre₁ ++ [byteJ]) ++ b' :: rest0'' := by
          rw [← hrest0_symm]; simp [List.append_assoc]
        have hpre1' : (pre₁ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre1]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₁ ++ [byteJ]) rest0'' b' _ _ (by omega) hj1 hsplit' hrest0' hpre1' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx11, arm64_norm]) (by simp [hx12, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match LibsignalSpqrV1.decodeVarint (b' :: rest0'') with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ b' :: rest0'') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        wp_steps 1
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
