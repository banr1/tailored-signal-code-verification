/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Shared Step Lemmas for `PolynomialDecoder::encode`

Provides relocatable `[LibsignalPlacement]` basic-block steppers shared between
`PolynomialDecoder::encode [local#1]` (`Block 152`) and `[local#2]` (`Block 315`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

abbrev subroutine_ok_withLsCodeLoaded_dec := @subroutine_ok_withLsCodeLoaded

theorem step_msg48rep_polyDecLen_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (decA sp ret_pc : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  have hst : stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) =
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      (memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt (sp - 48#64) polyEncodedLenStack) := by
    rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64),
      stackAt_varint_eq_stack16 (by omega) (sp - 48#64)]
  refine SepWPp.call_cs_placed (x := PinnedEncLenGhost.mk decA g pb)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CSPlaced, polynomialDecoderEncodedLenElemsOutSpec,
      polynomialDecoderEncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withMsgEnc48CSPlaced, polynomialDecoderEncodedLenElemsOutSpec,
      polynomialDecoderEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, polynomialDecoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems hpts_eq hpts_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [hst]
    exact Entails.of_eq (by ac_rfl)


theorem polyDecoder_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOf resStack A)).pre
      ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, polyDecoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)


def IsPolyDecoderEncodeEntryProg (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧ IsPolyDecoderEncodeEntry b ext entry) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = @lsProg_152 inst H ∧ entry = (@blkPl_152 inst).base) ∨
    (prog = @lsProg_315 inst H ∧ entry = (@blkPl_315 inst).base))

theorem polyDecoderEncode_fetch_entry_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) = some ins)
    (hp1 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_152 H).fetch ((blkPl_152).base + 0#64) = some ins)
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_315 H).fetch ((blkPl_315).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, ext, rfl, hfn⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact polyDecoderEncode_fetch_entry hfn (h1 b ext) (h2 b ext)
  · simpa using @hp1 inst H
  · simpa using @hp2 inst H

theorem polyDecoderEncode_fetch_add_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some ins)
    (hp1 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_152 H).fetch ((blkPl_152).base + BitVec.ofNat 64 k) = some ins)
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, ext, rfl, hfn⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact polyDecoderEncode_fetch_add hfn (h1 b ext) (h2 b ext)
  · exact @hp1 inst H
  · exact @hp2 inst H

open Lean Elab Tactic in
scoped elab "pd_fetches_prog" hfn:ident lo:num hi:num : tactic => do
  let off1 := 0x37604
  let off2 := 0x4d14c
  let loN := lo.getNat
  let hiN := hi.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37604
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d14c
  for i in [loN / 4 : hiN / 4] do
    let k := 4 * i
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let kHex := String.ofList (Nat.toDigits 16 k)
    let p1 := mkIdent (`CryptoVerification |>.str s!"blkPC_152_rebase_fetch_0x{kHex}")
    let p2 := mkIdent (`CryptoVerification |>.str s!"blkPC_315_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := polyDecoderEncode_fetch_entry_prog $hfn
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff1 (by decide) $dec1)
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $p1 _ H)
          (fun [LibsignalPlacement] H => $p2 _ H)))
    else
      evalTactic (← `(tactic|
        have := polyDecoderEncode_fetch_add_prog $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff1 (by decide) $dec1)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $p1 _ H)
          (fun [LibsignalPlacement] H => $p2 _ H)))

/-- Step `+0..+36` (`0x37520..0x37544` / `0x52544..0x52568`):
allocates 48B frame (`msgEnc48SavedFrame`), saves `fp, lr, x21, x20, x19`, sets `x20 = decA`,
`x1 = v`, `x19 = v`, and `x0 = ((tag <<< 3) ||| 2#32).zeroExtend 64`. -/
theorem step_polyDecoder_prologue_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) (tag : BitVec 32) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (s1 : State) (sv3 : BitVec 64),
      s1.pc = entry + 36#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 →
      s1.readReg64 .x1 = v → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog ret s1
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 0 36; examples_hide_fetches
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  have hw0' : BitVec.truncate 32 (s.readReg64 .x0) = tag := hw0
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 36#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0] at hw0' ⊢; simp only [arm64_norm]
          exact polyDecoder_tag_orr_eq tag)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

theorem step_polyDecoder_mov_x0_x20_40_placed
    {prog : Program} {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 44#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = decA → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 40 44; examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 44#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

theorem step_polyDecoder_mov_x1_x19_48_placed
    {prog : Program} {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) (decA v x0v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 48#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = x0v) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 52#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = x0v → s1.readReg64 .x1 = v → s1.readReg64 .x19 = v →
      s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 48 52; examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 52#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+56..+64` (`0x37558..0x37560` / `0x5257c..0x52584`):
loads `w0 = [x20, #0x18]` (`pb.ptsNeeded`) and branches to `entry + 108#64` if `pb.ptsNeeded == 0#32`,
else falls through to `entry + 64#64`. -/
theorem step_polyDecoder_check_ptsNeeded_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.ptsNeeded == 0#32 then 108#64 else 64#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 56 64
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpn : (pb.ptsNeeded == 0#32)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 64#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 108#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+80..+104` (`0x37570..0x37588` / `0x52594..0x525ac`):
stores tag byte `0x08#8` (`field 1, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_ptsNeeded_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 104#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 80 104
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 104#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+108..+116` (`0x3758c..0x37594` / `0x525b0..0x525b8`):
loads `w0 = [x20, #0x1c]` (`pb.polys`) and branches to `entry + 160#64` if `pb.polys == 0#32`,
else falls through to `entry + 116#64`. -/
theorem step_polyDecoder_check_polys_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 108#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.polys == 0#32 then 160#64 else 116#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 108 116
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpl : (pb.polys == 0#32)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 160#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+132..+156` (`0x375a4..0x375bc` / `0x525c8..0x525e0`):
stores tag byte `0x10#8` (`field 2, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_polys_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 132#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 156#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 132 156
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 156#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+160..+172` (`0x375c0..0x375cc` / `0x525e4..0x525f0`):
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 3#32`, `x3 = v`. -/
theorem step_polyDecoder_prep_pts_placed
    {prog : Program} {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) (decA v sp : BitVec 64)
    (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 160#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 172#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg32 .x0 = 3#32 → s1.readReg64 .x1 = g.pts.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → s1.readReg64 .x3 = v →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog ret s1 (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 160 172; examples_hide_fetches; subst hP
  dsimp only [polyDecoderElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 172#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+176..+188` / `+248..+264` (`0x375d0..0x375dc` / `0x525f4..0x52600`):
loads `w8 = [decA + 0x20]` (`boolByte pb.isComplete`).
- If `pb.isComplete = false`, branches to `+248` and executes the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`).
- If `pb.isComplete = true`, falls through to `+188`. -/
theorem step_polyDecoder_check_isComplete_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program}
    {entry : BitVec 64} {s0 s : State} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (decA v sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hfalse : pb.isComplete = false → ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F))
    (htrue : pb.isComplete = true → ∀ s1 : State,
      s1.pc = entry + 188#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog (s0.readReg64 .lr) s1
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 176 188
  pd_fetches_prog hfn 248 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  cases hc : pb.isComplete
  · have hbyte : boolByte pb.isComplete = 0#8 := by rw [hc]; rfl
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
    apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr)
    dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← hbyte]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    · apply (hfalse hc)
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
  · have hbyte : boolByte pb.isComplete = 1#8 := by rw [hc]; rfl
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 188#64)
    dsimp only [polyDecoderElemsAt]; rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by rw [← hbyte]; dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (htrue hc _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1))

/-- Step `+204..+228` (`0x375ec..0x37604` / `0x52610..0x52628`):
stores tag byte `0x20#8` (`field 4, wire type varint`) into `curBs`, sets `x9 = curPtr`,
`x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length`, and compares `x8 = curCap` with `x10` at `+228`. -/
theorem step_polyDecoder_push_isComplete_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntryProg prog entry) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 204#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx8 : s.readReg64 .x8 = curCap) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 228#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x8 = curCap → s1.readReg64 .x9 = curPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      s1.pstate = subsPState64 curCap (BitVec.ofNat 64 (curBs ++ [0x20#8]).length) →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp prog ret s1
        (vecU8At A v curCap curPtr (curBs ++ [0x20#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 204 228; examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 228#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hlen1 : BitVec.ofNat 64 curBs.length + 1#64 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length := by
    rw [List.length_append, List.length_singleton]; exact (BitVec.ofNat_add curBs.length 1).symm
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x20#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+232..+264` (`0x37608..0x37628` / `0x5262c..0x5264c`):
stores value byte `0x01#8` into `curBs`, updates `[v + 16] = curBs.length + 1`, and executes
the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`). -/
theorem step_polyDecoder_push_isComplete_val_epilogue_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} {s0 s : State} (hfn : IsPolyDecoderEncodeEntryProg prog entry)
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 232#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length) (hx19 : s.readReg64 .x19 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches_prog hfn 232 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); dsimp only [msgEnc48SavedFrame]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
  refine SepWPp.weaken_pre
    (show _ ⊢ (vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
  · rw [← vecU8At_close_one A v curCap curPtr curBs 0x01#8 hlt]
    have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19)
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
    dsimp only [msgEnc48SavedFrame]
  · apply hnext
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · epochEncLen_cc_close
    · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩

theorem pd1_fetch_add_mono {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name = entry)
    {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  subst hfn; exact h1

open Lean Elab Tactic in
elab "pd1_fetches " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let off := 0x37604
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37604
  let helper := mkIdent ``CryptoVerification.SpqrV1.Prost.MessageEncode.pd1_fetch_add_mono
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := $helper $hfn (k := $kq) ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec)))

end CryptoVerification.SpqrV1.Prost.MessageEncode
