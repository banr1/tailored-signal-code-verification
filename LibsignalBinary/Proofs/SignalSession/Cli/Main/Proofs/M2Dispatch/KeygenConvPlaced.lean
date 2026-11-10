/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Relocatable `keygen` Shared Context & Convergence Blocks (Block `617`)

Shared parser state context (`KeygenCtxPlaced`, `KeygenGoalPlaced`) and convergence blocks
(`M+0x524 .. M+0x550`, `0xf40`, `0xfc4 .. 0xfe0`) for `keygen`'s `u32` count parser under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

def keygenBase (A : RustAlloc) (s0 : State) (stk : Nat)
    (buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (me : AddrV) (Statics : SepProp) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  addrWords A me cap ptr (BitVec.ofNat 64 me.name.length) devw ∗
    argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
    argsBuf A 3#64 buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
    ((s0.readReg64 .x1) ↦₆₄ p0) ∗ cStrAt p0 (bytesOfString "libsignal-cli") ∗
    ((s0.readReg64 .x1 + 8#64) ↦₆₄ p1) ∗ cStrAt p1 bs1 ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ p2) ∗ cStrAt p2 bs2 ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ p3) ∗
    ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ 0#64) ∗
    mainSaved s0 ∗
    ((fsp + 0x48#64) ↦₆₄ devw) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
    memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
    stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ Statics

structure KeygenRegs (s0 s : State) (buf vcap vptr : BitVec 64) : Prop where
  x19 : s.readReg64 (.gpr 19#5) = buf
  x20 : s.readReg64 (.gpr 20#5) = vptr
  x23 : s.readReg64 (.gpr 23#5) = vcap
  x24 : s.readReg64 (.gpr 24#5) = 3#64
  trace : s.trace = s0.trace
  fs : s.fs = s0.fs

theorem shl32_of_lo32 {x : BitVec 64} {v : Nat} (hv : v < 2 ^ 32)
    (hx : x.setWidth 32 = BitVec.ofNat 32 v) :
    x <<< 32 = (BitVec.ofNat 64 v) <<< 32 := by
  have h1 : (x.setWidth 32).toNat = v := by
    rw [hx]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  bv_bits

theorem shl32_bit0 (x : BitVec 64) :
    (x <<< 32).getLsbD 0 = false := by
  bv_bits

theorem shr32_shl32 {v : Nat} (hv : v < 2 ^ 32) :
    ((BitVec.ofNat 64 v) <<< 32) >>> 32 = BitVec.ofNat 64 v := by
  bv_bits

theorem digit_hi_false {b : BitVec 8} (hd : isDigit b = true) :
    BitVec.ult 9#32 (b.setWidth 32 - 48#32) = false := by
  have hle : b.setWidth 32 - 48#32 ≤ 9#32 := (sub48_ule_9_iff_isDigit b).mpr hd
  simp only [BitVec.ult]; simp only [BitVec.le_def] at hle
  exact decide_eq_false (by omega)

theorem digit_hi_true {b : BitVec 8} (hnd : ¬ isDigit b = true) :
    BitVec.ult 9#32 (b.setWidth 32 - 48#32) = true := by
  have hnle : ¬ (b.setWidth 32 - 48#32 ≤ 9#32) := mt (sub48_ule_9_iff_isDigit b).mp hnd
  simp only [BitVec.ult]; simp only [BitVec.le_def] at hnle
  exact decide_eq_true (by omega)

theorem madd_digit_lo32 {b : BitVec 8} {acc : Nat}
    (hd : isDigit b = true) (_hlt : 10 * acc + (b.toNat - 48) < 2 ^ 32) :
    (b.setWidth 32 - 48#32) + BitVec.ofNat 32 acc * 10#32 =
      BitVec.ofNat 32 (10 * acc + (b.toNat - 48)) := by
  simp only [isDigit, decide_eq_true_eq] at hd; bv_omega

theorem cond_513_257_bit0 (c : Bool) :
    (if c = true then (0x201#64 : BitVec 64) else 0x101#64).getLsbD 0 = true := by
  cases c <;> decide

macro "kg_simp" : tactic =>
  `(tactic| simp only [BitVec.zeroExtend, bne, shl32_bit0, List.length_nil, Nat.add_zero,
      beq_self_eq_true, arm64_norm, *])

structure KeygenCtxPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustAlloc) (uuidParse : UuidParser) (i : Inputs) (s0 : State) (ret : BitVec 64)
    (stk hookStack resStack : Nat) (buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (me : AddrV)
    (Statics : SepProp) (Q Qp : State → SepProp → Prop) (oom : State → SepProp) : Prop where
  hc : MainCalleesBlk617 A H uuidParse hookStack resStack
  hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk
  hstk64 : stk ≤ 2 ^ 63
  hok : CliInputsOk i
  hne : i.argv ≠ []
  hlen : i.argv.length = 3
  hps : [(p1, bs1), (p2, bs2), (p3, bs3)].map (·.2) = i.argv.map bytesOfString
  hcmd : bs1 = utf8 "keygen"
  haddr : addrParse uuidParse bs2 = some me
  hvcap : vcap ≠ 0#64
  hexit : ExitKPlacedRet CodeOk H A s0 ret stk
    (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
      s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp
  hnext : ∀ (s' : State) (w : CallW) (c : CallV),
    parseArgs uuidParse (i.argv.map bytesOfString) = some c →
    AtCallPlaced CodeOk s0 s' w i.argv.length buf →
    SepWPp (mProgPlaced H) ret s'
      (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argvAtP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
      Q Qp oom

abbrev KeygenGoalPlaced [LibsignalPlacement] {CodeOk : Memory → Prop} {H : LibsignalHooks}
    {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (_K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (s : State) (w3 : BitVec 64) (PreP3 : SepProp) : Prop :=
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  SepWPp (mProgPlaced H) ret s
    (PreP3 ∗ ((fsp + 0x40#64) ↦₆₄ w3) ∗
      keygenBase A s0 stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics)
    Q Qp oom

theorem KeygenCtxPlaced.parse_none [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = none) :
    parseArgs uuidParse (i.argv.map bytesOfString) = none := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu]

theorem KeygenCtxPlaced.parse_gt100 [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {v : Nat}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v) (hgt : ¬ v ≤ 100) :
    parseArgs uuidParse (i.argv.map bytesOfString) = none := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu, hgt]

theorem KeygenCtxPlaced.parse_ok [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {v : Nat}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v) (hle : v ≤ 100) :
    parseArgs uuidParse (i.argv.map bytesOfString) = some (.keygen me v) := by
  rw [← K.hps]
  simp only [List.map_cons, List.map_nil, parseArgs, K.hcmd, ↓reduceIte, K.haddr, hu, hle]

theorem step_keygen_530_fail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x538) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hw11 : (s.readReg64 (.gpr 11#5)).setWidth 32 = 0#32)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb44#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0xb44 :=
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre (by
      let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
      dsimp only [keygenBase]
      have hperm : ∀ (P3 W3 AW V B X0 C0 X1 C1 X2 C2 X3 X4 MS W4 W1 M1 M2 ST PL STX : SepProp),
          P3 ∗ W3 ∗ (AW ∗ V ∗ B ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ C2 ∗ X3 ∗ X4 ∗
            MS ∗ W4 ∗ W1 ∗ M1 ∗ M2 ∗ ST ∗ PL ∗ STX) ⊢
            (W3 ∗ W4 ∗ W1 ∗ M1 ∗ M2) ∗
              (AW ∗ V ∗ B ∗ MS ∗ ST ∗ PL ∗
                (P3 ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ C2 ∗ X3 ∗ X4 ∗ STX)) :=
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
      have hp2 : ∀ (M AW V B MS ST PL R : SepProp),
          M ∗ (AW ∗ V ∗ B ∗ MS ∗ ST ∗ PL ∗ R) ⊢ AW ∗ V ∗ B ∗ MS ∗ M ∗ ST ∗ PL ∗ R :=
        fun _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
      exact Entails.trans (hperm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 devw w1))
          (hp2 _ _ _ _ _ _ _ _))) ?_
  rw [← K.hlen]
  exact step_drop_addr_ae8_placed (buf := buf) (vcap := vcap) (vptr := vptr)
    (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 me.name.length) (devw := devw) (me := me)
    (ps := [(p1, bs1), (p2, bs2), (p3, bs3)])
    K.hc K.hstk K.hstk64 K.hok K.hne hparse hin1
    (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, kr.x19])
    (by simp only [arm64_norm, kr.x20])
    (by change _ = cap; simp only [show Reg.x1 = Reg.gpr 1#5 from rfl, arm64_norm, hx1])
    (by simp only [arm64_norm, kr.x23])
    (by simp only [arm64_norm, kr.x24, K.hlen])
    K.hvcap (by simp only [arm64_norm, kr.trace]) (by simp only [arm64_norm, kr.fs]) K.hexit

theorem step_keygen_530_ok_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {n : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x538) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hw11 : (s.readReg64 (.gpr 11#5)).setWidth 32 = 1#32)
    (hw21 : (s.readReg64 (.gpr 21#5)).setWidth 32 = BitVec.ofNat 32 n)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.keygen me n)) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced, keygenBase]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align0 := fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x550#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x550 := {
    pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
    run := by simp only [arm64_norm, *]
    sp := by simp only [arm64_norm, *]
    fp := by simp only [arm64_norm, *]
    inv := hinv1
    vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
    spAligned := hsp0 }
  let w5v := ((s.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64
  let w : CallW := ⟨0x8000000000000000#64, cap, ptr, BitVec.ofNat 64 me.name.length, devw, w5v,
    s.readReg64 (.gpr 26#5)⟩
  have hw5_lo : w5v.setWidth 32 = BitVec.ofNat 32 n := by
    dsimp only [w5v]; rw [← hw21]; bv_bits
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_ok_tail_548_placed (buf := buf) (vcap := vcap) (vptr := vptr) (p0 := p0) (w := w)
      (c := .keygen me n) (ps := [(p1, bs1), (p2, bs2), (p3, bs3)]) (Statics := Statics)
      K.hc K.hstk K.hstk64 hparse hin1
      (by simp only [arm64_norm, kr.x19]) (by simp only [arm64_norm, kr.x20])
      (by simp only [arm64_norm, kr.x23])
      (by simp only [arm64_norm, kr.x24, K.hlen])
      (by simp only [arm64_norm, w]) (by simp only [arm64_norm, hx22, w])
      (by simp only [arm64_norm, w])
      (by simp only [arm64_norm, BitVec.zero_or, w, w5v])
      K.hvcap (by simp only [arm64_norm, kr.trace]) (by simp only [arm64_norm, kr.fs]) K.hnext)
  rw [hfsp, K.hlen]
  simp only [arm64_norm]
  dsimp only [callHeap, argvAtP, w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, show Reg.x1 = Reg.gpr 1#5 from rfl, hx1, hx15]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (pure_intro_entails ⟨trivial, hw5_lo⟩ (Entails.refl _))))
  exact Entails.of_eq (by ac_rfl)

theorem step_keygen_52c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x534) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  exact step_keygen_530_fail_placed K
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
    ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
     by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
     by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
    (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
    (by simp only [arm64_norm]) hparse

theorem step_keygen_f04_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xf40) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx13 : s.readReg64 (.gpr 13#5) = ptr) (hx14 : s.readReg64 (.gpr 14#5) = cap)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  exact step_keygen_530_fail_placed K
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
    ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
     by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
     by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm]) hparse

theorem step_keygen_fac_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {v : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xfe0) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hv_lt : v < 2 ^ 32) (hx8 : s.readReg64 (.gpr 8#5) = (BitVec.ofNat 64 v) <<< 32)
    (hne_ds : stripPlus bs3 ≠ []) (hdig : ∀ b ∈ stripPlus bs3, isDigit b = true)
    (hval : (stripPlus bs3).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = v) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  have hu : parseUnsigned (2 ^ 32 - 1) bs3 = some v :=
    parseUnsigned_some_of_digits hne_ds hdig hval (by omega)
  have hlsr : ((BitVec.ofNat 64 v) <<< 32) >>> 32 = BitVec.ofNat 64 v := shr32_shl32 hv_lt
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x538 :=
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
  rw [← mProgPlaced_eq]
  by_cases hle : v ≤ 100
  · have hcmp : (101#64).ule (BitVec.ofNat 64 v) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
        decide_eq_false_iff_not]
      omega
    exact step_keygen_530_ok_placed K hin1
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
      (by simp only [arm64_norm, hx1])
      (by simp only [arm64_norm, hcmp, Bool.false_eq_true, ↓reduceIte])
      (by apply BitVec.eq_of_toNat_eq; simp only [arm64_norm, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]; omega)
      (K.parse_ok hu hle)
  · have hcmp : (101#64).ule (BitVec.ofNat 64 v) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
        decide_eq_true_eq]
      omega
    exact step_keygen_530_fail_placed K hin1
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
      (by simp only [arm64_norm, hcmp, ↓reduceIte])
      (K.parse_gt100 hu hle)

theorem step_keygen_524_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {v : Nat}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x52c) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hv_lt : v < 2 ^ 32) (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 v)
    (hne_ds : stripPlus bs3 ≠ []) (hdig : ∀ b ∈ stripPlus bs3, isDigit b = true)
    (hval : (stripPlus bs3).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = v) :
    KeygenGoalPlaced K s w3 (cStrAt p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  have hshl := shl32_of_lo32 hv_lt hx9
  have hb0 := shl32_bit0 (s.readReg64 (.gpr 9#5))
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xfe0#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  exact step_keygen_fac_placed K
    ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
    ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
     by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
     by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
    (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
    (by simp only [arm64_norm, hx1]) hv_lt
    (by simp only [arm64_norm, *]) hne_ds hdig hval

theorem step_keygen_f90_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 remPtr : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {b : BitVec 8} {rest : List (BitVec 8)}
    {me : AddrV} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0xfc4) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = remPtr)
    (hrest : (remPtr ↦ₛ (b :: rest)) ∗ RestP3 = cStrAt p3 bs3)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 ((remPtr ↦ₛ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  rw [ProofLib.pointsToBytes_cons, sepConj_assoc, sepConj_assoc]
  have hb0_cond := cond_513_257_bit0 ((BitVec.zeroExtend 32 b - 48#32).ult 10#32)
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x534#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_52c_placed (w3 := w3) K
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1]) hparse)
  rw [← hrest, ProofLib.pointsToBytes_cons]; exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
