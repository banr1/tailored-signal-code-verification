/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp

/-!
# Phase 1 + Contract Assembly & Entry Wrapper for `spqr::send::<signal_session_ratchet::Coins>`

Combines `.rodata` and global invariant bundles with panic-polymorphic Phase 1 execution
(`+0..+224`) for `spqr::send::<signal_session_ratchet::Coins>` on the CLI image.
-/

@[expose] public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.EncodeVarint

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## 1. `.rodata` + Global Invariant (`TokenInit`, `logOff`) Extraction & Restoration -/

/-- Full `.rodata` + global invariant bundle for `spqr::send::<signal_session_ratchet::Coins>`:
    combines `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt img.base` with `GF.Mul2U16.tokenInitAt img.base` (`0x87ea0..0x87ea9`) and
    `logOff img` (`0x87ed0`). -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt (img : Obj.Image) : SepProp :=
  CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt img.base ∗
  GF.Mul2U16.tokenInitAt img.base ∗
  logOff img

/-- Extract `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt img` from `TokenInit img ∗ logOff img` under
    `Obj.Loads libsignalSessionImage img` and `img.FrozenLoaded s`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendFullRoAt {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp}
    (hP : s.mem ⊨ TokenInit img ∗ logOff img ∗ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt img ∗ P := by
  have hP' : s.mem ⊨ (GF.Mul2U16.tokenInitAt img.base ∗ logOff img) ∗ P := by
    refine Satisfies.mono (Entails.of_eq ?_) hP
    rw [GF.Mul2U16.tokenInitAt_eq_TokenInit]
    ac_rfl
  have hro := CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendRoAt himg hF hP'
  refine Satisfies.mono (Entails.of_eq ?_) hro
  dsimp only [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt]
  ac_rfl

/-- Discard the read-only `.rodata` tables in `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt img`, recovering
    `TokenInit img ∗ logOff img ∗ P`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt_restore {img : Obj.Image} {m : Memory} {P : SepProp}
    (hm : m ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt img ∗ P) :
    m ⊨ TokenInit img ∗ logOff img ∗ P := by
  have hm' :
      m ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt img.base ∗ (TokenInit img ∗ logOff img ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendFullRoAt]
    rw [GF.Mul2U16.tokenInitAt_eq_TokenInit]
    ac_rfl
  exact Satisfies.of_sep_right hm'

/-! ## 2. `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts` Assembly from Hooks -/

/-- Assemble `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs)`
    from `TripleRatchetHooks`, `SpqrHooks`, and `Obj.Loads libsignalSessionImage img`
    (with `<States>::from_pb` discharged unconditionally via `States.FromPb.states_from_pb_ok_x`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContracts_of_hooks_and_remaining
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs) := by
  have hC : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K)
      (tripleRatchetExterns C ctl abs) :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContracts_of_hooks himg hTH hSH
    (States.FromPb.states_from_pb_ok_x hC.toAllocContracts)

/-! ## 3. Phase 1 Early-Return Pure Model Equations & `tapeAfter` at `0` Draws -/

/-- When `0` tape bytes are drawn, `tapeAt ctl cur rest` decomposes into
    `⌜rest.length < 2 ^ 63⌝ ∗ tapeAfter ctl cur rest 0`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.tapeAt_eq_pure_sep_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest = ⌜rest.length < 2 ^ 63⌝ ∗ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  simp only [Nat.zero_min, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero, List.take_zero,
    List.drop_zero, pointsToBytes_nil, emp_sepConj, sepConj_assoc]

/-- `tapeAt ctl cur rest` entails `tapeAfter ctl cur rest 0`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.tapeAt_entails_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  rw [CryptoVerification.Cli.SpqrV1.Top.Send.tapeAt_eq_pure_sep_tapeAfter_zero]
  exact Entails.pure_left fun _ => Entails.refl _

/-- Continuation from `+224` supporting an additional panic disjunct `φ_panic`
    in `hok_next`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_224_panic {F : ShaCompress} {φ_panic : Prop}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hbase : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hfrom_pb : StatesFromPbOkX img A F ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    {s0 s : State} (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1) {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0) (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ err : LibsignalSpqrV1.Error,
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ st0 : States spqrPolyApi (spqrAuthApi F),
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ sf : State, ImgCallInv img sf →
        sf.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesFromPbName) img hinv ?_
  refine CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_pre_states_from_pb_224 hpc hrun hsp hfsp_align htr hx20 ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 _ hx23_1 _ _ hx26_1 _ _ hx29_1 hx30_1
  refine finish_sepWP_inImage hpc1 hrun1 (fun hinv1 => ?_) (Entails.refl _)
  rw [hx19] at hx19_1; rw [hx23] at hx23_1; rw [hx26] at hx26_1
  rw [memRegion_190_1f20_split_states_from_pb (s0.sp - 0x1f80#64)]
  refine call_inImage_calleeStack_panic (spec := statesFromPbSpecX A F img.base)
    (s0.sp - 0x1f80#64) statesFromPbStackX (by decide)
    (x := ({ out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } : StatesFromPbGhost))
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = (s0.sp - 0x1f80#64) + 0xb0#64 ∧
      img.base &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound v1)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) chunkedStatesSize ∗
      Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
      statesFromPbJumpTableAt img.base ∗ A.pool)
    (T_post := fun _ =>
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
        (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
      statesFromPbJumpTableAt img.base ∗ A.pool)
    (F := memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
      memRegion ret 72 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
    hfrom_pb hinv1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [statesFromPbSpecX]; rw [hsp1]; ac_rfl)
    ⟨hx8_1, hx0_1, hbase, hpts⟩ (by dsimp only [chunkedStatesSize]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [statesFromPbSpecX]; rw [hsp1]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ _ hvregs2
  have htr2' : s2.trace = s0.trace := htr2.trans htr1
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := (hvregs2.trans hx29_1.2).trans hvregs
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx21_1] at hx21_2
  rw [hx23_1] at hx23_2; rw [hx26_1] at hx26_2
  rcases hres : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with (err | _) | st0
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
      memRegion ret 72 ∗ A.pool ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
    rw [memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64)]
    have herr := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_states_from_pb_err_step (F := F) hA hdropChain s0 s2 ret w0 w1 vn chain err
      (statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2
    refine sepWPp_of_early_return (SepWP.mono herr ?_) (herr_post err hres)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hPf, hsp_f, hcc_f, htr_f.trans htr2'⟩
  · dsimp only [resultChunkedStatesAt]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜False⌝ ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
       memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       statesFromPbJumpTableAt img.base ∗ A.pool ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    exact SepWPp.pure_left fun hfalse => False.elim hfalse
  · rw [← hres]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
        (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    rw [memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64),
        memRegion_b0_1260_split_930_950 (s0.sp - 0x1f80#64)]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x950#64) 928 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base) ∗
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8 ∗
       memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
       stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_inImage (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + statesSendArmOffset st0) img hinv2 ?_
    refine CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_states_from_pb_ok_step hbase hA hpc2 hrun2 hsp2 hfsp_align htr2' hx21_2 hx26_2 hres ?_
    intro sf hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f _ hx23_f hx24_f hx25_f hx26_f hx28_f hx29_f
    rw [hx19_2] at hx19_f; rw [hx23_2] at hx23_f
    refine finish_sepWP_inImage hpc_f hrun_f
      (fun hinv_f => hok_next st0 hres sf hinv_f hpc_f hrun_f hsp_f htr_f
        hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx26_f hx28_f (hx29_f.2.trans hvregs2')) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8) ∗
       (memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 928 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600))) ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
       memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
       Rest) by ac_rfl)) ?_
    rw [memRegion_b0_950_and_cf0_1f20_rejoin (s0.sp - 0x1f80#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Continuation from `+156` supporting an additional panic disjunct `φ_panic`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_156_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {φ_panic : Prop}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hbase : img.base &&& 0xfff#64 = 0#64)
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContracts img.base A ext) (hfrom_pb : StatesFromPbOkX img A F ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    {s0 s : State} (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + 156#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0) (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : LibsignalSpqrV1.Error),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ sf : State, ImgCallInv img sf →
        sf.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hinner : pq.inner with _ | ⟨⟨v1⟩⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
      (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
      (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
      DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
      (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
      (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
      memRegion ret 72 ∗ A.pool ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
    have hnone := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_inner_none_step (H_inner := H_inner) hA hdropChain s0 s ret
      w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain
      (statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx20 hx23 hlen16
    refine sepWPp_of_early_return (SepWP.mono hnone ?_) (hnone_post hinner)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hPf, hsp_f, hcc_f, htr_f.trans htr⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
      (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
      (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
      DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
      (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
      (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_inImage (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + 224#64) img hinv ?_
    have h224 := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_inner_some_to_224 (ext := ext) h_inner_eq s0 s ret
      w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain v1
      (memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx20 hx23 hx26 hlen16
    refine SepWP.mono h224 ?_
    intro sm Pm hpc_m hrun_m ⟨hPm, hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hinv_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_224_panic img A ext hbase hA hfrom_pb hdropChain ret w0 w1
        pq.versionNegotiation pq.chain v1 (hpts_of_v1 v1 hinner)
        hinv_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m
        (fun err hres => herr_post v1 err hinner hres)
        (fun st0 hres => hok_next v1 st0 hinner hres)
        (hvregs_m.trans hvregs)))

/-- Continuation from `+80` supporting an additional panic disjunct `φ_panic`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_80_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hbase : img.base &&& 0xfff#64 = 0#64)
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContracts img.base A ext) (hfrom_pb : StatesFromPbOkX img A F ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    {s0 s : State} (ret : BitVec 64) (stBytes : Bytes) (hlen : stBytes.length < 2 ^ 32)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + 80#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ pq : PqRatchetState,
      spqrDecodeState stBytes = .ok pq → pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : LibsignalSpqrV1.Error),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ w0 w1 : BitVec 64, w0 ≠ DecodeState.none2Cap →
      ∀ sf : State, ImgCallInv img sf →
        sf.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hdec : spqrDecodeState stBytes with e | pq
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ memRegion ret 72 ∗
      (A.pool ∗ statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
    have herr := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_decode_state_err_step (H_inner := H_inner) (A := A) (ext := ext)
      s0 s ret e (A.pool ∗ statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx26
    refine sepWPp_of_early_return (SepWP.mono herr ?_) (hdec_err_post e hdec)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_inImage (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + 156#64) img hinv ?_
    have h156 := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_decode_state_ok_to_156 (H_inner := H_inner) hA s0 s ret pq
      (memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx21 hx26
    refine SepWP.mono h156 ?_
    rintro sm Pm hpc_m hrun_m ⟨w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, hPm, hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hinv_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_156_panic img A ext hbase h_inner_eq hA hfrom_pb hdropChain
        ret w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq
        (fun v1 hinner => v1StatePtsBound_of_spqrDecodeState (F := F) (K := K) hlen hdec hinner)
        hinv_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m hl16 (hnone_post pq hdec)
        (fun v1 err hinner hres => herr_post pq v1 err hdec hinner hres)
        (fun v1 st0 hinner hres => hok_next pq v1 st0 hdec hinner hres w0 w1 hw0)
        (hvregs_m.trans hvregs)))

/-- Full Phase 1 execution of `spqr::send::<signal_session_ratchet::Coins>`
    supporting an additional panic disjunct `φ_panic` in `hok_next`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_phase1_step_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    {φ_panic : Prop}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hbase : img.base &&& 0xfff#64 = 0#64)
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContracts img.base A ext) (hdecode : DecodeStateOkX H_inner img A ext)
    (hfrom_pb : StatesFromPbOkX img A F ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 : State) (ret : BitVec 64) (st : VecArg) (hlen : st.bytes.length < 2 ^ 32)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s0) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState st.bytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ pq : PqRatchetState,
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : LibsignalSpqrV1.Error),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ w0 w1 : BitVec 64, w0 ≠ DecodeState.none2Cap →
      ∀ sf : State, ImgCallInv img sf →
        sf.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry img.base + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A ∗ memRegion ret 72 ∗ A.pool ∗
        Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ statesFromPbJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr DecodeState.decodeStateName) img hinv ?_
  have hpro := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_prologue_to_decode_state (b := img.base) (ext := ext) s0 ret st.v
    (st.at A ∗ memRegion ret 72 ∗ A.pool ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
     statesFromPbJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ Rest)
    hsp0_align hpc hrun hx0 hx1
  refine SepWP.mono hpro ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, ⟨_, hvregs1⟩, hx19_1, hx0_1, hx8_1, hx21_1, hx26_1, hx30_1, htr1⟩ hinv1
  refine SepWPp.weaken_pre hP1 ?_
  rw [memRegion_1f20_split_decode_state (s0.sp - 0x1f80#64)]
  refine call_inImage_calleeStack_panic (spec := decodeStateSpecX H_inner img.base A)
    (s0.sp - 0x1f80#64) decodeStateStackX (by decide)
    (x := ({ st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } : DecodeStateGhost))
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = st.v ∧ st.bytes.length < 2 ^ 32)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ st.at A ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 352 ∗ A.pool)
    (T_post := fun _ => Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ st.at A ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState st.bytes) ∗ A.pool)
    (F := memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      memRegion ret 72 ∗ statesFromPbJumpTableAt img.base ∗
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
    hdecode hinv1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [decodeStateSpecX]; rw [hsp1]; ac_rfl)
    ⟨hx8_1, hx0_1, hlen⟩ (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [decodeStateSpecX]; rw [hsp1]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 _ hx21_2 _ _ _ _ hx26_2 _ _ hvregs2
  rw [hx19_1] at hx19_2; rw [hx21_1] at hx21_2; rw [hx26_1] at hx26_2
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
    decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState st.bytes) ∗
    memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
    memRegion ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
    CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
    (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ Rest) by ac_rfl)) ?_
  exact CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_from_80_panic (F := F) (K := K) img A ext hbase h_inner_eq hA hfrom_pb hdropChain
    ret st.bytes hlen hinv2 hsp0_align hpc2 hrun2 hsp2 (htr2.trans htr1)
    hx19_2 hx21_2 hx26_2 hdec_err_post hnone_post herr_post hok_next
    (hvregs2.trans hvregs1)

end CryptoVerification.SpqrV1.Top.Send
