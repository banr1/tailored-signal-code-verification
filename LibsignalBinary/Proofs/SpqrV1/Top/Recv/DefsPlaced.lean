/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.RecvPlacedCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Placed
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpers
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon

/-!
# Relocatable Definitions for `spqr::recv`

Relocatable program, `.rodata` jump-table bundles, callee specifications, and
`SpqrRecvPlacedContracts` for `spqr::recv` (Block `329`) under `[LibsignalPlacement]`.
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
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

/-! ## 1. Rebased Program, Entry Address, and `.rodata` Bundle for Block `329` (`spqr::recv`) -/

/-- Rebased program for Block `329` (`spqr::recv`) under `Rust.withPanics ext`. -/
noncomputable abbrev spqrRecvPlacedProg (ext : String → Option (State → State)) : Program :=
  (blkPC_329).rebase (blkPl_329).base (Rust.withPanics ext)

/-- Symbolic entry address of Block `329` (`spqr::recv`). -/
noncomputable abbrev spqrRecvPlacedEntry : BitVec 64 := (blkPl_329).base

/-- Relocatable `SepWPp` enriched with `LibsignalCodeRoLoaded lsmpl s.mem`, automatically
    preserved across `Steps` (`SepWPpLS.of_sepWP`) and available to `withLsCodeRoLoaded lsmpl`
    callee contracts (relocatable counterpart of `SepWPpI`). -/
def SepWPpLS (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Q_err : State → SepProp → Prop) : Prop :=
  LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog ret s P Q Q_err

theorem _root_.Arm64.Steps.lsCodeRoLoaded {prog : Program} {s s' : State}
    (h : Steps prog s s') (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) :
    LibsignalCodeRoLoaded lsmpl s'.mem :=
  hcrl.of_keepsFrozen h.keepsFrozen

theorem SepWPpLS.of_sepWPp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Q_err) :
    SepWPpLS prog ret s P Q Q_err :=
  fun _ => h

theorem SepWPpLS.of_sepWP {prog : Program} {ret mid : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLS prog ret sm Pm Q Q_err)) :
    SepWPpLS prog ret s P Q Q_err := by
  intro hcrl R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hsteps.lsCodeRoLoaded hcrl) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPpLS.exists_elim {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Q_err : State → SepProp → Prop}
    (h : ∀ x, SepWPpLS prog ret s (P x) Q Q_err) :
    SepWPpLS prog ret s (∃∗ x, P x) Q Q_err :=
  fun hcrl => SepWPp.exists_elim (fun x => h x hcrl)

theorem SepWPpLS.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPpLS prog ret s P' Q Q_err) :
    SepWPpLS prog ret s P Q Q_err :=
  fun hcrl => SepWPp.mono_pre h (hwp hcrl)

theorem SepWPpLS.of_sepWP_ret_lscl {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : LibsignalCodeLoaded lsmpl s.mem → SepWP prog ret s P Q) :
    SepWPpLS prog ret s P Q Q_err :=
  fun hcrl => SepWPp.of_sepWP_ret (h hcrl.1)

theorem subroutine_ok_withMemEq_of_lscl {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem seq_clean_lscl {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hp hr ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hp hr hcl' hQ))

/-- Relocatable `.rodata` jump table for `<States>::from_pb` (Block `333`). -/
def statesFromPbJumpTablePlacedAt : SepProp :=
  (lsρ "spqr:.rodata.<spqr::v1::chunked::states::States>::from_pb") ↦ᵣ
    States.FromPb.statesFromPbJumpTableBytes

/-- Relocatable `.rodata` jump table for `<States>::recv` (Block `332`). -/
def statesRecvJumpTablePlacedAt : SepProp :=
  (lsρ "spqr:.rodata.<spqr::v1::chunked::states::States>::recv") ↦ᵣ
    States.Recv.statesRecvJumpTableBytes

/-- Relocatable `.rodata` bundle required by `<States>::recv` (Block `332`). -/
def statesRecvRoPlacedAt : SepProp :=
  statesRecvJumpTablePlacedAt ∗
  Unchunked.unchunkedSendCt2PlacedRoAt ∗
  GF.Mul2U16.tokenInitPlacedAt ∗
  GF.UnacceleratedMul.reduceTablePlacedAt

/-- Relocatable `.rodata` jump table for `<States>::into_pb` (Block `334`). -/
def statesIntoPbJumpTablePlacedAt : SepProp :=
  (lsρ "spqr:.rodata.<spqr::v1::chunked::states::States>::into_pb") ↦ᵣ
    States.IntoPb.statesIntoPbJumpTableBytes

/-- Combined relocatable `.rodata` separation-logic resource for `spqr::recv` (Block `329`). -/
def spqrRecvRoPlacedAt : SepProp :=
  Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
  statesFromPbJumpTablePlacedAt ∗
  statesRecvRoPlacedAt ∗
  statesIntoPbJumpTablePlacedAt

/-! ## 2. Relocatable Callee Specifications for Block `329` (`spqr::recv`) -/

/-- Relocatable specification for `spqr::decode_state` (Block `325`). -/
def decodeStatePlacedSpecX (H_inner : V1InnerHeapPred) (A : RustAlloc) : Spec DecodeStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32⌝ ∗
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗ stackAt s.sp decodeStateStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool ∗ stackAt s0.sp decodeStateStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification for `spqr::init_inner` (Block `324`). -/
def initInnerPlacedSpecX (A : RustAlloc) (F : ShaCompress) : Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63⌝ ∗
      memRegion x.out Drop.optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp initInnerStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp initInnerStack
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

/-- Relocatable specification for `<States>::from_pb` (Block `333`). -/
def statesFromPbPlacedSpecX (A : RustAlloc) (F : ShaCompress) : Spec StatesFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧ v1StatePtsBound x.pb⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      Drop.optProtoInnerStateAt A x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesFromPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA Drop.optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesFromPbStackX
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- Relocatable specification for `<States>::recv` (Block `332`). -/
def statesRecvPlacedSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem) : Spec (StatesRecvGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self⌝ ∗
      memRegion x.outA v1RecvSize ∗
      Drop.chunkedStatesAt A x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s.sp statesRecvStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoPlacedAt ∗
      A.pool ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun x s0 sf => statesRecvOnPanic K x s0 sf

/-- Relocatable specification for `<States>::into_pb` (Block `334`). -/
def statesIntoPbPlacedSpecX (A : RustAlloc) (F : ShaCompress) : Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out Drop.optProtoInnerStateSize ∗
      Drop.chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Drop.optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStackX
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-! ## 3. Relocatable Callee Contract Bundle (`SpqrRecvPlacedContracts`) -/

/-- Relocatable bundle of callee `subroutine_ok` contracts for Block `329` (`spqr::recv`). -/
structure SpqrRecvPlacedContracts (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State)) : Prop where
  dealloc_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)
  memcpy_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpySpec
  dropEpochSlice_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (Drop.dropProtoEpochSliceSpec A))
  dropOptProtoInnerState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (Drop.dropOptProtoInnerStatePlacedSpec A))
  dropOptProtoChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (Drop.dropOptProtoSpqrChainSpec A))
  dropChain_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (Drop.dropSpqrChainSpec A))
  dropPqRatchetState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (Drop.dropProtoPqRatchetStatePlacedSpec A))
  dropStates_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (Drop.dropChunkedStatesLocal2PlacedSpec A F))
  decodeState_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 325) (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX H_inner A))
  initInner_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 324) (withLsCodeRoLoaded lsmpl (initInnerPlacedSpecX A F))
  chainFrom_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith F) A))
  chainFromPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A))
  chainNew_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 363) (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith F) A))
  chainAddEpoch_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 368) (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) A))
  chainRecvKey_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 366) (withLsCodeRoLoaded lsmpl (chainRecvKeySpecX (spqrHkdfWith F) A))
  chainIntoPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A))
  messageDeserialize_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 351) (withLsCodeRoLoaded lsmpl (messageDeserializeSpecX spqrPolyApi A))
  statesFromPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 333) (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F))
  statesRecv_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 332) (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K))
  statesIntoPb_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 334) (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F))
  encodeToVec_ok :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 426) (withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A))
  /-- Representation equivalence between `DecodeState.optProtoInnerStateAt H_inner A a opt` and
      `Drop.optProtoInnerStateAt A a opt`. -/
  h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt

end CryptoVerification.SpqrV1.Top.Recv
