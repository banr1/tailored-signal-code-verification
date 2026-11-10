/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Budget Specifications & Envelopes

Allocation-event envelope `RecvCt2ChunkEnv`, panic budget invariant `recvCt2ChunkBudgetOnPanic`,
and fixed-base budget specifications (`recvCt2ChunkSpecX*`, `recvCt2ChunkSpecExt*`) for `0x5ec2c`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_418 blkPl_350 blkPl_418 lsProg_350 lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall extract_withLsCodeRoLoaded reserveCap
   sessionMemcpyRegionSpec tripleRatchetProgAtExt withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Bytes MlKem NUM_POLYS optKeyBytesAt)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (boolByte chunkAt polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff
   polyDecoderPadSize polyDecoderPtsNeededOff sortedSetPtListOf vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (DecodedMessageGhost decodedMessageStack decodedMessageTotal
   decodedMessage_eq_ok optVecU8Of)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (PolyDecodedMessageCall RecvCt2ChunkGhost SplitBytes
   ctLabelSym ekSentCt1ReceivedAt ekSentCt1ReceivedRecvChunkResultAt
   polyDecodedMessageName polyDecodedMessageStackX polyDecoderNew96
   recvCt2ChunkFrameBytes recvCt2ChunkName recvCt2ChunkStackExt recvCt2ChunkStackX
   sckaKeyInfoPrefixSym zeros32Sym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv VmPreserved rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (sliceConcat2Events sliceConcat3Events)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (AuthUpdateLenEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotsEnv addChunkSlotsEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty decodedMessagePlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)

/-! ## Execution-Order `AllocEvent` Envelopes & Non-Vacuity Witnesses -/

/-- Canonical `AllocEvent` envelope of `<PolyDecoder as Decoder>::decoded_message` (Block `418`)
    over `PolyDecodedMessageCall`. -/
def PolyDecodedMessageEnv (x : PolyDecodedMessageCall) (evs : List AllocEvent) : Prop :=
  DecodedMessageEnv x.dec evs

theorem polyDecodedMessageEnv_nonempty (x : PolyDecodedMessageCall) :
    ∃ evs, PolyDecodedMessageEnv x evs :=
  decodedMessageEnv_nonempty x.dec

/-- Deterministic heap allocation events of `alloc_mac_ct2` (`Part1b`, `+224 .. +292`) when
    `128 ≤ ct2FullLen`:
    - `ct2FullLen ≤ 128`: `__rust_alloc(128, 1)` for `ct2_128` (`mac` slice is empty);
    - `128 < ct2FullLen`: `__rust_alloc(ct2FullLen - 128, 1)` for `mac`, then
      `__rust_alloc(128, 1)` for `ct2_128`. -/
def recvCt2MacCt2AllocEvents (ct2FullLen : Nat) : List AllocEvent :=
  (if ct2FullLen ≤ 128 then [] else rustAllocEvents (ct2FullLen - 128) 1) ++
    rustAllocEvents 128 1

/-- Deterministic heap allocation events between `decapsulate_compressed_key` and
    `Authenticator::update` (`Part2`, `+480 .. +664`):
    `__rust_alloc(32, 1)` (`ss_raw`), `sliceConcat2(41)` (`info`), and
    `__rust_alloc_zeroed(32, 1)` (`ss`). -/
def recvCt2PreAuthUpdateEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ sliceConcat2Events 41 ++ rustAllocEvents 32 1

/-- Deterministic heap allocation events for `sliceConcat3(1131)` (`35 + 8 + 1088` bytes)
    followed by `libcrux_hmac::hmac` (`SHA256`) in `Part2b` (`+664 .. +860`). -/
def recvCt2HmacEvents : List AllocEvent :=
  sliceConcat3Events 1131 ++ libcruxHmacSha256Events

/-- Allocation envelope of `<Vec<u8>>::reserve(128)` on `self.uc.ct1` (`ct1.length = 960`) in
    `Part2b`:
    - `[]` when `1088 ≤ cap_ct1.toNat` (spare capacity `≥ 960 + 128`);
    - `rustReallocEvents c (reserveCap c 960 128) 1` for `960 ≤ c < 1088` when
      `do_reserve_and_handle` grows the existing `ct1` buffer. -/
def RecvCt2ReserveCt1Env (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    ∃ c : Nat, 960 ≤ c ∧ c < 1088 ∧
      evs = rustReallocEvents c (reserveCap c 960 128) 1

theorem recvCt2ReserveCt1Env_nil : RecvCt2ReserveCt1Env [] :=
  Or.inl rfl

theorem recvCt2ReserveCt1Env_nonempty : ∃ evs, RecvCt2ReserveCt1Env evs :=
  ⟨[], recvCt2ReserveCt1Env_nil⟩

theorem recvCt2ReserveCt1Env_of_doReserve (c : DoReserveCall)
    (hlen : c.bs.length = 960) (hadd : c.additional = 128)
    (hge : 960 ≤ c.cap.toNat) (hlt : c.cap.toNat < 1088) :
    RecvCt2ReserveCt1Env (doReserveEvents c) := by
  refine Or.inr ⟨c.cap.toNat, hge, hlt, ?_⟩
  unfold doReserveEvents
  split
  · rename_i h0
    rw [h0] at hge
    exact absurd hge (by decide)
  · rw [hlen, hadd]

/-- Optional final `32`-byte `EpochSecret.secret` allocation (`Part3b`):
    `[]` on `Err(Error::MacVerifyFailed)` or post-HMAC bounds/overflow panic, and
    `rustAllocEvents 32 1` on `Ok(Done)`. -/
def OptSecret32AllocEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustAllocEvents 32 1

theorem optSecret32AllocEnv_nil : OptSecret32AllocEnv [] :=
  Or.inl rfl

theorem optSecret32AllocEnv_alloc32 : OptSecret32AllocEnv (rustAllocEvents 32 1) :=
  Or.inr rfl

theorem optSecret32AllocEnv_nonempty : ∃ evs, OptSecret32AllocEnv evs :=
  ⟨[], optSecret32AllocEnv_nil⟩

/-- Post-`decaps` execution-order envelope of `<EkSentCt1Received>::recv_ct2_chunk` when
    `128 ≤ ct2FullLen`, `ct1.length = 960`, and `dk.length = 2400`:
    1. `recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents`;
    2. `AuthUpdateLenEnv rkLen 32` (`Authenticator::update`);
    3. `RecvCt2ReserveCt1Env` (`ct1.reserve(128)`);
    4. `recvCt2HmacEvents` (`sliceConcat3(1131)` + `libcrux_hmac::hmac`);
    5. `FreeOnlyEvs` (`mac_data` / `tag` temporary drops);
    6. `OptSecret32AllocEnv` (`EpochSecret.secret` `32`B allocation on `Ok(Done)`, `[]` on `Err`);
    7. `FreeOnlyEvs` (epilogue buffer drops and `drop_glue_sorted_set_pt16`). -/
def RecvCt2PostDecapsEnv (rkLen ct2FullLen : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
    (SeqEnv (AuthUpdateLenEnv rkLen 32)
      (SeqEnv RecvCt2ReserveCt1Env
        (SeqEnv (· = recvCt2HmacEvents)
          (SeqEnv FreeOnlyEvs
            (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))

theorem recvCt2PostDecapsEnv_nonempty (rkLen ct2FullLen : Nat) :
    ∃ evs, RecvCt2PostDecapsEnv rkLen ct2FullLen evs := by
  let g0 : CryptoVerification.SpqrV1.Auth.AuthenticatorGhost :=
    { rootKey := { cap := 0#64, ptr := 1#64 }, macKey := { cap := 0#64, ptr := 1#64 } }
  have hupd : AuthUpdateLenEnv rkLen 32
      (LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdatePinnedEvents g0 rkLen 32) :=
    LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdatePinnedEvents_mem_authUpdateLenEnv
      g0 rkLen 32
  let e1 := recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents
  let e2 := LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdatePinnedEvents g0 rkLen 32
  exact ⟨e1 ++ (e2 ++ ([] ++ (recvCt2HmacEvents ++ ([] ++ ([] ++ []))))),
    SeqEnv.append rfl
      (SeqEnv.append hupd
        (SeqEnv.append recvCt2ReserveCt1Env_nil
          (SeqEnv.append rfl
            (SeqEnv.append FreeOnlyEvs.nil
              (SeqEnv.append optSecret32AllocEnv_nil FreeOnlyEvs.nil)))))⟩

/-- Post-`decoded_message` allocation envelope of `<EkSentCt1Received>::recv_ct2_chunk`
    (mirroring the binary's exact check order):
    - `none` (`StillReceiving`): `[]`;
    - `some ct2Full` with `ct2Full.length < 128`: `[]` (`slice_index_fail` before `alloc_mac_ct2`);
    - `some ct2Full` with `128 ≤ ct2Full.length` and `ct1Len ≠ 960 ∨ dkLen ≠ 2400`:
      `recvCt2MacCt2AllocEvents ct2Full.length` (`alloc_mac_ct2` runs before `decaps` panics via
      `unwrap_failed`);
    - `some ct2Full` with `128 ≤ ct2Full.length`, `ct1Len = 960`, and `dkLen = 2400`:
      `RecvCt2PostDecapsEnv rkLen ct2Full.length`. -/
def RecvCt2TailEnv (rkLen ct1Len dkLen : Nat) : Option Bytes → List AllocEvent → Prop
  | none, evs => evs = []
  | some ct2Full, evs =>
    if ct2Full.length < 128 then
      evs = []
    else if ct1Len != 960 || dkLen != 2400 then
      evs = recvCt2MacCt2AllocEvents ct2Full.length
    else
      RecvCt2PostDecapsEnv rkLen ct2Full.length evs

theorem recvCt2TailEnv_nonempty (rkLen ct1Len dkLen : Nat) (optCt2 : Option Bytes) :
    ∃ evs, RecvCt2TailEnv rkLen ct1Len dkLen optCt2 evs := by
  cases optCt2 with
  | none => exact ⟨[], rfl⟩
  | some ct2Full =>
    dsimp only [RecvCt2TailEnv]
    split
    · exact ⟨[], rfl⟩
    · split
      · exact ⟨recvCt2MacCt2AllocEvents ct2Full.length, rfl⟩
      · exact recvCt2PostDecapsEnv_nonempty rkLen ct2Full.length

/-- Canonical execution-order `AllocEvent` envelope of
    `<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk` (Block `350`):
    - `x.epoch != x.self.uc.epoch`: `[]` (immediate `assert_failed` panic);
    - `x.epoch == x.self.uc.epoch`: sequential composition of `<PolyDecoder>::add_chunk`
      (`AddChunkSlotsEnv`), `<PolyDecoder>::decoded_message` (`DecodedMessageEnv`), and
      `RecvCt2TailEnv`. -/
def RecvCt2ChunkEnv {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  if x.epoch != x.self.uc.epoch then
    evs = []
  else
    let receivingCt2 := addChunkTotal x.self.receiving_ct2 x.chunk
    SeqEnv (AddChunkSlotsEnv x.self.receiving_ct2.pts)
      (SeqEnv (DecodedMessageEnv receivingCt2)
        (RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
          (decodedMessageTotal receivingCt2)))
      evs

attribute [local irreducible] addChunkTotal decodedMessageTotal

theorem recvCt2ChunkEnv_nonempty {F : ShaCompress} (x : RecvCt2ChunkGhost F) :
    ∃ evs, RecvCt2ChunkEnv x evs := by
  unfold RecvCt2ChunkEnv
  split
  · exact ⟨[], rfl⟩
  · dsimp only
    rcases decodedMessageEnv_nonempty (addChunkTotal x.self.receiving_ct2 x.chunk) with
      ⟨eDec, heDec⟩
    rcases recvCt2TailEnv_nonempty x.self.uc.auth.rootKey.length
      x.self.uc.ct1.length x.self.uc.dk.length
      (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk)) with ⟨eTail, heTail⟩
    exact ⟨[] ++ (eDec ++ eTail),
      SeqEnv.append (addChunkSlotsEnv_nil x.self.receiving_ct2.pts)
        (SeqEnv.append heDec heTail)⟩

theorem recvCt2ChunkEnv_of_stillReceiving {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    {eAdd eDec : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hdec_none : decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk) = none)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hdec : DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk) eDec) :
    RecvCt2ChunkEnv x (eAdd ++ eDec) := by
  unfold RecvCt2ChunkEnv
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have htail :
      RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk)) [] := by
    rw [hdec_none]; rfl
  simpa only [List.append_nil] using SeqEnv.append hadd (SeqEnv.append hdec htail)

/-! ## Budget-Threaded `<PolyDecoder as Decoder>::decoded_message` Specifications & Bridge -/

/-- Envelope-parametric relocatable (`[LibsignalPlacement]`) callee specification of
    `<PolyDecoder as Decoder>::decoded_message` (Block `418`, `onPanic = ⌜False⌝`,
    `onOom = ⌜False⌝`). -/
def polyDecodedMessagePlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PolyDecodedMessageCall → List AllocEvent → Prop) :
    Spec (PolyDecodedMessageCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧
      s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA vecHeaderBytes ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt s.sp polyDecodedMessageStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ opt : Option Bytes,
        ⌜x.dec.decodedMessage = .ok opt ∧ sf.trace = s0.trace ∧ Env x evs⌝ ∗
          optKeyBytesAt A.repAlloc x.outA opt) ∗
        polyDecoderAt A.repAlloc x.decA x.dec ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp polyDecodedMessageStackX

/-- Canonical relocatable budget specification of `<PolyDecoder as Decoder>::decoded_message`
    (Block `418`). -/
abbrev polyDecodedMessagePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyDecodedMessageCall × M.σ) :=
  polyDecodedMessagePlacedSpecOfEnv M A lim PolyDecodedMessageEnv

/-- Envelope-parametric relocatable contract for `<PolyDecoder as Decoder>::decoded_message`
    (Block `418`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
def PolyDecodedMessagePlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PolyDecodedMessageCall → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (blkPl_418).base
    (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpecOfEnv M A lim Env))

/-- Canonical relocatable budget contract for `<PolyDecoder as Decoder>::decoded_message`
    (Block `418`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
abbrev PolyDecodedMessagePlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyDecodedMessagePlacedOkXOfEnv M A lim PolyDecodedMessageEnv ext

private theorem optVecU8Of_eq_optKeyBytesAt (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

theorem polyDecodedMessagePlacedOkX_of_decodedMessage [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdm : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec M A lim))) :
    PolyDecodedMessagePlacedOkX M A lim ext := by
  unfold PolyDecodedMessagePlacedOkX PolyDecodedMessagePlacedOkXOfEnv
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpts_sort : x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
        ⌜s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          FitsEnv M lim st (PolyDecodedMessageEnv x)⌝ ∗
        (memRegion x.outA vecHeaderBytes ∗
          sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
          ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
          ((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
          memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim st s0 ∗
          stackAt s0.sp polyDecodedMessageStackX ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hpre0
      dsimp only [polyDecodedMessagePlacedSpec, polyDecodedMessagePlacedSpecOfEnv,
        polyDecoderAt, NUM_POLYS]
      sep_ac_rfl
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨⟨hlen, _⟩, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2.1⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec M A lim)).pre (x', st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec,
      polyDecodedMessagePlacedSpec, polyDecodedMessagePlacedSpecOfEnv,
      PolyDecodedMessageEnv, decodedMessageStack, polyDecodedMessageStackX, x'] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcro, hpre0⟩
  refine subroutine_ok.mono_outcome hdm (x', st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec, x'] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hevs, htr⟩, hpost_mem⟩
    rw [optVecU8Of_eq_optKeyBytesAt] at hpost_mem
    dsimp only [withLsCodeRoLoaded, polyDecodedMessagePlacedSpec, polyDecodedMessagePlacedSpecOfEnv,
      decodedMessageStack, polyDecodedMessageStackX] at hpost_mem ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨decodedMessageTotal x.dec, ?_⟩
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hdec_eq, htr, hevs⟩, hpost_mem⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- Envelope-parametric fixed-offset callee specification of
    `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`, `onPanic = ⌜False⌝`,
    `onOom = ⌜False⌝`). -/
def polyDecodedMessageSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (b : BitVec 64)
    (Env : PolyDecodedMessageCall → List AllocEvent → Prop) :
    Spec (PolyDecodedMessageCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧
      s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA vecHeaderBytes ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗
      stackAt s.sp polyDecodedMessageStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ opt : Option Bytes,
        ⌜x.dec.decodedMessage = .ok opt ∧ sf.trace = s0.trace ∧ Env x evs⌝ ∗
          optKeyBytesAt A.repAlloc x.outA opt) ∗
        polyDecoderAt A.repAlloc x.decA x.dec ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp polyDecodedMessageStackX

/-- Canonical fixed-offset budget specification of `<PolyDecoder as Decoder>::decoded_message`. -/
abbrev polyDecodedMessageSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (b : BitVec 64) :
    Spec (PolyDecodedMessageCall × M.σ) :=
  polyDecodedMessageSpecOfEnv M A lim b PolyDecodedMessageEnv

/-- Fixed-offset contract for `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`). -/
def PolyDecodedMessageOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecodedMessageName)
    ((polyDecodedMessageSpec M A lim img.base).inImage img)

/-! ## Budget-Threaded `<EkSentCt1Received>::recv_ct2_chunk` Specifications & Contracts -/

/-- Budget-form panic postcondition of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`):
    retains the genuine pure model panic `(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true`
    while eliminating `∨ allocFailedIn s0 sf`. -/
def recvCt2ChunkBudgetOnPanic {F : ShaCompress} (K : MlKem) (x : RecvCt2ChunkGhost F)
    (s0 sf : State) : SepProp :=
  ⌜(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded relocatable (`[LibsignalPlacement]`)
    specification of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
def recvCt2ChunkPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt s.sp recvCt2ChunkStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
        (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp recvCt2ChunkStackX
  onPanic := fun (x, _) s0 sf => recvCt2ChunkBudgetOnPanic K x s0 sf

/-- Single-envelope (`Env`) budget-threaded relocatable specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
abbrev recvCt2ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim Env Env

/-- Canonical budget-threaded relocatable specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
abbrev recvCt2ChunkPlacedSpec [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkPlacedSpecOfEnv K F M A lim RecvCt2ChunkEnv

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
def RecvCt2ChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_350 (Rust.withPanics ext))
    (blkPl_350).base
    (withLsCodeRoLoaded lsmpl
      (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv))

/-- Envelope-parametric relocatable contract for `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
abbrev RecvCt2ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim Env Env ext

/-- Canonical relocatable budget contract for `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
abbrev RecvCt2ChunkPlacedOkX [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  RecvCt2ChunkPlacedOkXOfEnv K F M A lim RecvCt2ChunkEnv ext

/-- Envelope-parametric fixed-offset specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, stack `recvCt2ChunkStackX`). -/
def recvCt2ChunkSpecOfEnv (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗
      stackAt s.sp recvCt2ChunkStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
        (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp recvCt2ChunkStackX
  onPanic := fun (x, _) s0 sf => recvCt2ChunkBudgetOnPanic K x s0 sf

/-- Canonical fixed-offset budget specification of `<EkSentCt1Received>::recv_ct2_chunk`
    (`0x5ec2c`, stack `recvCt2ChunkStackX`). -/
abbrev recvCt2ChunkSpec (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkSpecOfEnv K F M A lim b RecvCt2ChunkEnv

/-- Fixed-offset contract for `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, stack
    `recvCt2ChunkStackX`). -/
def RecvCt2ChunkOkX (img : Obj.Image) (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName)
    ((recvCt2ChunkSpec K F M A lim img.base).inImage img)

/-- Envelope-parametric fixed-offset specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, contract-backed stack
    `recvCt2ChunkStackExt`). -/
def recvCt2ChunkSpecExtOfEnv (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗
      stackAt s.sp recvCt2ChunkStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
        (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp recvCt2ChunkStackExt
  onPanic := fun (x, _) s0 sf => recvCt2ChunkBudgetOnPanic K x s0 sf

/-- Canonical fixed-offset contract-backed budget specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, stack `recvCt2ChunkStackExt`). -/
abbrev recvCt2ChunkSpecExt (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkSpecExtOfEnv K F M A lim b RecvCt2ChunkEnv

/-- Fixed-offset contract-backed `subroutine_ok` predicate for
    `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, stack `recvCt2ChunkStackExt`). -/
def RecvCt2ChunkOkExt (img : Obj.Image) (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName)
    ((recvCt2ChunkSpecExt K F M A lim img.base).inImage img)

/-! ## `VmPreserved`-Strengthened `SplitBytes` Relocation Combinators -/

/-- `VmPreserved`-strengthened `memcpy` relocation specification for `S : SplitBytes n P`,
    allowing `A.pool lim st s` to be transported across `504`-byte `ekSentCt1ReceivedSplit`
    copies via `A.pool_of_vmPreserved`. -/
def SplitBytes.memcpyVmSpec {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) :
    Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved S.memcpySpec

theorem SplitBytes.memcpyVm_ok {prog : Program} {entry : BitVec 64} {n : Nat}
    {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64)
    (hmc : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok prog entry (SplitBytes.memcpyVmSpec S) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [SplitBytes.memcpyVmSpec, withVmPreserved, SplitBytes.memcpySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc :
      s0.mem ⊨ (withVmPreserved sessionMemcpyRegionSpec).pre (dst, src, bs) s0 ∗ (S.heap bs ∗ R) := by
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩, ?_⟩
    rw [hlen]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h4
  refine (hmc.to_outcome (dst, src, bs) (S.heap bs ∗ R) s0 hpc hrun hpre_mc hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hpost1⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hx0_sf, htr⟩, hpost_mem⟩
    dsimp only [SplitBytes.memcpyVmSpec, withVmPreserved, SplitBytes.memcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    have harrange :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (S.heap bs ∗ R) =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ R := by sep_ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr)) hpost_mem
  · right; left
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; right
    refine ⟨hoom, ?_⟩
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget
