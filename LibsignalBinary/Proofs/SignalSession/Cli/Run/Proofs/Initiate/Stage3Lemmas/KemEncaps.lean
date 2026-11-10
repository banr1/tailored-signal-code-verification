/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Seed Packing & `kyber::encapsulate` (`+0x0ee8 → +0x0fb4`)

Packs all 32 low coin bytes `(coinWord t i _).truncate 8` into `[fsp + 0xfe0 .. fsp + 0x1000)`,
folds `[fsp + 0xfe0 .. fsp + 0x1000)` to `(fsp + 0xfe0) ↦ₛ (initiateKemCoins t).toList`, collapses
scratch slots `[fsp .. fsp + 0x70)`, invokes `kyberEncaps_ok_at_init`, and splits the `1600`-byte
output at `fsp + 0x1600` into `(fsp + 0x1600) ↦ₛ ct.toList` and `(fsp + 0x1c20) ↦ₛ ss.toList`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefix coinsCursorAt coinWord
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem memRegion4_split1 (p : BitVec 64) :
    memRegion p 4 =
      (∃∗ b0, p ↦₈ b0) ∗ (∃∗ b1, (p + 1#64) ↦₈ b1) ∗
      (∃∗ b2, (p + 2#64) ↦₈ b2) ∗ (∃∗ b3, (p + 3#64) ↦₈ b3) := by
  rw [← memRegion_merge_at p 1 3 (p + 1#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 1#64) 1 2 (p + 2#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 2#64) 1 1 (p + 3#64) (by bv_omega) (by decide),
      ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one]

private theorem pack4_bytes_eq (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) =
      (p ↦ₛ [b0, b1, b2, b3]) := by
  rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_nil]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]

private theorem vec32_chunks4_eq (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩, v.get ⟨1, by decide⟩, v.get ⟨2, by decide⟩, v.get ⟨3, by decide⟩] ++
      ([v.get ⟨4, by decide⟩, v.get ⟨5, by decide⟩, v.get ⟨6, by decide⟩, v.get ⟨7, by decide⟩] ++
      ([v.get ⟨8, by decide⟩, v.get ⟨9, by decide⟩, v.get ⟨10, by decide⟩, v.get ⟨11, by decide⟩] ++
      ([v.get ⟨12, by decide⟩, v.get ⟨13, by decide⟩, v.get ⟨14, by decide⟩, v.get ⟨15, by decide⟩] ++
      ([v.get ⟨16, by decide⟩, v.get ⟨17, by decide⟩, v.get ⟨18, by decide⟩, v.get ⟨19, by decide⟩] ++
      ([v.get ⟨20, by decide⟩, v.get ⟨21, by decide⟩, v.get ⟨22, by decide⟩, v.get ⟨23, by decide⟩] ++
      ([v.get ⟨24, by decide⟩, v.get ⟨25, by decide⟩, v.get ⟨26, by decide⟩, v.get ⟨27, by decide⟩] ++
       [v.get ⟨28, by decide⟩, v.get ⟨29, by decide⟩, v.get ⟨30, by decide⟩, v.get ⟨31, by decide⟩])))))) := by
  apply List.ext_getElem
  · simp [v.toList_length]
  · intro i hi1 hi2
    have hi : i < 32 := by simpa [v.toList_length] using hi1
    simp only [List.Vector.get]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | rfl | omega

private theorem kemCoins32_pointsTo_eq (fsp : BitVec 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ((fsp + 0xfe0#64) ↦₈ (coinWord t 0 (by decide)).truncate 8) ∗
    ((fsp + 0xfe1#64) ↦₈ (coinWord t 1 (by decide)).truncate 8) ∗
    ((fsp + 0xfe2#64) ↦₈ (coinWord t 2 (by decide)).truncate 8) ∗
    ((fsp + 0xfe3#64) ↦₈ (coinWord t 3 (by decide)).truncate 8) ∗
    ((fsp + 0xfe4#64) ↦₈ (coinWord t 4 (by decide)).truncate 8) ∗
    ((fsp + 0xfe5#64) ↦₈ (coinWord t 5 (by decide)).truncate 8) ∗
    ((fsp + 0xfe6#64) ↦₈ (coinWord t 6 (by decide)).truncate 8) ∗
    ((fsp + 0xfe7#64) ↦₈ (coinWord t 7 (by decide)).truncate 8) ∗
    ((fsp + 0xfe8#64) ↦₈ (coinWord t 8 (by decide)).truncate 8) ∗
    ((fsp + 0xfe9#64) ↦₈ (coinWord t 9 (by decide)).truncate 8) ∗
    ((fsp + 0xfea#64) ↦₈ (coinWord t 10 (by decide)).truncate 8) ∗
    ((fsp + 0xfeb#64) ↦₈ (coinWord t 11 (by decide)).truncate 8) ∗
    ((fsp + 0xfec#64) ↦₈ (coinWord t 12 (by decide)).truncate 8) ∗
    ((fsp + 0xfed#64) ↦₈ (coinWord t 13 (by decide)).truncate 8) ∗
    ((fsp + 0xfee#64) ↦₈ (coinWord t 14 (by decide)).truncate 8) ∗
    ((fsp + 0xfef#64) ↦₈ (coinWord t 15 (by decide)).truncate 8) ∗
    ((fsp + 0xff0#64) ↦₈ (coinWord t 16 (by decide)).truncate 8) ∗
    ((fsp + 0xff1#64) ↦₈ (coinWord t 17 (by decide)).truncate 8) ∗
    ((fsp + 0xff2#64) ↦₈ (coinWord t 18 (by decide)).truncate 8) ∗
    ((fsp + 0xff3#64) ↦₈ (coinWord t 19 (by decide)).truncate 8) ∗
    ((fsp + 0xff4#64) ↦₈ (coinWord t 20 (by decide)).truncate 8) ∗
    ((fsp + 0xff5#64) ↦₈ (coinWord t 21 (by decide)).truncate 8) ∗
    ((fsp + 0xff6#64) ↦₈ (coinWord t 22 (by decide)).truncate 8) ∗
    ((fsp + 0xff7#64) ↦₈ (coinWord t 23 (by decide)).truncate 8) ∗
    ((fsp + 0xff8#64) ↦₈ (coinWord t 24 (by decide)).truncate 8) ∗
    ((fsp + 0xff9#64) ↦₈ (coinWord t 25 (by decide)).truncate 8) ∗
    ((fsp + 0xffa#64) ↦₈ (coinWord t 26 (by decide)).truncate 8) ∗
    ((fsp + 0xffb#64) ↦₈ (coinWord t 27 (by decide)).truncate 8) ∗
    ((fsp + 0xffc#64) ↦₈ (coinWord t 28 (by decide)).truncate 8) ∗
    ((fsp + 0xffd#64) ↦₈ (coinWord t 29 (by decide)).truncate 8) ∗
    ((fsp + 0xffe#64) ↦₈ (coinWord t 30 (by decide)).truncate 8) ∗
    ((fsp + 0xfff#64) ↦₈ (coinWord t 31 (by decide)).truncate 8) =
      ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) := by
  simp only [coinWord_truncate8]
  conv_rhs => rw [vec32_chunks4_eq (initiateKemCoins t)]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  dsimp only [List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  simp only [← pack4_bytes_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem p32_4 {p0 p1 p2 p3 : BitVec 64} {w0 w1 w2 w3 : BitVec 32} {R R' : SepProp}
    (h : R ⊢ R') :
    (p0 ↦₃₂ w0) ∗ (p1 ↦₃₂ w1) ∗ (p2 ↦₃₂ w2) ∗ (p3 ↦₃₂ w3) ∗ R ⊢
      memRegion p0 4 ∗ memRegion p1 4 ∗ memRegion p2 4 ∗ memRegion p3 4 ∗ R' :=
  sepConj_mono (pointsTo32_entails_memRegion p0 w0)
    (sepConj_mono (pointsTo32_entails_memRegion p1 w1)
      (sepConj_mono (pointsTo32_entails_memRegion p2 w2)
        (sepConj_mono (pointsTo32_entails_memRegion p3 w3) h)))

private theorem mem4_elim_bytes {prog : Program} {ret : BitVec 64} {s : State}
    {p : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ u0 u1 u2 u3 : BitVec 8,
      SepWPp prog ret s
        (B ∗ ((p ↦₈ u0) ∗ ((p + 1#64) ↦₈ u1) ∗ ((p + 2#64) ↦₈ u2) ∗ ((p + 3#64) ↦₈ u3) ∗ R))
        Q Qp oom) :
    SepWPp prog ret s ((memRegion p 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, memRegion4_split1 p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
    sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 =>
      sepWPp_conseq_oom (by sep_frame) (h u3 u2 u1 u0)

private theorem scratch96_collapse (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
      w22 w23 : BitVec 32) :
    memRegion fsp 8 ∗
      ((fsp + 0x68#64) ↦₃₂ w0) ∗ ((fsp + 0x60#64) ↦₃₂ w1) ∗
      ((fsp + 0x5c#64) ↦₃₂ w2) ∗ ((fsp + 0x58#64) ↦₃₂ w3) ∗
      ((fsp + 0x54#64) ↦₃₂ w4) ∗ ((fsp + 0x50#64) ↦₃₂ w5) ∗
      ((fsp + 0x4c#64) ↦₃₂ w6) ∗ ((fsp + 0x48#64) ↦₃₂ w7) ∗
      ((fsp + 0x44#64) ↦₃₂ w8) ∗ ((fsp + 0x40#64) ↦₃₂ w9) ∗
      ((fsp + 0x3c#64) ↦₃₂ w10) ∗ ((fsp + 0x38#64) ↦₃₂ w11) ∗
      ((fsp + 0x34#64) ↦₃₂ w12) ∗ ((fsp + 0x30#64) ↦₃₂ w13) ∗
      ((fsp + 0x2c#64) ↦₃₂ w14) ∗ ((fsp + 0x28#64) ↦₃₂ w15) ∗
      ((fsp + 0x24#64) ↦₃₂ w16) ∗ ((fsp + 0x20#64) ↦₃₂ w17) ∗
      ((fsp + 0x1c#64) ↦₃₂ w18) ∗ ((fsp + 0x18#64) ↦₃₂ w19) ∗
      ((fsp + 0x14#64) ↦₃₂ w20) ∗ ((fsp + 0x10#64) ↦₃₂ w21) ∗
      ((fsp + 0x0c#64) ↦₃₂ w22) ∗ ((fsp + 0x08#64) ↦₃₂ w23) ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ⊢
      memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (Entails.refl _)))))))) ?_
  have hlow :
      memRegion fsp 8 ∗ memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x5c#64) 4 = memRegion fsp 0x60 := by
    rw [memRegion_merge_at (fsp + 0x58#64) 4 4 (fsp + 0x5c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x54#64) 4 8 (fsp + 0x58#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x50#64) 4 12 (fsp + 0x54#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x4c#64) 4 16 (fsp + 0x50#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x48#64) 4 20 (fsp + 0x4c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x44#64) 4 24 (fsp + 0x48#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x40#64) 4 28 (fsp + 0x44#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x3c#64) 4 32 (fsp + 0x40#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x38#64) 4 36 (fsp + 0x3c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x34#64) 4 40 (fsp + 0x38#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x30#64) 4 44 (fsp + 0x34#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x2c#64) 4 48 (fsp + 0x30#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x28#64) 4 52 (fsp + 0x2c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x24#64) 4 56 (fsp + 0x28#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x20#64) 4 60 (fsp + 0x24#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1c#64) 4 64 (fsp + 0x20#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x18#64) 4 68 (fsp + 0x1c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x14#64) 4 72 (fsp + 0x18#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x10#64) 4 76 (fsp + 0x14#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x0c#64) 4 80 (fsp + 0x10#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x08#64) 4 84 (fsp + 0x0c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at fsp 8 88 (fsp + 0x08#64) (by clear * -; bv_omega) (by decide)]
  have h60 := memRegion_merge_at (fsp + 0x60#64) 4 4 (fsp + 0x64#64) (by clear * -; bv_omega) (by decide)
  have h68 := memRegion_merge_at (fsp + 0x68#64) 4 4 (fsp + 0x6c#64) (by clear * -; bv_omega) (by decide)
  rw [← hlow, ← h60, ← h68]; sep_frame

set_option maxHeartbeats 1600000 in
theorem kem_encaps_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 se : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiate img W s0 se 0xee8) (htr : se.trace = s0.trace)
    (hx20 : se.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : se.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : se.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : se.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : se.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : se.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hx27 : se.readReg64 (.gpr 27#5) = (coinWord (padCoins x.coins) 28 (by decide)).setWidth 64)
    (hx28 : se.readReg64 (.gpr 28#5) = (coinWord (padCoins x.coins) 29 (by decide)).setWidth 64)
    (hx24 : se.readReg64 (.gpr 24#5) = (coinWord (padCoins x.coins) 30 (by decide)).setWidth 64)
    (hnext : ∀ sf : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiate img W s0 sf 0xfb4 → sf.trace = s0.trace →
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
          memRegion (fsp + 0x1c40#64) 32 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProg img W) (s0.readReg64 .lr) se
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
        A.pool ∗ stackAt fsp cliCoinsFillStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗ ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  obtain ⟨_, _, _, _, _, _, hkpk_eq, _⟩ := bundleEOf_props hs3.bundleEq
  have hsub_cf : cliCoinsFillStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_le64 := stk_sub_le_2pow64 hstk64
  have hfe0_split : memRegion (fsp + 0xfe0#64) 32 =
      memRegion (fsp + 0xfe0#64) 4 ∗ memRegion (fsp + 0xfe4#64) 4 ∗
      memRegion (fsp + 0xfe8#64) 4 ∗ memRegion (fsp + 0xfec#64) 4 ∗
      memRegion (fsp + 0xff0#64) 4 ∗ memRegion (fsp + 0xff4#64) 4 ∗
      memRegion (fsp + 0xff8#64) 4 ∗ memRegion (fsp + 0xffc#64) 4 ∗ emp := by
    rw [sepConj_emp,
        memRegion_merge_at (fsp + 0xff8#64) 4 4 (fsp + 0xffc#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff4#64) 4 8 (fsp + 0xff8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff0#64) 4 12 (fsp + 0xff4#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfec#64) 4 16 (fsp + 0xff0#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe8#64) 4 20 (fsp + 0xfec#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe4#64) 4 24 (fsp + 0xfe8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe0#64) 4 28 (fsp + 0xfe4#64) (by clear * -; bv_omega) (by decide)]
  refine sepWPp_conseq_oom
    (sep_replace (Entails.of_eq hfe0_split) (by dsimp only [fsp]; sep_frame) (Entails.refl _)) ?_
  refine mem4_elim_bytes fun u0 u1 u2 u3 =>
    mem4_elim_bytes fun u4 u5 u6 u7 =>
    mem4_elim_bytes fun u8 u9 u10 u11 =>
    mem4_elim_bytes fun u12 u13 u14 u15 =>
    mem4_elim_bytes fun u16 u17 u18 u19 =>
    mem4_elim_bytes fun u20 u21 u22 u23 =>
    mem4_elim_bytes fun u24 u25 u26 u27 =>
    mem4_elim_bytes fun u28 u29 u30 u31 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, emp_sepConj, sepConj_assoc]
  obtain ⟨halign_e, _, hfsp_e⟩ := hctrl.step_ctx fsp
  refine' s3_block_in hh 0xf50
    (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xee8 104
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx25 hx22 hx26 hx23 hx27 hx28 hx24
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    refine ⟨by simp only [arm64_norm, wp_norm], Entails.refl _, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_goal, by wp_norm_goal,
      by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
  · intro sm1 htr1 hctrl1 ⟨hx0_1, hx1_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
    obtain ⟨halign_1, _, hfsp_1⟩ := hctrl1.step_ctx fsp
    refine' s3_block_to_call hh
      (initEntry img W + bv% (ls_rel%
        "libsignal_cli_handshake::initiate" "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      0xfb4 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl1 ?_ ?_; rotate_left 1
    · have hpc := hctrl1.pc; have hrun := hctrl1.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xf50 100
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hctrl1.sp] at *
      try simp only [arm64_norm, wp_norm] at hx0_1 hx1_1 hx20_1 hx21_1
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx0_1, arm64_norm, wp_norm], by simp only [hx1_1, arm64_norm, wp_norm],
         by wp_norm_goal,
         by simp only [hx20_1, arm64_norm, wp_norm], by simp only [hx21_1, arm64_norm, wp_norm]⟩
    · intro sm2 hc2 hp2 hl2 ht2 ⟨hx0_2, hx1_2, hx8_2, hx20_2, hx21_2⟩
      rw [hctrl1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
      have htr2 : sm2.trace = s0.trace := ht2.trans (htr1.trans htr)
      have hstk_merge :
          stackAt fsp cliCoinsFillStack ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
              (stk - cliInitiateFrame - cliCoinsFillStack) =
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
            (pqxdhEntryStack - pqxdhHookStack) ∗
          stackAt fsp pqxdhHookStack := by
        rw [sepConj_comm (stackAt fsp cliCoinsFillStack),
            ← stackAt_sub_split_init fsp hsub_cf hstk_le64,
            stackAt_sub_split_init fsp hsub_pq hstk_le64,
            stackAt_sub_split_init fsp (by decide : pqxdhHookStack ≤ pqxdhEntryStack) (by decide),
            ← sepConj_assoc]
      have hout1600 :
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
            memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ⊢
            memRegion (fsp + 0x1600#64) 1600 ∗ memRegion (fsp + 0x1c40#64) 32 := by
        refine Entails.trans (sepConj_mono_left (pointsTo32_entails_memRegion _ _)) ?_
        rw [← memRegion_merge_at (fsp + 0x1618#64) 1576 32 (fsp + 0x1c40#64) (by clear * -; bv_omega) (by decide),
            ← sepConj_assoc, ← sepConj_assoc,
            memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by clear * -; bv_omega) (by decide),
            memRegion_merge_at (fsp + 0x1600#64) (4 + 20) 1576 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide)]
        exact Entails.refl _
      let g : KyberEncapsCall :=
        { pkPtr := fsp + 0x9c0#64
          pk1568 := toU8 be.kpkPub.toList
          coinsPtr := fsp + 0xfe0#64
          coins32 := toU8 (initiateKemCoins t).toList
          outPtr := fsp + 0x1600#64 }
      obtain ⟨h_some, h_out⟩ := kemEncaps_out_eq X ⟨W.C, W.Q⟩ be t
      have hpk_bv : bytesToBv8 g.pk1568 = x.bundle.kpk := by
        dsimp only [g]; rw [bytesToBv8_toU8_eq, hkpk_eq]
      have hcoins_bv : bytesToBv8 g.coins32 = (initiateKemCoins t).toList :=
        bytesToBv8_toU8_eq _
      have hpk_len : g.pk1568.length = 1568 := by
        dsimp only [g, toU8]; simp [be.kpkPub.toList_length]
      have hcoins_len : g.coins32.length = 32 := by
        dsimp only [g, toU8]; simp [(initiateKemCoins t).toList_length]
      have hcollapse_pre := scratch96_collapse fsp
        (coinWord t 0 (by decide)) (coinWord t 1 (by decide)) (coinWord t 2 (by decide))
        (coinWord t 3 (by decide)) (coinWord t 4 (by decide)) (coinWord t 5 (by decide))
        (coinWord t 6 (by decide)) (coinWord t 7 (by decide)) (coinWord t 8 (by decide))
        (coinWord t 9 (by decide)) (coinWord t 10 (by decide)) (coinWord t 11 (by decide))
        (coinWord t 12 (by decide)) (coinWord t 13 (by decide)) (coinWord t 14 (by decide))
        (coinWord t 15 (by decide)) (coinWord t 16 (by decide)) (coinWord t 17 (by decide))
        (coinWord t 18 (by decide)) (coinWord t 19 (by decide)) (coinWord t 20 (by decide))
        (coinWord t 21 (by decide)) (coinWord t 22 (by decide)) (coinWord t 23 (by decide))
      refine s3_call hh (kyberEncaps_ok_at_init img W X) g _
        hc2 htr2 hp2 hl2 hpanic
        (by
          simp only [kyberEncapsStubSpec, hpk_bv, hcoins_bv, hc2.sp, sepConj_assoc]
          dsimp only [g, fsp] at hx0_2 hx1_2 hx8_2 ⊢
          refine Entails.pure_right ⟨hx0_2, hx1_2, hx8_2, hpk_len, hcoins_len, h_some⟩ ?_
          have hkem := kemCoins32_pointsTo_eq (s0.sp - BitVec.ofNat 64 cliInitiateFrame) t
          dsimp only [t, fsp] at hkem hcollapse_pre hout1600 hstk_merge ⊢
          refine sep_replace hcollapse_pre (by sep_frame) ?_
          refine sep_replace hout1600 (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hkem) (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hstk_merge) (by sep_frame) ?_
          simp only [sepConj_assoc]
          sep_frame) ?_ ?_ ?_ ?_
      · intro _ _ h; simp [kyberEncapsStubSpec, Spec.onPanic] at h
      · intro _ _ _ h; simp [kyberEncapsStubSpec, Spec.onExit] at h
      · intro _ _ h; simp [kyberEncapsStubSpec, Spec.onOom] at h
      · intro sf _ _ _ hcs_f _ hof
        simp only [kyberEncapsStubSpec, hpk_bv, hcoins_bv, h_out, hc2.sp, sepConj_assoc]
        refine sepWPp_pure_elim_oom fun htr_f => ?_
        let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
        let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
        have hout_split :
            ((fsp + 0x1600#64) ↦ₛ (ct.toList ++ ss.toList)) =
              ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) := by
          rw [pointsToBytes_append, ct.toList_length]
          simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        have hstk_back :
            memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                (pqxdhEntryStack - pqxdhHookStack) ∗ stackAt fsp pqxdhHookStack =
              stackAt fsp pqxdhEntryStack :=
          (stackAt_sub_split_init fsp (by decide : pqxdhHookStack ≤ pqxdhEntryStack) (by decide)).symm
        refine sepWPp_conseq_oom ?_
          (hnext sf (hof htr_f) (htr_f.trans htr2)
            (hcs_f.2.1.trans hx20_2) (hcs_f.2.2.1.trans hx21_2))
        dsimp only [g, fsp, ct, ss, t] at h_out hout_split hstk_back ⊢
        rw [h_out, hout_split]
        exact sep_replace (Entails.of_eq hstk_back) (by sep_frame) (by sep_frame)

/-! ## `CliExternsOk` Generalization (`kem_encaps_ok_ext` with `byVal` `memRegion (fsp + 0xfe0#64) 32`) -/

private abbrev s3ProgExt (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt img.base (cliExternsWith ext)

private abbrev s3EntryExt (img : Obj.Image) (ext : String → Option (State → State)) : BitVec 64 :=
  (s3ProgExt img ext).fnAddr cliInitiateName

private abbrev s3PcExt (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    BitVec 64 :=
  s3EntryExt img ext + BitVec.ofNat 64 k

/-- Reducible control-state invariant at relative offset `k` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)`. -/
abbrev s3KemCtrlExt (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop :=
  let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
  s.pc = prog.fnAddr cliInitiateName + BitVec.ofNat 64 k ∧
  s.status = .Running ∧
  s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
  s.readReg64 .fp = s0.sp - 0x60#64 ∧
  s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
  s.fs.files = s0.fs.files ∧
  ImgCallInv img s ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s0.spAligned = true

private structure S3Ctrl (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = s3PcExt img ext k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  files0 : s.fs.files = s0.fs.files
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

private theorem S3Ctrl.of_prop {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : s3KemCtrlExt img ext s0 s k) : S3Ctrl img ext s0 s k := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem S3Ctrl.to_prop {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s3KemCtrlExt img ext s0 s k := by
  exact ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

private theorem S3Ctrl.spAligned_cur {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

private theorem S3Ctrl.step_ctx {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧
      s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧
      fsp = s.sp := by
  have ha := h.spAligned_cur; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

private theorem s3_withPanics_cliExternsWith (ext : String → Option (State → State)) :
    Rust.withPanics (cliExternsWith ext) = cliExternsWith ext :=
  withPanics_withCliPanics ext

private theorem s3_quietEv_false_of_isFsChange (e : TraceEvent)
    (h : e.isFsChange = true) : ¬ QuietEv e := by
  cases e with
  | writeByte st _ => cases st <;> simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢
  | _ => simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢

private theorem s3_externAt_fsTraced {prog : Program}
    (hX : ∀ n f, prog.externs n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hO : ∀ n f, prog.overrides n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    {pc : BitVec 64} {f : State → State} (h : prog.externAt? pc = some f) :
    HookFsTraced (fun e => e.isFsChange = true) f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, _⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno; split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, _⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno; split at hno
    · exact hO n f hno
    · cases hno

private theorem rebase_traceFsSound (C : Program) (b : BitVec 64) (hsvc : C.svc = execSyscall)
    {P0 : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext) :
    TraceFsSound (C.rebase b (Rust.withPanics (cliExternsWith ext))) := by
  refine TraceFsSound.of_isFs s3_quietEv_false_of_isFsChange fun s s' hst => ?_
  refine hst.files_eq_of_noFs (fun _ h => h)
    (fun _ _ h => s3_externAt_fsTraced ?_ (fun _ _ hn => by cases C; cases hn) h) (by cases C; exact hsvc)
  intro name f hf; cases C; change (Rust.withPanics (cliExternsWith ext)) name = some f at hf
  rw [s3_withPanics_cliExternsWith] at hf
  simp only [cliExternsWith, withCliPanics] at hf
  cases hpan : isCliPanicSymbol name
  · rw [hpan] at hf; exact hOk.fsTraced name f hf
  · rw [hpan] at hf; cases hf; exact fun _ => ⟨[], by simp [Rust.panicked], fun _ => rfl⟩

private theorem s3_traceFsSound (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    TraceFsSound (s3ProgExt img ext) := by
  exact rebase_traceFsSound libsignalSessionCode img.base rfl hOk

private theorem S3Ctrl.of_call {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    {s0 s sm : State} {k_in k_out : Nat}
    (h : S3Ctrl img ext s0 s k_in) (hsteps : Steps (s3ProgExt img ext) s sm)
    (hpcm : sm.pc = s3PcExt img ext k_out) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp) (hcsm : CalleeSavedPreserved s sm) (htrm : sm.trace = s.trace) :
    S3Ctrl img ext s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps
      (evs := []) (by simpa using htrm) NoFsEv.nil
  exact ⟨hpcm, hrunm, hspm.trans h.sp, hfp.trans h.fp, hx19.trans h.x19,
    hfs_eq.trans h.files0, h.inv.of_steps hsteps, hvregs.trans h.vregs, h.spAligned⟩

private theorem s3_block_in_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (hwp : SepWP (s3ProgExt img ext) (s3PcExt img ext k_out) s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧ Φ sm))
    (hcont : ∀ sm : State,
      sm.trace = s.trace →
      S3Ctrl img ext s0 sm k_out →
      Φ sm →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  intro R hm hL
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps
        (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' : S3Ctrl img ext s0 sm k_out :=
      { pc := hpcm
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_steps hsteps
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm htrm hctrl' hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_pc_sub_entry (a b : BitVec 64) :
    a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

private theorem s3_block_to_call_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (hwp : SepWP (s3ProgExt img ext) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = s3PcExt img ext k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = s3PcExt img ext k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  intro R hm hL
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps
        (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' : S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) :=
      { pc := s3_pc_sub_entry sm.pc (s3EntryExt img ext)
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_steps hsteps
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_call_ext {α : Type} {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (s3ProgExt img ext) callee spec)
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = s3PcExt img ext k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (sm.trace = s.trace → S3Ctrl img ext s0 sm k_out) →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine sepWPp_conseq_oom hpre ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre g s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F ∗ R') s hpc hctrl.run hm_pre
      (S3Ctrl.spAligned_cur hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hctrl.inv.of_steps hsteps)
        (S3Ctrl.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic g s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by
      simpa only [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan,
      hpanic sm _ (initPanicPost_of_allocFailed _ halloc0)⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

private theorem s3_hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)}
    {sym : String} {spec : Spec α}
    (hnp : E2E.isImagePanicSymbol sym = false) (h : HookSat ext sym spec) :
    HookSat (cliExternsWith ext) sym spec := by
  cases hf : ext sym with
  | none => exact (HookSat_none hf h).elim
  | some f =>
    exact HookSat_of_HookOk ((withCliPanics_of_isImagePanicSymbol_false ext hnp).trans hf)
      ((HookSat_iff_of_eq hf).mp h)

/-- `HookSat` for `libcrux_ml_kem::mlkem1024::kyber::encapsulate` with `.keepsFs` on
`cliExternsWith ext` directly from `CliExternsOk`. -/
theorem kemEncaps_stub_ok_of_cliExternsOk {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    HookSat (cliExternsWith ext) E2E.kemEncapsName (CliExt.kemEncapsSpec P0.Q).keepsFs := by
  cases hf : ext E2E.kemEncapsName with
  | none => exact (HookSat_none hf hOk.kemEncaps).elim
  | some f =>
    have hok := (HookSat_iff_of_eq hf).mp hOk.kemEncaps
    have hnio : E2E.kemEncapsName ∉ CliExt.ioNames := by decide +kernel
    exact s3_hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, E2E.kemEncapsName])
      (HookSat_of_HookOk hf (hok.keepsFs (hOk.fsKept E2E.kemEncapsName f hf hnio)))

/-- `subroutine_ok` for `libcrux_ml_kem::mlkem1024::kyber::encapsulate` at `initiate`'s relative
call target under `CliExternsOk P0 A ext`. -/
theorem kemEncaps_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      (CliExt.kemEncapsSpec P0.Q) := by
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := E2E.kemEncapsName)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    (stub := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")
    (by simp [Rust.isPanicSymbol, E2E.kemEncapsName])
    (s3_hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, E2E.kemEncapsName])
      hOk.kemEncaps)

/-- `byVal` randomness handoff (`memRegion (fsp + 0xfe0#64) 32` + `0x600` → `1568` B) from
`kem_encaps_ok_ext` to `DeriveKeysA1.derive_keys_a1_ok_ext`. -/
theorem kemEncaps_byVal_handoff_to_deriveKeysA1 (fsp : BitVec 64) :
    memRegion (fsp + 0xfe0#64) 32 ∗ memRegion (fsp + 0x1000#64) 0x600 ⊢
      memRegion (fsp + 0xfe0#64) 1568 := by
  rw [memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64)
    (by bv_omega) (by decide)]
  exact Entails.refl _

attribute [local irreducible] libsignalSessionCode Program.fnOff

set_option maxHeartbeats 1200000 in
/-- Generalized Stage 3 KEM seed packing & `kyber::encapsulate` (`+0x0ee8 → +0x0fb4`) under
`CliExternsOk P0 A ext`, handing off `memRegion (fsp + 0xfe0#64) 32` (`byVal` randomness). -/
theorem kem_encaps_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 se : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbundle : bundleEOf? x.bundle = some be)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl_in : s3KemCtrlExt img ext s0 se 0xee8) (htr : se.trace = s0.trace)
    (hx20 : se.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : se.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : se.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : se.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : se.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : se.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hx27 : se.readReg64 (.gpr 27#5) = (coinWord (padCoins x.coins) 28 (by decide)).setWidth 64)
    (hx28 : se.readReg64 (.gpr 28#5) = (coinWord (padCoins x.coins) 29 (by decide)).setWidth 64)
    (hx24 : se.readReg64 (.gpr 24#5) = (coinWord (padCoins x.coins) 30 (by decide)).setWidth 64)
    (hnext : ∀ sf : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
      s3KemCtrlExt img ext s0 sf 0xfb4 → sf.trace = s0.trace →
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) sf
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
          memRegion (fsp + 0x1c40#64) 32 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) se
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
        A.pool ∗ stackAt fsp cliCoinsFillStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗ ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  have hctrl : S3Ctrl img ext s0 se 0xee8 := S3Ctrl.of_prop hctrl_in
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  obtain ⟨_, _, _, _, _, _, hkpk_eq, _⟩ := bundleEOf_props hbundle
  have hpk_list : be.kpkPub.toList = x.bundle.kpk := by
    simpa [bytesToBv8_toU8_eq] using hkpk_eq
  have hsub_cf : cliCoinsFillStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_le64 := stk_sub_le_2pow64 hstk64
  have hfe0_split : memRegion (fsp + 0xfe0#64) 32 =
      memRegion (fsp + 0xfe0#64) 4 ∗ memRegion (fsp + 0xfe4#64) 4 ∗
      memRegion (fsp + 0xfe8#64) 4 ∗ memRegion (fsp + 0xfec#64) 4 ∗
      memRegion (fsp + 0xff0#64) 4 ∗ memRegion (fsp + 0xff4#64) 4 ∗
      memRegion (fsp + 0xff8#64) 4 ∗ memRegion (fsp + 0xffc#64) 4 ∗ emp := by
    rw [sepConj_emp,
        memRegion_merge_at (fsp + 0xff8#64) 4 4 (fsp + 0xffc#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff4#64) 4 8 (fsp + 0xff8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff0#64) 4 12 (fsp + 0xff4#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfec#64) 4 16 (fsp + 0xff0#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe8#64) 4 20 (fsp + 0xfec#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe4#64) 4 24 (fsp + 0xfe8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe0#64) 4 28 (fsp + 0xfe4#64) (by clear * -; bv_omega) (by decide)]
  refine sepWPp_conseq_oom
    (sep_replace (Entails.of_eq hfe0_split) (by dsimp only [fsp]; sep_frame) (Entails.refl _)) ?_
  refine mem4_elim_bytes fun u0 u1 u2 u3 =>
    mem4_elim_bytes fun u4 u5 u6 u7 =>
    mem4_elim_bytes fun u8 u9 u10 u11 =>
    mem4_elim_bytes fun u12 u13 u14 u15 =>
    mem4_elim_bytes fun u16 u17 u18 u19 =>
    mem4_elim_bytes fun u20 u21 u22 u23 =>
    mem4_elim_bytes fun u24 u25 u26 u27 =>
    mem4_elim_bytes fun u28 u29 u30 u31 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, emp_sepConj, sepConj_assoc]
  obtain ⟨halign_e, _, hfsp_e⟩ := hctrl.step_ctx fsp
  refine' s3_block_in_ext hOk 0xf50
    (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xee8 104
    dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx25 hx22 hx26 hx23 hx27 hx28 hx24
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    refine ⟨by simp only [arm64_norm, wp_norm], Entails.refl _, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_goal, by wp_norm_goal,
      by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
  · intro sm1 htr1 hctrl1 ⟨hx0_1, hx1_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *
    obtain ⟨halign_1, _, hfsp_1⟩ := hctrl1.step_ctx fsp
    refine' s3_block_to_call_ext hOk
      (s3EntryExt img ext + bv% (ls_rel%
        "libsignal_cli_handshake::initiate" "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      0xfb4 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl1 ?_ ?_; rotate_left 1
    · have hpc := hctrl1.pc; have hrun := hctrl1.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xf50 100
      dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hctrl1.sp] at *
      try simp only [arm64_norm, wp_norm] at hx0_1 hx1_1 hx20_1 hx21_1
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx0_1, arm64_norm, wp_norm], by simp only [hx1_1, arm64_norm, wp_norm],
         by wp_norm_goal,
         by simp only [hx20_1, arm64_norm, wp_norm], by simp only [hx21_1, arm64_norm, wp_norm]⟩
    · intro sm2 hc2 hp2 hl2 ht2 ⟨hx0_2, hx1_2, hx8_2, hx20_2, hx21_2⟩
      rw [hctrl1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
      have htr2 : sm2.trace = s0.trace := ht2.trans (htr1.trans htr)
      have hstk_merge :
          stackAt fsp cliCoinsFillStack ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
              (stk - cliInitiateFrame - cliCoinsFillStack) =
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
            (pqxdhEntryStack - extHookStack) ∗
          stackAt fsp extHookStack := by
        rw [sepConj_comm (stackAt fsp cliCoinsFillStack),
            ← stackAt_sub_split_init fsp hsub_cf hstk_le64,
            stackAt_sub_split_init fsp hsub_pq hstk_le64,
            stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide),
            ← sepConj_assoc]
      have hout1600 :
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
            memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ⊢
            memRegion (fsp + 0x1600#64) 1600 ∗ memRegion (fsp + 0x1c40#64) 32 := by
        refine Entails.trans (sepConj_mono_left (pointsTo32_entails_memRegion _ _)) ?_
        rw [← memRegion_merge_at (fsp + 0x1618#64) 1576 32 (fsp + 0x1c40#64) (by clear * -; bv_omega) (by decide),
            ← sepConj_assoc, ← sepConj_assoc,
            memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by clear * -; bv_omega) (by decide),
            memRegion_merge_at (fsp + 0x1600#64) (4 + 20) 1576 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide)]
        exact Entails.refl _
      have hcollapse_pre := scratch96_collapse fsp
        (coinWord t 0 (by decide)) (coinWord t 1 (by decide)) (coinWord t 2 (by decide))
        (coinWord t 3 (by decide)) (coinWord t 4 (by decide)) (coinWord t 5 (by decide))
        (coinWord t 6 (by decide)) (coinWord t 7 (by decide)) (coinWord t 8 (by decide))
        (coinWord t 9 (by decide)) (coinWord t 10 (by decide)) (coinWord t 11 (by decide))
        (coinWord t 12 (by decide)) (coinWord t 13 (by decide)) (coinWord t 14 (by decide))
        (coinWord t 15 (by decide)) (coinWord t 16 (by decide)) (coinWord t 17 (by decide))
        (coinWord t 18 (by decide)) (coinWord t 19 (by decide)) (coinWord t 20 (by decide))
        (coinWord t 21 (by decide)) (coinWord t 22 (by decide)) (coinWord t 23 (by decide))
      let g := (fsp + 0x9c0#64, be.kpkPub, fsp + 0xfe0#64, initiateKemCoins t, fsp + 0x1600#64)
      refine s3_call_ext hOk (kemEncaps_ok_at_init_ext img hOk) g _
        hc2 htr2 hp2 hl2 hpanic
        (by
          simp only [CliExt.kemEncapsSpec, CliExt.withStack, g, hpk_list, hc2.sp, sepConj_assoc]
          dsimp only [fsp] at hx0_2 hx1_2 hx8_2 ⊢
          refine Entails.pure_right ⟨hx0_2, hx1_2, hx8_2⟩ ?_
          have hkem := kemCoins32_pointsTo_eq (s0.sp - BitVec.ofNat 64 cliInitiateFrame) t
          dsimp only [t, fsp] at hkem hcollapse_pre hout1600 hstk_merge ⊢
          refine sep_replace hcollapse_pre (by sep_frame) ?_
          refine sep_replace hout1600 (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hkem) (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hstk_merge) (by sep_frame) ?_
          simp only [sepConj_assoc]
          sep_frame) ?_ ?_ ?_ ?_
      · intro _ _ h; simp [CliExt.kemEncapsSpec, CliExt.withStack] at h
      · intro _ _ _ h; simp [CliExt.kemEncapsSpec, CliExt.withStack] at h
      · intro _ _ h; simp [CliExt.kemEncapsSpec, CliExt.withStack] at h
      · intro sf _ _ _ hcs_f _ hof
        simp only [CliExt.kemEncapsSpec, CliExt.withStack, g, hpk_list, hc2.sp, sepConj_assoc]
        refine sepWPp_pure_elim_oom fun htr_f => ?_
        have h1c20 : (fsp + 0x1600#64) + 0x620#64 = fsp + 0x1c20#64 := by clear * -; bv_omega
        have hstk_back :
            memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                (pqxdhEntryStack - extHookStack) ∗ stackAt fsp extHookStack =
              stackAt fsp pqxdhEntryStack :=
          (stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)).symm
        refine sepWPp_conseq_oom ?_
          (hnext sf (hof htr_f).to_prop (htr_f.trans htr2)
            (hcs_f.2.1.trans hx20_2) (hcs_f.2.2.1.trans hx21_2))
        dsimp only [fsp, t] at h1c20 hstk_back ⊢
        rw [h1c20]
        exact sep_replace (Entails.of_eq hstk_back) (by sep_frame) (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
