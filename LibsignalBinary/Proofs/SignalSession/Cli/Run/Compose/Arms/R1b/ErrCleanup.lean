/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Shared OOM Stubs and Error Cleanup Chain for Arm `R1b` (`R+0x2a60 .. R+0x2c7c`, `R+0x2d44 .. R+0x2d7c`)

Reusable `SepWPp` continuations for the OOM panic stubs (`alloc::raw_vec::handle_error`) and
error/reject cleanup tail of `run_hop_init2_ok` (Arm `R1b`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

gen_decodes CryptoVerification.libsignalSessionCode_tree r1bDecErr
  [(ls_off% "libsignal_cli::run" + 0x2a60) → (ls_off% "libsignal_cli::run" + 0x2c7c),
   (ls_off% "libsignal_cli::run" + 0x2d44) → (ls_off% "libsignal_cli::run" + 0x2d80)]

theorem r1b_bind_state {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s' : State} {P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sm : State, sm = s' → ImgCallInv img sm → SepWPp prog ret sm P' Q Qp oom) :
    ImgCallInv img s' → SepWPp prog ret s' P' Q Qp oom :=
  fun hinv => h s' rfl hinv

theorem r1b_fsp_align {s0 s : State} (hsp : s.sp = runFsp s0) (hsp0 : s0.spAligned = true) :
    runFsp s0 &&& 15#64 = 0#64 :=
  hsp ▸ eq_of_beq (r1b_spAligned_of_fsp hsp hsp0)

theorem r1b_allocFailedIn_mono {s0 s1 s2 : State}
    (ha : allocFailedIn s0 s1) (hp : s1.trace <+: s2.trace) :
    allocFailedIn s0 s2 := by
  unfold allocFailedIn at ha ⊢
  rcases hp with ⟨extTr, htr2⟩
  rw [← htr2, List.drop_append]
  exact List.mem_append_left _ ha

/-! ## `ownedBytes` / `vecU8` Bridges, `memRegion` Packing, and `r1b_SpePayload` -/

theorem r1b_ownedBytes_to_vecU8 (A : RustAlloc) (v cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len) ∗
      ownedBytes A cap ptr len bs) ⊢
      vecU8 A v bs := by
  dsimp only [vecU8, vecU8At, vecHeader, ownedBytes]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  conv => lhs; rw [sepConj_comm ((v + 16#64) ↦₆₄ len), sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨rfl, hle, hlt, hne⟩
  conv => rhs; rw [sepConj_comm ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length), sepConj_assoc]
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)

theorem r1b_cell64_cons {a : BitVec 64} (v : BitVec 64) {n : Nat} (hn : n < 2 ^ 64 - 8) :
    ((a ↦₆₄ v) ∗ memRegion (a + 8#64) n) ⊢ memRegion a (n + 8) :=
  ProofLib.memRegion_cons a v (n := n + 8) (by omega) (by omega)

theorem r1b_cells2_to_region16 (a : BitVec 64) (v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 :=
  Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _))
    (r1b_cell64_cons v0 (by decide))

theorem r1b_cells2_region8_to_24 (a : BitVec 64) (v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  have h16 : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
  refine Entails.trans (sepConj_mono_right (by rw [h16]; exact r1b_cell64_cons v1 (by decide))) ?_
  exact r1b_cell64_cons v0 (by decide)

theorem r1b_cell8_to_region (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 := by
  rw [ProofLib.memRegion_one a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem r1b_cell32_to_region (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [ProofLib.memRegion_four a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem r1b_region16_to_cells (a : BitVec 64) :
    memRegion a 16 = ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
      (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, ProofLib.memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_left]
  congr 1; funext v0
  rw [sepExists_sepConj_right]

theorem r1b_region48_to_cells (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
  have h32 : memRegion (a + 32#64) 16 = ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
    have ha : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
    simpa [ha] using r1b_region16_to_cells (a + 32#64)
  have h16 : memRegion (a + 16#64) 16 = ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) := by
    have ha : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
    simpa [ha] using r1b_region16_to_cells (a + 16#64)
  have hsplit32 : memRegion (a + 16#64) 32 =
      memRegion (a + 16#64) 16 ∗ memRegion (a + 32#64) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, ProofLib.memRegion_split (a + 16#64) 16 16 (by decide),
      show a + 16#64 + 16#64 = a + 32#64 from by bv_omega]
  rw [show (48 : Nat) = 16 + 32 from rfl, ProofLib.memRegion_split a 16 32 (by decide),
    hsplit32, r1b_region16_to_cells a, h16, h32]
  simp only [sepExists_sepConj_left]
  congr 1; funext v0
  simp only [sepExists_sepConj_right]
  congr 1; funext v1
  congr 1; funext v2; congr 1; funext v3; congr 1; funext v4; congr 1; funext v5
  ac_rfl

def r1b_SpeRegs (cap ptr len r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) : Prop :=
  (r9 &&& 0xffffffff#64) = (cap &&& 0xffffffff#64) ∧
  (r23 <<< 32) = (cap &&& 0xffffffff00000000#64) ∧
  (r27 &&& 0x00ffffffffffffff#64) = (ptr &&& 0x00ffffffffffffff#64) ∧
  ((r16 &&& 0xff#64) <<< 56) = (ptr &&& 0xff00000000000000#64) ∧
  ((r14 &&& 16777215#64) <<< 32) = (len &&& 0x00ffffff00000000#64) ∧
  ((r15 <<< 8) &&& 0xffffff00#64) = (len &&& 0x00000000ffffff00#64) ∧
  (r28 <<< 56) = (len &&& 0xff00000000000000#64) ∧
  (r22 &&& 0xff#64) = (len &&& 0xff#64)

theorem r1b_SpeRegs.of_zext_r9_r22 {cap ptr len r10 r23 r27 r16 r14 r15 r28 r2 : BitVec 64}
    (h : r1b_SpeRegs cap ptr len r10 r23 r27 r16 r14 r15 r28 r2) :
    r1b_SpeRegs cap ptr len
      ((r10.truncate 32).zeroExtend 64) r23 r27 r16 r14 r15 r28
      ((r2.truncate 32).zeroExtend 64) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨by bv_bits, h2, h3, h4, h5, h6, h7, by bv_bits⟩

theorem r1b_SpeRegs.repack {cap ptr len r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64}
    (h : r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22) :
    (((r9 &&& 0xffffffff#64) ||| (r23 <<< 32)) = cap) ∧
    (((r27 &&& 0x00ffffffffffffff#64) ||| ((r16 &&& 0xff#64) <<< 56)) = ptr) ∧
    (((((r14 &&& 16777215#64) <<< 32) ||| (r28 <<< 56)) |||
      (((r15 <<< 8) &&& 0xffffff00#64) ||| (r22 &&& 0xff#64))) = len) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨by bv_bits, by bv_bits, by bv_bits⟩

def r1b_SpePayload (A : RustAlloc)
    (tag r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) : SepProp :=
  ∃∗ isPlain : Bool,
    if isPlain then
      ∃∗ i : Nat, ⌜RunDrop.PlainSpeTag i ∧ tag = speWord i⌝
    else
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64, ∃∗ bs : List (BitVec 8),
        ⌜tag = speWord 1 ∧ r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22⌝ ∗
          ownedBytes A cap ptr len bs

theorem r1b_SpePayload_plain (A : RustAlloc) {i : Nat} (hi : RunDrop.PlainSpeTag i)
    (r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) :
    emp ⊢ r1b_SpePayload A (speWord i) r9 r23 r27 r16 r14 r15 r28 r22 := by
  refine Entails.sepExists_right true (Entails.sepExists_right i ?_)
  rw [← sepConj_emp ⌜RunDrop.PlainSpeTag i ∧ speWord i = speWord i⌝]
  exact Entails.pure_right ⟨hi, rfl⟩ (Entails.refl _)

theorem r1b_SpePayload_str (A : RustAlloc) {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    {r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64}
    (hregs : r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22) :
    ownedBytes A cap ptr len bs ⊢
      r1b_SpePayload A (speWord 1) r9 r23 r27 r16 r14 r15 r28 r22 := by
  refine Entails.sepExists_right false
    (Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right len (Entails.sepExists_right bs ?_))))
  exact Entails.pure_right ⟨rfl, hregs⟩ (Entails.refl _)

theorem r1b_SpePayload_zext_r9_r22 {A : RustAlloc}
    {tag r10 r23 r27 r16 r14 r15 r28 r2 : BitVec 64} :
    r1b_SpePayload A tag r10 r23 r27 r16 r14 r15 r28 r2 ⊢
      r1b_SpePayload A tag
        ((r10.truncate 32).zeroExtend 64) r23 r27 r16 r14 r15 r28
        ((r2.truncate 32).zeroExtend 64) := by
  dsimp only [r1b_SpePayload]
  apply Entails.sepExists_elim
  rintro (_ | _)
  · refine Entails.sepExists_right false ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_right cap <|
      Entails.sepExists_elim fun ptr => Entails.sepExists_right ptr <|
      Entails.sepExists_elim fun len => Entails.sepExists_right len <|
      Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    apply Entails.pure_left
    rintro ⟨htag, hregs⟩
    exact Entails.pure_right ⟨htag, hregs.of_zext_r9_r22⟩ (Entails.refl _)
  · exact Entails.sepExists_right true (Entails.refl _)

theorem r1b_pack_speOwnedAt (A : RustAlloc) (a tag w1 w2 w3 w4 w5 : BitVec 64)
    (r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64)
    (hw1 : w1 = ((r9 &&& 0xffffffff#64) ||| (r23 <<< 32)))
    (hw2 : w2 = ((r27 &&& 0x00ffffffffffffff#64) ||| ((r16 &&& 0xff#64) <<< 56)))
    (hw3 : w3 = ((((r14 &&& 16777215#64) <<< 32) ||| (r28 <<< 56)) |||
      (((r15 <<< 8) &&& 0xffffff00#64) ||| (r22 &&& 0xff#64)))) :
    r1b_SpePayload A tag r9 r23 r27 r16 r14 r15 r28 r22 ∗
      ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k := by
  have htail16 : ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 0x20#64) 16 := by
    have h40 : a + 40#64 = (a + 32#64) + 8#64 := by bv_omega
    rw [h40]; exact r1b_cells2_to_region16 (a + 32#64) w4 w5
  have htail40 : ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion (a + 8#64) 40 := by
    have h24 : ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 0x20#64) 16 ⊢ memRegion (a + 24#64) 24 := by
      have ha : a + 0x20#64 = (a + 24#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w3 (by decide)
    have h16 : ((a + 16#64) ↦₆₄ w2) ∗ memRegion (a + 24#64) 24 ⊢ memRegion (a + 16#64) 32 := by
      have ha : a + 24#64 = (a + 16#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w2 (by decide)
    have h08 : ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
      have ha : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w1 (by decide)
    exact Entails.trans (sepConj_mono_right (Entails.trans
      (sepConj_mono_right (Entails.trans (sepConj_mono_right htail16) h24)) h16)) h08
  dsimp only [r1b_SpePayload]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  rintro (_ | _)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro len
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro bs
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨rfl, hregs⟩
    rcases hregs.repack with ⟨hcap, hptr, hlen⟩
    rw [hw1, hcap, hw2, hptr, hw3, hlen]
    refine Entails.sepExists_right (.withString 1 (by decide)) ?_
    dsimp only [RunDrop.speOwnedAt]
    have hvec : ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        ((a + 24#64) ↦₆₄ len) ∗ ownedBytes A cap ptr len bs ⊢
        ∃∗ bs' : List (BitVec 8), vecU8 A (a + 8#64) bs' := by
      have ha16 : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
      have ha24 : a + 24#64 = (a + 8#64) + 16#64 := by bv_omega
      rw [ha16, ha24]
      exact Entails.trans (r1b_ownedBytes_to_vecU8 A (a + 8#64) cap ptr len bs)
        (Entails.sepExists_right bs (Entails.refl _))
    refine Entails.trans (Entails.of_eq (show
      ownedBytes A cap ptr len bs ∗ ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗
        ((a + 16#64) ↦₆₄ ptr) ∗ ((a + 24#64) ↦₆₄ len) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) =
      (a ↦₆₄ speWord 1) ∗ (((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        ((a + 24#64) ↦₆₄ len) ∗ ownedBytes A cap ptr len bs) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hvec htail16)
  · simp only [↓reduceIte]
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro i
    rw [← sepConj_emp ⌜RunDrop.PlainSpeTag i ∧ tag = speWord i⌝, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hi, rfl⟩
    refine Entails.sepExists_right (.plain i hi) ?_
    dsimp only [RunDrop.speOwnedAt]
    rw [emp_sepConj]
    exact sepConj_mono_right htail40

/-! ## OOM `alloc::raw_vec::handle_error` Panic Stubs (`R+0x2d44 .. R+0x2d7c`) -/

theorem r1b_oom_2d44 {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hst : InRun img ext s0 s 0x2d44) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2d44 12
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm _ => ?_
  exact r1b_handle_error_panic (img := img) (ext := ext)
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp [hsm, arm64_norm]))

theorem r1b_oom_2d68 {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hst : InRun img ext s0 s 0x2d68) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2d68 12
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm _ => ?_
  exact r1b_handle_error_panic (img := img) (ext := ext)
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp [hsm, arm64_norm]))

theorem r1b_oom_2d5c {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hst : InRun img ext s0 s 0x2d5c) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x120#64) ↦₆₄ v0) ∗ F) Q Qp (runOom s0) := by
  intro fsp
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2d5c 12
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm _ => ?_
  exact r1b_handle_error_panic (img := img) (ext := ext)
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

theorem r1b_oom_2d74 {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hst : InRun img ext s0 s 0x2d74) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x158#64) ↦₆₄ v0) ∗ F) Q Qp (runOom s0) := by
  intro fsp
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2d74 12
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm _ => ?_
  exact r1b_handle_error_panic (img := img) (ext := ext)
    (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

/-! ## Error Stack-Frame Gap and Shared Context -/

def r1b_errFrameRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x110 ∗
  memRegion (fsp + 0x118#64) 4 ∗
  memRegion (fsp + 0x130#64) 0x20 ∗
  memRegion (fsp + 0x160#64) 0x08 ∗
  memRegion (fsp + 0x180#64) 0x08 ∗
  memRegion (fsp + 0x1d0#64) 0xd0 ∗
  memRegion (fsp + 0x2c0#64) 0x210 ∗
  memRegion (fsp + 0x500#64) 0x24f0

private theorem r1b_merge_region (fsp : BitVec 64) (o1 n1 n2 : Nat)
    (ho : BitVec.ofNat 64 o1 + BitVec.ofNat 64 n1 = BitVec.ofNat 64 (o1 + n1) := by decide)
    (hb : n1 + n2 ≤ 2 ^ 64 := by decide) :
    memRegion (fsp + BitVec.ofNat 64 o1) n1 ∗ memRegion (fsp + BitVec.ofNat 64 (o1 + n1)) n2 =
      memRegion (fsp + BitVec.ofNat 64 o1) (n1 + n2) := by
  have heq : fsp + BitVec.ofNat 64 (o1 + n1) = (fsp + BitVec.ofNat 64 o1) + BitVec.ofNat 64 n1 := by
    rw [BitVec.add_assoc, ho]
  rw [heq]
  exact (ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o1) n1 n2 hb).symm

theorem r1b_rejoin_errFrame (fsp : BitVec 64) :
    r1b_errFrameRest fsp ∗
    memRegion (fsp + 0x110#64) 8 ∗
    memRegion (fsp + 0x11c#64) 4 ∗
    memRegion (fsp + 0x120#64) 16 ∗
    memRegion (fsp + 0x150#64) 16 ∗
    memRegion (fsp + 0x168#64) 24 ∗
    memRegion (fsp + 0x188#64) 48 ∗
    memRegion (fsp + 0x1b8#64) 24 ∗
    memRegion (fsp + 0x2a0#64) 32 ∗
    memRegion (fsp + 0x4d0#64) 48 ⊢
    runLocals fsp [] := by
  dsimp only [r1b_errFrameRest, runLocals, runLocalsFrom]
  have hf0 : memRegion fsp 0x110 = memRegion (fsp + 0#64) 0x110 := by
    have hz : fsp + 0#64 = fsp := by bv_omega
    rw [hz]
  refine Entails.of_eq ?_
  calc
    _ = memRegion (fsp + 0#64) 0x110 ∗
        (memRegion (fsp + 0x110#64) 8 ∗
        (memRegion (fsp + 0x118#64) 4 ∗
        (memRegion (fsp + 0x11c#64) 4 ∗
        (memRegion (fsp + 0x120#64) 16 ∗
        (memRegion (fsp + 0x130#64) 0x20 ∗
        (memRegion (fsp + 0x150#64) 16 ∗
        (memRegion (fsp + 0x160#64) 8 ∗
        (memRegion (fsp + 0x168#64) 24 ∗
        (memRegion (fsp + 0x180#64) 8 ∗
        (memRegion (fsp + 0x188#64) 48 ∗
        (memRegion (fsp + 0x1b8#64) 24 ∗
        (memRegion (fsp + 0x1d0#64) 0xd0 ∗
        (memRegion (fsp + 0x2a0#64) 32 ∗
        (memRegion (fsp + 0x2c0#64) 0x210 ∗
        (memRegion (fsp + 0x4d0#64) 48 ∗
         memRegion (fsp + 0x500#64) 0x24f0))))))))))))))) := by rw [hf0]; ac_rfl
    _ = memRegion (fsp + 0#64) runLocalBytes := by
      rw [r1b_merge_region fsp 0x4d0 48 0x24f0,
          r1b_merge_region fsp 0x2c0 0x210 0x2520,
          r1b_merge_region fsp 0x2a0 32 0x2730,
          r1b_merge_region fsp 0x1d0 0xd0 0x2750,
          r1b_merge_region fsp 0x1b8 24 0x2820,
          r1b_merge_region fsp 0x188 48 0x2838,
          r1b_merge_region fsp 0x180 8 0x2868,
          r1b_merge_region fsp 0x168 24 0x2870,
          r1b_merge_region fsp 0x160 8 0x2888,
          r1b_merge_region fsp 0x150 16 0x2890,
          r1b_merge_region fsp 0x130 0x20 0x28a0,
          r1b_merge_region fsp 0x120 16 0x28c0,
          r1b_merge_region fsp 0x11c 4 0x28d0,
          r1b_merge_region fsp 0x118 4 0x28d4,
          r1b_merge_region fsp 0x110 8 0x28d8,
          r1b_merge_region fsp 0 0x110 0x28e0]

structure r1b_ErrCtx (img : Obj.Image) (ext : String → Option (State → State))
    (g : RunCall) (d : Init1Data) (s0 s : State) (off : Nat) : Prop where
  st : InRun img ext s0 s off
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  trace : s0.trace <+: s.trace
  hist : s.fs.files = runFiles g.i ∧
    Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = []
  ans : g.a = some none

theorem r1b_ErrCtx.of_call {img : Obj.Image} {ext : String → Option (State → State)}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat}
    (hc : r1b_ErrCtx img ext g d s0 st_bl off)
    (hin : InRun img ext s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_ErrCtx img ext g d s0 sf off' := {
  st := hin
  x19 := hcs.1.trans hc.x19
  x20 := hcs.2.1.trans hc.x20
  x21 := hcs.2.2.1.trans hc.x21
  trace := htr ▸ hc.trace
  hist := ⟨hfs.trans hc.hist.1, htr ▸ hc.hist.2⟩
  ans := hc.ans
}

def r1b_errCore (A : RustAlloc) (g : RunCall) (d : Init1Data) (s0 : State) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗
  memRegion g.call 56 ∗
  storesAt A g.stores StoresGhost.opened ∗
  (g.inp ↦ₛ inputOf g.i g.c) ∗
  addrNameHeap A d.meG ∗
  ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
  runSaved s0 ∗
  r1b_errFrameRest fsp ∗
  ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
  ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
  ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
  protocolAddressAt A d.peerG (fsp + 0x2a0#64)

def r1b_errCommon (A : RustAlloc) (g : RunCall) (d : Init1Data) (s0 : State)
    (resStack : Nat) : SepProp :=
  r1b_errCore A g d s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap

/-! ## Cleanup Tail (`2c68 ← 2c54 ← 2c34 ← 2bf0`) -/

private theorem r1b_addrNameHeap_to_ownedBytes (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  dsimp only [addrNameHeap, ownedBytes]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hne⟩
  refine Entails.pure_right ⟨by simp, hle, hlt, hne⟩ (Entails.refl _)

private theorem r1b_cleanup_2c68 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hbnd : r1b_StackBounds B resStack)
    (hst : InRun img ext s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htrace : s0.trace <+: s.trace)
    (hhist : s.fs.files = runFiles g.i ∧
      Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion ((runFsp s0) + 0x110#64) 8 ∗ memRegion ((runFsp s0) + 0x11c#64) 4 ∗
        memRegion ((runFsp s0) + 0x120#64) 16 ∗ memRegion ((runFsp s0) + 0x150#64) 16 ∗
        memRegion ((runFsp s0) + 0x168#64) 24 ∗ memRegion ((runFsp s0) + 0x188#64) 48 ∗
        memRegion ((runFsp s0) + 0x1b8#64) 24 ∗
        protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  have haddr : protocolAddressAt A d.peerG (fsp + 0x2a0#64) =
      ((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ∗ addrNameHeap A d.peerG := by
    rw [protocolAddressAt_eq_parts A d.peerG (fsp + 0x2a0#64)]
    have h2a8 : fsp + 0x2a0#64 + 8#64 = fsp + 0x2a8#64 := by bv_omega
    have h2b0 : fsp + 0x2a0#64 + 16#64 = fsp + 0x2b0#64 := by bv_omega
    rw [h2a8, h2b0]
  have hpeer32 : ∀ capv ptrv : BitVec 64,
      ((fsp + 0x2a0#64) ↦₆₄ capv) ∗ ((fsp + 0x2a8#64) ↦₆₄ ptrv) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ⊢ memRegion (fsp + 0x2a0#64) 32 := by
    intro capv ptrv
    have hup := addrUpperAt_entails_memRegion (fsp + 0x2b0#64) d.peerG
    have h2a8 : fsp + 0x2b0#64 = (fsp + 0x2a8#64) + 8#64 := by bv_omega
    have h2a0 : fsp + 0x2a8#64 = (fsp + 0x2a0#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hup)) ?_
    refine Entails.trans (sepConj_mono_right (by rw [h2a8]; exact r1b_cell64_cons ptrv (by decide))) ?_
    rw [h2a0]; exact r1b_cell64_cons capv (by decide)
  rw [haddr]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2c68 20
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  by_cases hcap : d.peerG.name.cap = 0#64
  · rw [hcap]
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2c7c#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    have hst_m : InRun img ext s0 sm 0x2c7c := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    have hrej_m : AtReject img ext g StoresGhost.opened .postDispatch s0 sm := {
      base := hst_m
      x19 := by simpa [hsm, arm64_norm] using hx19
      preRegs := fun h => by cases h
      trace := by simpa [hsm, arm64_norm] using htrace
      hist := ⟨by simpa [hsm, arm64_norm] using hhist.1,
        by simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hrej sm StoresGhost.opened .postDispatch hrej_m)
    dsimp only [rejectMem]
    have h1 := hpeer32 0#64 d.peerG.name.ptr
    have h2 : addrNameHeap A d.peerG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (addrNameHeap A d.peerG ∗ anyHeap) by ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_
        (sepConj_mono_right (sepConj_mono_right h2))))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))
  · have hcap_f : (d.peerG.name.cap == 0#64) = false := beq_false_of_ne hcap
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hsm_sp : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run") := by
      dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2c7c := by
      dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
    dsimp only [fsp]
    apply MainHops.sepWPp_weaken_pre
    · refine Entails.trans (Entails.of_eq (show _ =
        addrNameHeap A d.peerG ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          memRegion (runFsp s0 + 0x1b8#64) 24 ∗
          (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗
            ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by ac_rfl))
        (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes A d.peerG))
    refine r1b_call_dealloc_ownedBytes (Q := Q) (cap := d.peerG.name.cap) (ptr := d.peerG.name.ptr)
      (len := BitVec.ofNat 64 d.peerG.name.bytes.length) (bs := d.peerG.name.bytes)
      hh hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm])
      hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    have hrej_f : AtReject img ext g StoresGhost.opened .postDispatch s0 sf := {
      base := hin_f
      x19 := hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19)
      preRegs := fun h => by cases h
      trace := htr_f ▸ (by simpa [hsm, arm64_norm] using htrace)
      hist := ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
        by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hrej sf StoresGhost.opened .postDispatch hrej_f)
    dsimp only [rejectMem]
    have h1 := hpeer32 d.peerG.name.cap d.peerG.name.ptr
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap by ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))

private theorem r1b_cleanup_2c54 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hbnd : r1b_StackBounds B resStack)
    (hst : InRun img ext s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htrace : s0.trace <+: s.trace)
    (hhist : s.fs.files = runFiles g.i ∧
      Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        runSaved s0 ∗ r1b_errFrameRest fsp ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x1b8#64) 24 ∗
        protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2c54 20
  have hpc := hst.pc; have hrun := hst.run
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  by_cases hcap : d.dirCap = 0#64
  · rw [hcap] at hx24 ⊢
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2c68#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    have hst_m : InRun img ext s0 sm 0x2c68 := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c68 (d := d) hh hbnd hst_m
      (by simpa [hsm, arm64_norm] using hx19) (by simpa [hsm, arm64_norm] using htrace)
      ⟨by simpa [hsm, arm64_norm] using hhist.1, by simpa [hsm, arm64_norm] using hhist.2⟩
      hans hpanic hrej)
    have hdrop_dir : ownedBytes A 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap ⊢
        anyHeap := entails_anyHeap _
    refine Entails.trans (Entails.of_eq (show _ =
      runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest fsp ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x1b8#64) 24 ∗ protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (ownedBytes A 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hdrop_dir))))))))))))))))
  · have hcap_f : (d.dirCap == 0#64) = false := beq_false_of_ne hcap
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hsm_sp : sm.sp = fsp := by simpa [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run") := by
      dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2c68 := by
      dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
    dsimp only [fsp] at hsm_sp ⊢
    refine MainHops.sepWPp_weaken_pre (Entails.of_eq (show _ =
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗ protocolAddressAt A d.peerG (runFsp s0 + 0x2a0#64) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by ac_rfl)) ?_
    refine r1b_call_dealloc_ownedBytes (cap := d.dirCap) (ptr := d.dirPtr)
      (len := BitVec.ofNat 64 d.dir.length) (bs := d.dir) (Q := Q) hh hbnd hinv_m hsm_pc (by simp [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (r1b_cleanup_2c68 (d := d) hh hbnd hin_f
        (hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19))
        (htr_f ▸ (by simpa [hsm, arm64_norm] using htrace))
        ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
          by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
        hans
        hpanic hrej)

theorem r1b_cleanup_2c34 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2c34)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon, r1b_errCore]
  rw [hfsp_eq]
  have h1b8_24 :
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ⊢ memRegion (fsp + 0x1b8#64) 24 := by
    have hc8 : fsp + 0x1c8#64 = (fsp + 0x1c0#64) + 8#64 := by bv_omega
    have hc0 : fsp + 0x1c0#64 = (fsp + 0x1b8#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _))) ?_
    refine Entails.trans (sepConj_mono_right (by rw [hc8]; exact r1b_cell64_cons d.dirCap (by decide))) ?_
    rw [hc0]; exact r1b_cell64_cons d.meG.name.ptr (by decide)
  have hres_split : memRegion g.res runResSize =
      (∃∗ vres : BitVec 64, g.res ↦₆₄ vres) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    conv_lhs => rw [show runResSize = 8 + (runResSize - 8) from rfl]
    rw [ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide), ProofLib.memRegion_eight]
  have hx19 := hc.x19; have hx20 := hc.x20; have hx21 := hc.x21
  have htrace := hc.trace; have hhist := hc.hist; have hans := hc.ans
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun vres => ?_
  generalize hstP : storesAt A g.stores StoresGhost.opened = stProp
  generalize hpeerP : protocolAddressAt A d.peerG (fsp + 0x2a0#64) = peerProp
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2c34 32
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  by_cases hcap : d.meG.name.cap = 0#64
  · rw [hcap] at hx21
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2c54#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hst_m : InRun img ext s0 sm 0x2c54 := {
      pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c54 (d := d) hh hbnd hst_m
      (by simpa only [hsm, arm64_norm] using hx19) (by simp only [hsm, arm64_norm])
      (by simp only [hsm, arm64_norm])
      (by simpa only [hsm, arm64_norm] using htrace)
      ⟨by simpa only [hsm, arm64_norm] using hhist.1,
        by simpa only [hsm, arm64_norm] using hhist.2⟩
      hans
      hpanic hrej)
    have hdrop_me : addrNameHeap A d.meG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [runResAt]
    rw [hstP, hpeerP]
    dsimp only [fsp] at h1b8_24 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
      memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
      (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
        ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (addrNameHeap A d.meG ∗ anyHeap) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h1b8_24 (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hdrop_me)))))))))))))))))
  · have hcap_f : (d.meG.name.cap == 0#64) = false := beq_false_of_ne hcap
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hsm_sp : sm.sp = fsp := by simpa only [hsm, arm64_norm] using hsp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run") := by
      dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2c54 := by
      dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
    dsimp only [fsp] at hsm_sp h1b8_24 ⊢
    apply MainHops.sepWPp_weaken_pre
    · refine Entails.trans (Entails.of_eq (show _ =
        addrNameHeap A d.meG ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
        (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
            ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
          anyHeap) by ac_rfl))
        (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes A d.meG))
    refine r1b_call_dealloc_ownedBytes (Q := Q) (cap := d.meG.name.cap) (ptr := d.meG.name.ptr)
      (len := BitVec.ofNat 64 d.meG.name.bytes.length) (bs := d.meG.name.bytes)
      hh hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm])
      hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2c54 (d := d) hh hbnd hin_f
        (hcs_f.1.trans (by simpa only [hsm, arm64_norm] using hx19))
        (hcs_f.2.2.2.1.trans (by simp only [hsm, arm64_norm]))
        (hcs_f.2.2.2.2.2.1.trans (by simp only [hsm, arm64_norm]))
        (htr_f ▸ (by simpa only [hsm, arm64_norm] using htrace))
        ⟨by rw [hfs_f]; simpa only [hsm, arm64_norm] using hhist.1,
          by rw [htr_f]; simpa only [hsm, arm64_norm] using hhist.2⟩
        hans
        hpanic hrej)
    dsimp only [runResAt]
    rw [hstP, hpeerP]
    refine Entails.trans (Entails.of_eq (show _ =
      ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
      memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
      (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
        ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left h1b8_24)))))))))))))

theorem r1b_cleanup_2bf0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2bf0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq]
  rw [r1b_region48_to_cells (fsp + 0x4d0#64)]
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have ho8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
  have ho16 : fsp + 0x4d0#64 + 16#64 = fsp + 0x4e0#64 := by bv_omega
  have ho24 : fsp + 0x4d0#64 + 24#64 = fsp + 0x4e8#64 := by bv_omega
  have ho32 : fsp + 0x4d0#64 + 32#64 = fsp + 0x4f0#64 := by bv_omega
  have ho40 : fsp + 0x4d0#64 + 40#64 = fsp + 0x4f8#64 := by bv_omega
  rw [ho8, ho16, ho24, ho32, ho40]
  apply MainHops.sepWPp_weaken_pre
  · exact Entails.of_eq (show _ =
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        ((fsp + 0x4d0#64) ↦₆₄ w0 ∗ (fsp + 0x4d8#64) ↦₆₄ w1 ∗
          (fsp + 0x4e0#64) ↦₆₄ w2 ∗ (fsp + 0x4e8#64) ↦₆₄ w3 ∗
          (fsp + 0x4f0#64) ↦₆₄ w4 ∗ (fsp + 0x4f8#64) ↦₆₄ w5)) ∗
      (errCore ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48) by ac_rfl)
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2bf0 68
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 +
      ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" -
      ls_off% "libsignal_cli::run") % 2 ^ 64))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hsm_sp : sm.sp = fsp := by simpa only [hsm, arm64_norm] using hsp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 +
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" -
        ls_off% "libsignal_cli::run") % 2 ^ 64) := by
    dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPc img ext 0x2c34 := by
    dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp only [hsm, arm64_norm]
  have hpack_all : ∀ w1' w2' w3' : BitVec 64,
      w1' = ((s.readReg64 (.gpr 9#5) &&& 0xffffffff#64) ||| (s.readReg64 (.gpr 23#5) <<< 32)) →
      w2' = ((s.readReg64 (.gpr 27#5) &&& 0x00ffffffffffffff#64) |||
        ((s.readReg64 (.gpr 16#5) &&& 0xff#64) <<< 56)) →
      w3' = ((((s.readReg64 (.gpr 14#5) &&& 16777215#64) <<< 32) |||
        (s.readReg64 (.gpr 28#5) <<< 56)) |||
        (((s.readReg64 (.gpr 15#5) <<< 8) &&& 0xffffff00#64) |||
          (s.readReg64 (.gpr 22#5) &&& 0xff#64))) →
      r1b_SpePayload A (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
      ((fsp + 0x4d0#64) ↦₆₄ s.readReg64 (.gpr 12#5) ∗
        (fsp + 0x4d8#64) ↦₆₄ w1' ∗ (fsp + 0x4e0#64) ↦₆₄ w2' ∗
        (fsp + 0x4e8#64) ↦₆₄ w3' ∗ (fsp + 0x4f0#64) ↦₆₄ s.readReg64 (.gpr 11#5) ∗
        (fsp + 0x4f8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := by
    intro w1' w2' w3' h1 h2 h3
    have hp := r1b_pack_speOwnedAt A (fsp + 0x4d0#64) (s.readReg64 (.gpr 12#5))
      w1' w2' w3' (s.readReg64 (.gpr 11#5)) (s.readReg64 (.gpr 13#5))
      (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) h1 h2 h3
    rw [ho8, ho16, ho24, ho32, ho40] at hp
    exact hp
  apply MainHops.sepWPp_weaken_pre
  · exact sepConj_mono_left (hpack_all _ _ _ (by bv_bits) (by bv_bits) (by bv_bits))
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun k => ?_
  dsimp only [fsp] at hsm_sp ⊢
  refine MainHops.sepWPp_weaken_pre (Entails.of_eq (show _ =
    RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) k ∗
    stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
    (errCore ∗ anyHeap ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48) by ac_rfl)) ?_
  refine r1b_call_dropSpeOwned (a := runFsp s0 + 0x4d0#64) (k := k) (Q := Q) hh hdrop hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
    hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
    (by simp only [hsm, arm64_norm]; dsimp only [fsp, runFsp, runFrame]; bv_omega) hpanic ?_
  intro sf hin_f hcs_f hfs_f htr_f
  have hc_f : r1b_ErrCtx img ext g d s0 sf 0x2c34 := {
    st := hin_f
    x19 := hcs_f.1.trans (by simpa only [hsm, arm64_norm] using hc.x19)
    x20 := hcs_f.2.1.trans (by simpa only [hsm, arm64_norm] using hc.x20)
    x21 := hcs_f.2.2.1.trans (by simpa only [hsm, arm64_norm] using hc.x21)
    trace := htr_f ▸ (by simpa only [hsm, arm64_norm] using hc.trace)
    hist := ⟨by rw [hfs_f]; simpa only [hsm, arm64_norm] using hc.hist.1,
      by rw [htr_f]; simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c34 hh hbnd hc_f hpanic hrej)
  dsimp only [r1b_errCommon]
  rw [herrCore]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
