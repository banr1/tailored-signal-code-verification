/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Fetch
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` on Empty PQ State for the CLI Image

Proves `SpqrSendEmptyRunStmt` in the CLI image: `spqr::send::<Coins>` on an empty PQ ratchet state
returns `NotEnabled` without advancing the coins tape.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000

set_option maxHeartbeats 3200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Address Arithmetic and Empty-State Proofs -/

/-- `spqr::decode_state` as a wrapping offset from `spqr::send`: in the CLI image it lies below the
moved `spqr::send` copy, so `decode_state_empty_ok_at` is applied at its own entry (`k = 0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSend_add_decodeState_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName + bv% ((2^64 + ls_off% "spqr::decode_state" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr decodeStateName + BitVec.ofNat 64 0 := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    show CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName = num% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") by fnoff_eq,
    show CryptoVerification.libsignalSessionCode.fnOff decodeStateName = num% (ls_off% "spqr::decode_state") by fnoff_eq]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.tape_fold (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  refine Entails.pure_left fun _ => ?_
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_ext_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image) (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) := by
  have hfn := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  have hdec := sub_ok_at_of_fnAddr hC.decode_state_empty decodeStateName 0 (Nat.add_zero _)
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSend_add_decodeState_eq_fnAddr] at hdec
  have hmc := memcpyPcs_of_sessionMemcpyRegion (hC.toAllocContracts.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName (num% (ls_off% "memcpy" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>")))
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 0 108
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 136 88
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4608 12
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4632 36
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec, CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec, Spec.inImage, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  wp_steps
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.tape_fold img.base cur rest) (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image) (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_ext_trap C A ctl S ext img hC.to_trap hE

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hS : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) :
    subroutine_ok (trTrapProgAt img.base C abs) ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_ext_trap C A ctl S (trTrapExterns C abs) img
    (Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hS) hE

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hS : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) :
    subroutine_ok (rebasedTripleRatchetProg img.base C ctl abs) ((rebasedTripleRatchetProg img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) :=
  subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_trap C A ctl S abs img hS hE)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmptyRunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.SendEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_run'_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) : CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmptyRunStmt_trap C A ctl S abs img :=
  fun hS hE himg => root_of_tripleRatchetProgAt_trap himg
    (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_base_trap C A ctl S abs img hS hE)

/-- Establishes `SpqrSendEmptyRunStmt`: in-image `spqr::send::<Coins>` meets `spqrSendEmptySpec`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_run' (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) : CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmptyRunStmt C A ctl S abs img :=
  fun hS hE himg => subroutine_ok_prog_kit_of_trTrap himg
    (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendEmpty_run'_trap C A ctl S abs img hS hE himg)

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
