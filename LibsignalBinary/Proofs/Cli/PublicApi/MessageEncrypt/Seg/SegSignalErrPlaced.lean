/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalErr
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `segSignal` `OTR::encrypt` Error Branch (`+0x3a4..+0x3c8` → `+0xc14`)

Proves `segSignal_placed_err_path_pf` on Block `464` (`lsProg_464 Hk`) under `[LibsignalPlacement]`,
stepping from `+0x3a4` on `.error e` to `tailSignalEncryptErr_placed_ok` at `+0xc14`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

set_option maxHeartbeats 800000 in
/-- **The `Err` path** (`+0x3a4..+0x3c8 b.eq` → T5 `+0xc14` → T1) under `[LibsignalPlacement]`:
`Err(protocol p)`. -/
theorem segSignal_placed_err_path_pf [LibsignalPlacement]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s (fun _ => False) := by
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hnp, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr, _hx20, hx25, hx26, hx28,
    _hpt, _hrest, _hloc, _hnow, hstk, g, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hp_pan : p ≠ .panic := by
    rintro rfl
    exact hnp herr
  rw [herr] at hm
  simp only [signalMessageResultAt, errResultAt, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨pqCap', pqPtr', hm⟩ := hm
  have hst : speAt A (utf8 "encrypt") (sp + 0x588#64) p ⊢
      ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
        ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗ words64At (sp + 0x588#64) ws ∗ H :=
    speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) (by intro h; cases h)
  have hm1 := segSignal_apply hst (by sep_focus) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ws, H, hm1⟩ := hm1
  obtain ⟨hstg, hm1⟩ := segSignal_pure_front hm1
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := segSignal_list_len6 ws hstg.2.1
  have hsplit : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb00#64) 24 ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    rw [show (0x588 : Nat) = 0x508 + (24 + 0x68) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x508 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x508) 24 _ (by decide)]
  have hm2 := segSignal_apply (Entails.of_eq_explicit hsplit) (by sep_focus) hm1
  have hm2' : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗ _ :=
    segSignal_apply (Entails.refl _) (by sep_focus) hm2
  obtain ⟨vs, hvs, hm3⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm2'
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3 vs hvs
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, hsp0]
    bv_omega
  have hm4 := segSignal_focusR (T := ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗ words64At (sp + 0xb00#64) [v0, v1, v2])
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm3
  refine SegExitPlaced.of_sepWP hm4 (segSignal_placed_step_err hs_pc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 _hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm6 := Satisfies.mono (sepConj_mono_left hPm3) hm5
  rw [← sepConj_assoc] at hm6
  have hm7 := segSignal_apply (segSignal_err_tail_ent A sp g sess taken k pqCap' pqPtr' (segSignalRes C S x otr).2
    w0 w1 w2 w3 w4 w5) (by sep_focus) hm6
  have hmod := segSignal_model_err (C := C) (S := S) (x := x) hcur hnone hfrom hrem
    (execOk_of_exec_error herr)
  have hdraws := (segSignal_sendState (S := S) (x := x) (c := .newOrUnchanged) hcur hnone hfrom hrem).2
  have hstf : kit.storeFinal st0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = st0 := by
    rw [hmod]; rfl
  have histf : ikit.idFinal ist0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = ist0 := by
    rw [hmod]; rfl
  refine tailSignalEncryptErr_placed_ok env x R0 s0 s3
    (okAnswers r .newOrUnchanged) (.protocol p)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) g (takenRecord sess taken)
    (some (pqCap', pqPtr', (segSignalRes C S x otr).2)) ?_ hstg ?_
  · refine ⟨⟨by rw [hmod, segSignal_ofProtocol hp_pan], by rw [hmod]; exact ⟨hsc.2, trivial⟩,
      by rw [hmod]; trivial⟩, ?_⟩
    rw [hs3_tr, htr, hmod, ikit.traceOfWith_load]; rfl
  · refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19,
      hcrl3, hs3_vregs.trans hvregs⟩, ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstk, ?_⟩
    rw [hdraws, hstf, histf]
    dsimp only
    rw [← hsp0]
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm7

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
