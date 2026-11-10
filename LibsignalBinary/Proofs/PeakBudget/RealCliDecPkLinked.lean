/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model

/-!
# Linked `W4` (`recv-prekey`, Arm `R3b`) Binary-Wide Slot Envelope and Bridges

Defines the wide-clone `W4` (`recv-prekey`) slot abbreviations, `W4BinaryCallSiteDom`, and
`realCliDecPkBinaryWideSlotEnv`, together with pointer-erasure congruence and containment into
`(mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (StoresGhost pathOf)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams W4BinaryRecvPrekeyWideSlotEnv
   mkBinaryKitRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (FreshBobCloneDom SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeySlotParams W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyRealParams
   W4TryDecryptCall mkW4RecvPrekeySlotParams)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf
   W4TryDecryptPathACDomOf)
open LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. Wide-Clone `W4` (`recv-prekey`) Slot Abbreviations -/

abbrev W4CloneBDomEnv (evs : List AllocEvent) : Prop :=
  ∃ (G : SessionGhost) (ses : Session (List (BitVec 8))),
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses ∧ SegCloneEnv G ses.state evs

abbrev W4CloneACDomEnv (evs : List AllocEvent) : Prop :=
  ∃ (G : SessionGhost) (ses : Session (List (BitVec 8))),
    FreshBobCloneDom 16384 G ses ∧ SegCloneEnv G ses.state evs

abbrev W4TrialRunWideEnv (F : ShaCompress) (K : MlKem) (x : W4ArchivedTrial F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailWideEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (W4FailedTdCancelEnv F K x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

abbrev mkW4RecvPrekeyWideSlotParams (R : W4RecvPrekeyRealParams) :
    W4DecryptPrekeySlotParams (W4ArchivedTrial R.F) :=
  { mkW4RecvPrekeySlotParams R with TrialEnv := W4TrialRunWideEnv R.F R.K }

/-- Structural call-site guard on `W4RecvPrekeyRealParams` at `(F, K, maxCt, peerVal, files)`. -/
structure W4BinaryCallSiteDom (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParams) : Prop where
  eq_F : R.F = F
  eq_K : R.K = K
  eq_rd : R.rd = cliIo.rd
  eq_files : R.files = files
  eq_peerVal : R.peer.val = peerVal
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  ownKey_len : R.ownKeyName.length ≤ 64
  ownReg_len : R.ownRegName.length ≤ 64
  kpkMark_len : R.kpkMarkName.length ≤ 64
  res_old : R.x_res.cap.toNat ≤ 4096
  res_new : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096
  spqr_key : R.x_spqr.p.authKey.length ≤ 32
  cur_dom : (∀ evs, ¬ (mkW4RecvPrekeySlotParams R).CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur
  arch_valid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  arch_enc : (encodeRecord R.r_arch).length ≤ 2097152
  out0_valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  out0_enc : (encodeRecord R.r_out0).length ≤ 2097152
  out1_freshBob : FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1
  trials_len4 : R.archivedTrials.length ≤ 4
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomOf R.F R.K maxCt R.fc_cur
  trials_dom : ∀ y ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K maxCt y
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K maxCt R.td_AC

abbrev W4RealCallSiteDom := W4BinaryCallSiteDom

/-- Widened binary-kit `W4` (`recv-prekey`) slot envelope (`DecPkGhost → List AllocEvent → Prop`)
over `W4BinaryRecvPrekeyParams` and `W4BinaryRecvPrekeyWideSlotEnv`. -/
abbrev realCliDecPkBinaryWideSlotEnv [LibsignalPlacement]
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParams,
    W4BinaryCallSiteDom W.C.F W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnv w4 evs

section RflSanityChecks

example :
    @W4CloneBDomEnv =
      @LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4CloneBDomEnv := rfl

example :
    @W4CloneACDomEnv =
      @LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4CloneACDomEnv := rfl

example :
    @W4TrialRunWideEnv =
      @LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4TrialRunWideEnv := rfl

example :
    @mkW4RecvPrekeyWideSlotParams =
      @LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.mkW4RecvPrekeyWideSlotParams := rfl

end RflSanityChecks

theorem realCliDecPkBinaryWideSlotEnv_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnv X W x = realCliDecPkBinaryWideSlotEnv X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnv, hp, hf, hmsg]

/-! ## 2. Call-Site Domain Lift and `hrecvP_slot` Containment -/

theorem recv_rest_length_le_msgCapBytes {g : RunCall} {peerV : AddrV}
    {tag : BitVec 8} {rest : List (BitVec 8)}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = tag :: rest) :
    rest.length ≤ msgCapBytes := by
  have hin_stdin : (tag :: rest).length ≤ stdinCapBytes := by
    simpa [hc, inputOf, CallV.tag, hst] using hin
  have hrest_stdin : rest.length ≤ stdinCapBytes :=
    Nat.le_trans (Nat.le_succ rest.length) hin_stdin
  have hcap_le : stdinCapBytes ≤ msgCapBytes := by
    unfold stdinCapBytes msgCapBytes
    decide
  exact Nat.le_trans hrest_stdin hcap_le

private theorem w4TryDecryptCallDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCall F}
    (h : W4TryDecryptCallDomOf F K c₁ td) :
    W4TryDecryptCallDomOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem w4FailedTdDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {fc : W4FailedTryDecryptCall F}
    (h : W4FailedTdDomOf F K c₁ fc) :
    W4FailedTdDomOf F K c₂ fc :=
  ⟨w4TryDecryptCallDomOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem w4ArchivedTrialDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {tr : W4ArchivedTrial F}
    (h : W4ArchivedTrialDomOf F K c₁ tr) :
    W4ArchivedTrialDomOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    w4FailedTdDomOf_mono hc h.tr_fail⟩

private theorem w4TryDecryptPathACDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCall F}
    (h : W4TryDecryptPathACDomOf F K c₁ td) :
    W4TryDecryptPathACDomOf F K c₂ td :=
  ⟨w4TryDecryptCallDomOf_mono hc h.base, h.zero_skip⟩

theorem W4BinaryCallSiteDom.toRealDomOf {F : ShaCompress} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParams}
    (hcs : W4BinaryCallSiteDom F K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R where
  kpk_dir := hcs.kpk_dir
  outer_dom := by
    have hpeer40 : R.peer.name.bytes.length ≤ 40 := by
      have hp40 := parseArgs_peer_name_length_le hparse
      change R.peer.val.name.length ≤ 40
      rw [hcs.eq_peerVal]
      exact hp40
    have hsess2M : sessionCapBytes ≤ 2097152 := by
      unfold sessionCapBytes
      decide
    refine
      { peer_len := hpeer40
        ownKey_len := hcs.ownKey_len
        ownReg_len := hcs.ownReg_len
        kpkMark_len := hcs.kpkMark_len
        res_old := hcs.res_old
        res_new := hcs.res_new
        ikm_small := by decide
        spqr_key := hcs.spqr_key
        sess_cap := fun bs hr => by
          dsimp only [mkW4RecvPrekeySlotParams] at hr
          rw [hcs.eq_rd] at hr
          exact Nat.le_trans (cliIo_rd_ok_length_le_sessionCapBytes R.files _ bs hr) hsess2M
        small_cap := fun d _ n bs hr => by
          dsimp only [mkW4RecvPrekeySlotParams] at hr
          rw [hcs.eq_rd] at hr
          exact cliIo_rd_ok_length_le_sessionCapBytes R.files (pathOf d.path n) bs hr
        cur_dom := hcs.cur_dom
        arch_valid := hcs.arch_valid
        arch_enc := hcs.arch_enc
        out0_valid := hcs.out0_valid
        out0_enc := hcs.out0_enc
        out1_freshBob := hcs.out1_freshBob
        trials_len4 := hcs.trials_len4 }
  cur_fail_dom hcur := w4FailedTdDomOf_mono hct (hcs.cur_fail_dom hcur)
  trials_dom y hy := w4ArchivedTrialDomOf_mono hct (hcs.trials_dom y hy)
  tdB_dom hb := w4TryDecryptCallDomOf_mono hct (hcs.tdB_dom hb)
  tdAC_dom hac := w4TryDecryptPathACDomOf_mono hct (hcs.tdAC_dom hac)

abbrev w4RealCallSiteDom_toRealDomOf := @W4BinaryCallSiteDom.toRealDomOf

/-- Containment of `realCliDecPkBinaryWideSlotEnv` into
`(mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv` for any `S : RunSem` with
`S.pksmParse = pksmParse`. -/
theorem w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV : AddrV) (peerV : AddrV)
    (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : S.pksmParse rest = some pm)
    (hS_pksm : S.pksmParse = pksmParse := by rfl)
    {evs : List AllocEvent}
    (hevs : realCliDecPkBinaryWideSlotEnv X W (r3bDecPkGhost g meV peerV pm) evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv evs := by
  obtain ⟨w4, hcs, _hik, _hbk, henv⟩ := hevs
  have hparse_recv : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ hparse
  have hpk' : pksmParse rest = some pm := hS_pksm ▸ hpk
  have hct_rest : pm.message.ciphertext.length ≤ rest.length :=
    (pksmParse_lengths_le hpk').2.2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4.base :=
    hcs.toRealDomOf hparse_recv hct_cap
  have hdom4 : W4BinaryRecvPrekeyDom g.c g.i w4 := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨hcs.eq_peerVal, hdom.outer_dom.peer_len, hcs.eq_files, hcs.eq_rd, hdom⟩
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [hc]
  exact ⟨w4, hc ▸ hdom4, henv⟩

/-- Discharges the `hrecvP_slot` premise of
`CliSlotEnvelopeBridge.cliMainArmEnvs_runEnv_to_cliRunBinaryEnv` for any `S : RunSem` with
`S.pksmParse = pksmParse`. -/
theorem w4_hrecvP_slot_binaryWide_sub_binaryKit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ (meV : AddrV) (_meG : AddrGhost) (peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage) (evs : List AllocEvent),
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      realCliDecPkBinaryWideSlotEnv X W (r3bDecPkGhost g meV peerV pm) evs →
      (mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv evs :=
  fun meV _meG peerV rest pm _evs hc hst hpk hevs =>
    w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit
      img S X W g meV peerV rest pm hparse hin hc hst hpk hS_pksm hevs

end LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked
