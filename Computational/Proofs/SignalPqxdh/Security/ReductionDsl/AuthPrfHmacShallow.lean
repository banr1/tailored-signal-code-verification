/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacA
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacRun
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic

/-!
# Shallow Decomposition of the Fused `PrfHmac` Step

Decomposes `prfMuRun jt (stepAuthMuPrim S q hst) mst` into `embedPrim (hmPre S jt q hst mst) >>=
hmResume`, separating `PrimBaseSpec` pre-processing from the at-most-one `PrfHmac` oracle query,
and replaces closure-returning receive preparation with closure-free `HmRecvData`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open FgGapDh
open OracleSpec OracleComp

/-! ## Multi-key Game Steps -/

def hmKeyP (i : ℕ) (st : PrfHmacMuState) :
    OracleComp PrimBaseSpec ((ℕ × MessageKeys) × PrfHmacMuState) :=
  match st.keys.lookup i with
  | some e => pure (e, st)
  | none => do
    let mk ← embedUnif sampleMessageKeys80
    pure ((st.keys.length, mk), { st with keys := (i, (st.keys.length, mk)) :: st.keys })

theorem prfHmacMuKey_eq (i : ℕ) (st : PrfHmacMuState) :
    prfHmacMuKey i st = embedPrim (spec := prfHmacSpec) (hmKeyP i st) := by
  unfold prfHmacMuKey hmKeyP
  rcases h : st.keys.lookup i with _ | e
  · simp only [embedPrim_bind, embedPrim_pure]
    rfl
  · rfl

theorem embedPrim_ite {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (c : Prop) [Decidable c]
    (a b : OracleComp PrimBaseSpec α) :
    embedPrim (spec := spec) (if c then a else b) =
      if c then embedPrim (spec := spec) a else embedPrim (spec := spec) b := by
  split <;> rfl

def hmForgeP (jt i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) :
    OracleComp PrimBaseSpec (Bool × PrfHmacMuState) :=
  if st.chal.lookup i == some (ad, ct) then pure (false, st)
  else do
    let ((r, mk), st) ← hmKeyP i st
    let x := aeadMacInput ad (etmBody ct)
    let fresh : Bool :=
      match st.chal.lookup i with
      | some (ad0, ct0) => x != aeadMacInput ad0 (etmBody ct0)
      | none => true
    if fresh ∧ 24 ≤ ct.length then
      if r ≤ jt then
        pure (false, { st with pending := (r, x, etmTag ct) :: st.pending })
      else do
        let res ← primQ (.aeadDec mk ad ct)
        pure (false, { st with bad := st.bad || res.isSome })
    else pure (false, st)

theorem prfHmacMuStep_tryForge (jt i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) :
    prfHmacMuStep jt (.tryForge i ad ct) st =
      embedPrim (spec := prfHmacSpec) (hmForgeP jt i ad ct st) := by
  simp only [prfHmacMuStep, hmForgeP, embedPrim_ite]
  split
  · rfl
  · rw [prfHmacMuKey_eq, embedPrim_bind]
    refine bind_congr fun p => ?_
    rcases p with ⟨⟨r, mk⟩, st'⟩
    simp only [embedPrim_ite, embedPrim_bind, embedPrim_pure]
    rfl

/-- Challenge encryption at rank `r ≤ jt` awaiting its 32-byte tag value. -/
structure HmEncCont where
  i  : ℕ
  r  : ℕ
  ad : Bytes
  ct : Bytes
  st : PrfHmacMuState

def HmEncCont.x0 (c : HmEncCont) : Bytes := aeadMacInput c.ad (etmBody c.ct)

def HmEncCont.post (c : HmEncCont) (t : Bytes) : Option Bytes × PrfHmacMuState :=
  (some (etmBody c.ct ++ t.take 8), { c.st with
    chal := (c.i, (c.ad, etmBody c.ct ++ t.take 8)) :: c.st.chal
    pending := c.st.pending.filter (fun e => !(e.1 == c.r && e.2.1 == c.x0))
    bad := c.st.bad || prfHmacPendingHit c.st.pending c.r c.x0 t })

/-- Pre-oracle `encOnce` step, returning `.inr` iff the key has rank `jt`. -/
def hmEncPre (jt i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) :
    OracleComp PrimBaseSpec ((Option Bytes × PrfHmacMuState) ⊕ HmEncCont) :=
  match st.chal.lookup i with
  | some _ => pure (.inl (none, st))
  | none => do
    let ((r, mk), st) ← hmKeyP i st
    let ct ← primQ (.aeadEnc mk ad pt)
    if r < jt then do
      let t ← embedUnif sampleBytes32
      pure (.inl ((HmEncCont.mk i r ad ct st).post t))
    else if r = jt then pure (.inr ⟨i, r, ad, ct, st⟩)
    else pure (.inl (some ct, { st with chal := (i, (ad, ct)) :: st.chal }))

def hmEncResume : (Option Bytes × PrfHmacMuState) ⊕ HmEncCont →
    OracleComp PrfHmacSimSpec (Option Bytes × PrfHmacMuState)
  | .inl res => pure res
  | .inr c => c.post <$> prfHmacEvalQ c.x0

theorem prfHmacMuStep_encOnce (jt i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) :
    prfHmacMuStep jt (.encOnce i ad pt) st =
      embedPrim (spec := prfHmacSpec) (hmEncPre jt i ad pt st) >>= hmEncResume := by
  simp only [prfHmacMuStep, hmEncPre]
  rcases h : st.chal.lookup i with _ | v
  · simp only [embedPrim_bind]
    rw [prfHmacMuKey_eq, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨⟨r, mk⟩, st'⟩
    rw [bind_assoc]
    change (prfHmacPrimQ (.aeadEnc mk ad pt) >>= _) = (prfHmacPrimQ (.aeadEnc mk ad pt) >>= _)
    refine bind_congr fun ct => ?_
    by_cases hlt : r < jt
    · have hle : r ≤ jt := hlt.le
      simp only [hle, hlt, ↓reduceIte, prfHmacTagQ, embedPrim_bind, embedPrim_pure, bind_assoc,
        pure_bind, hmEncResume]
      rfl
    · by_cases heq : r = jt
      · subst heq
        simp only [le_refl, hlt, ↓reduceIte, prfHmacTagQ, embedPrim_pure, pure_bind, hmEncResume,
          map_eq_bind_pure_comp]
        rfl
      · have hgt : ¬ r ≤ jt := by omega
        simp only [hgt, hlt, heq, ↓reduceIte, embedPrim_pure, pure_bind, hmEncResume]
  · rfl

/-! ## Send -/

abbrev HmRes (S : Setup) := (AuthResponse × AuthHybridStateFixed S) × PrfHmacMuState

/-- Send continuation whose challenge encryption awaits the oracle tag value. -/
structure HmSendCont (S : Setup) where
  sid    : SessionId S
  bundle : PreKeyBundleInput
  m0     : Bytes
  m1     : Bytes
  p      : AuthIntSendPrep S
  hst    : AuthHybridStateFixed S
  enc    : HmEncCont

def HmSendCont.post {S : Setup} (c : HmSendCont S) (t : Bytes) : HmRes S :=
  (finishAuthIntSendPure c.sid c.bundle c.m0 c.m1 c.p default ((c.enc.post t).1.getD []) c.hst,
    (c.enc.post t).2)

def hmSendTail (S : Setup) (jt : ℕ) (sid : SessionId S) (bundle : PreKeyBundleInput)
    (m0 m1 : Bytes) (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) (p : AuthIntSendPrep S) :
    OracleComp PrimBaseSpec (HmRes S ⊕ HmSendCont S) :=
  if p.isIdealSend then do
    let e ← hmEncPre jt (initSessionSlotIdx sid) p.ad p.msgPlain mst
    match e with
    | .inl (ct?, mst') =>
      pure (.inl (finishAuthIntSendPure sid bundle m0 m1 p default (ct?.getD []) hst, mst'))
    | .inr c => pure (.inr ⟨sid, bundle, m0, m1, p, hst, c⟩)
  else do
    let mk ← primQ (.deriveMsgKeys p.mkSeed p.spqrSalt?)
    let ct ← primQ (.aeadEnc mk p.ad p.msgPlain)
    pure (.inl (finishAuthIntSendPure sid bundle m0 m1 p mk ct hst, mst))

def hmSendPre (S : Setup) (jt : ℕ) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) : OracleComp PrimBaseSpec (HmRes S ⊕ HmSendCont S) := do
  match ← prepAuthIntSendPrim S sid u bundle m0 m1 hst with
  | none => pure (.inl ((.noneResp, hst), mst))
  | some p => hmSendTail S jt sid bundle m0 m1 hst mst p

def hmResume {S : Setup} : HmRes S ⊕ HmSendCont S → OracleComp PrfHmacSimSpec (HmRes S)
  | .inl r => pure r
  | .inr c => c.post <$> prfHmacEvalQ c.enc.x0

theorem prfMuRun_runAuthSendMuPrim (S : Setup) (jt : ℕ) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) :
    prfMuRun jt (runAuthSendMuPrim S sid u bundle m0 m1 hst) mst =
      embedPrim (spec := prfHmacSpec) (hmSendPre S jt sid u bundle m0 m1 hst mst) >>= hmResume := by
  simp only [runAuthSendMuPrim, hmSendPre]
  rw [prfMuRun_bind, prfMuRun_embedPrimMu, bind_map_left, embedPrim_bind, bind_assoc]
  refine bind_congr fun p? => ?_
  rcases p? with _ | p
  · rfl
  · simp only [hmSendTail]
    by_cases hI : p.isIdealSend = true
    · simp only [hI, ↓reduceIte, bind_assoc, pure_bind]
      rw [prfMuRun_bind, prfMuRun_encOnceMuQ, prfHmacMuStep_encOnce, bind_assoc, embedPrim_bind,
        bind_assoc]
      refine bind_congr fun e => ?_
      rcases e with ⟨ct?, mst'⟩ | c
      · simp only [hmEncResume, pure_bind, prfMuRun_pure, embedPrim_pure, hmResume]
      · simp only [hmEncResume, embedPrim_pure, pure_bind, hmResume,
          map_eq_bind_pure_comp, prfMuRun_pure]
        rfl
    · simp only [hI, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, primMuQ,
        prfMuRun_bind, prfMuRun_embedPrimMu, bind_map_left, embedPrim_bind, prfMuRun_pure,
        embedPrim_pure, hmResume]

/-! ## Receive -/

/-- Closure-free representation of `AuthIntRecvPrep`. -/
structure HmRecvData (S : Setup) where
  kEntry         : PrincipalEntry
  bEntry         : SpkBundleEntry
  opkPk?         : Option Bytes
  secrets        : Bytes
  hstDec         : AuthHybridState S
  usedTriples'   : List (Nat × KeyId × KeyId × Bytes)
  senderIsHonest : Bool

def HmRecvData.toPrep {S : Setup} (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool →
      AuthHybridState S → Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (d : HmRecvData S) : AuthIntRecvPrep S :=
  { kEntry := d.kEntry, bEntry := d.bEntry, opkPk? := d.opkPk?, secrets := d.secrets,
    hstDec := d.hstDec, finish := mkFinish d.usedTriples' d.senderIsHonest d.hstDec }

def hmFinishPrepP (S : Setup) (kVal jVal : Nat) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : OracleComp PrimBaseSpec (Option (HmRecvData S)) := do
  let st := hst.base
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys kVal msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  let isCanEk : Bool ← primQ (.isCanonical msg.hdr.ekAPk)
  let isCanEph : Bool ← primQ (.isCanonical msg.ephAPk)
  if !replayOk || !isCanEk || !isCanEph then return none
  let ss? : Option Bytes ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
  let some ss := ss? | return none
  let rRec : RecvKemRecord := {
    k := kVal, j := jVal, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk, kemCt :=
        msg.hdr.kemCt, kemSs := ss }
  let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
  let dh1 : Bytes ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
  let dh2 : Bytes ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
  let dh3 : Bytes ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
  let dh4? ← (match opkSk? with
    | some opkSk => do let d : Bytes ← primQ (.x25519 opkSk msg.hdr.ekAPk); pure (some d)
    | none => pure none)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
  return some {
    kEntry := kEntry, bEntry := bEntry, opkPk? := opkPk?, secrets := secrets,
    hstDec := hstDec, usedTriples' := usedTriples', senderIsHonest := senderPrincipal?.isSome }

theorem finishPrepareAuthRecvPrim_eq (S : Setup) (kVal jVal : Nat) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes)
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    finishPrepareAuthRecvPrim S kVal jVal kEntry bEntry opkSk? opkPk? mkFinish msg hst =
      Option.map (HmRecvData.toPrep mkFinish) <$>
        hmFinishPrepP S kVal jVal kEntry bEntry opkSk? opkPk? msg hst := by
  simp only [finishPrepareAuthRecvPrim, hmFinishPrepP, map_bind]
  refine bind_congr fun a => ?_
  refine bind_congr fun b => ?_
  split
  · simp
  · simp only [map_bind]
    refine bind_congr fun ss? => ?_
    rcases ss? with _ | ss
    · simp
    · simp only [map_bind, map_pure, Option.map_some]
      rfl

def hmRecvOPKPrepP (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    OracleComp PrimBaseSpec (Option (HmRecvData S)) := do
  let st := hst.base
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32) then return none
  if st.usedRecvOPK.contains (k.val, j.val, o.val) then return none
  let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
  if !senderOk then return none
  match st.principals.find? (fun (idx, _) => idx == k.val),
        st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)),
        st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
  | some (_, kEntry), some (_, bEntry), some (_, oEntry) =>
    if oEntry.consumed then return none
    hmFinishPrepP S k.val j.val kEntry bEntry (some oEntry.opkSk) (some oEntry.opkPk) msg hst
  | _, _, _ => return none

def hmRecvNoOPKPrepP (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    OracleComp PrimBaseSpec (Option (HmRecvData S)) := do
  let st := hst.base
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32) then return none
  if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return none
  let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
  if !senderOk then return none
  match st.principals.find? (fun (idx, _) => idx == k.val),
        st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
  | some (_, kEntry), some (_, bEntry) =>
    hmFinishPrepP S k.val j.val kEntry bEntry none none msg hst
  | _, _ => return none

theorem prepareAuthRecvOPKPrim_eq (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthRecvOPKPrim S k j o msg hst =
      Option.map (HmRecvData.toPrep (finishErasedRecvOPK k j o)) <$>
        hmRecvOPKPrepP S k j o msg hst := by
  simp only [prepareAuthRecvOPKPrim, hmRecvOPKPrepP]
  split
  · simp
  split
  · simp
  rw [map_bind]
  refine bind_congr fun ok => ?_
  split
  · simp
  split
  · rename_i heq1 heq2 heq3
    simp only [heq1, heq2, heq3]
    split
    · simp
    · exact finishPrepareAuthRecvPrim_eq _ _ _ _ _ _ _ _ _ _
  · rename_i hne
    split
    · rename_i h1 h2 h3
      exact (hne _ _ _ _ _ _ h1 h2 h3).elim
    · simp

theorem prepareAuthRecvNoOPKPrim_eq (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthRecvNoOPKPrim S k j l msg hst =
      Option.map (HmRecvData.toPrep (finishErasedRecvNoOPK k j l)) <$>
        hmRecvNoOPKPrepP S k j l msg hst := by
  simp only [prepareAuthRecvNoOPKPrim, hmRecvNoOPKPrepP]
  split
  · simp
  split
  · simp
  rw [map_bind]
  refine bind_congr fun ok => ?_
  split
  · simp
  split
  · rename_i heq1 heq2
    simp only [heq1, heq2]
    exact finishPrepareAuthRecvPrim_eq _ _ _ _ _ _ _ _ _ _
  · rename_i hne
    split
    · rename_i h1 h2
      exact (hne _ _ _ _ h1 h2).elim
    · simp

abbrev HmSchedOut := Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
  List ((Bytes × Bytes) × (Bytes × Bytes)))

def hmSchedFinP {S : Setup} (jt : ℕ) (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (sp : AuthIntRecvSchedPrep S)
    (mst : PrfHmacMuState) :
    OracleComp PrimBaseSpec ((HmSchedOut × AuthMkSaltCache S) × PrfHmacMuState) := do
  let sameMsgKeys : Bool :=
      match sp.matchedSess? with
      | some s => sp.sameEph && sameSaltKey sp.spqrSalt? s.spqrSalt?
      | none => false
  let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  if sp.useIdealBranch then
    match sp.matchedSess? with
    | some s =>
      if sameMsgKeys then
        if ad == s.ad && msg.aeadCt == s.aeadCt then
          return ((some (sp.drKey, sp.rk1, sp.ck1_1, s.msgPlain, sp.roCache', sp.rootRoCache'),
              mkSaltCache), mst)
        else do
          let (_, mst') ← hmForgeP jt (initSessionSlotIdx s.sid) ad msg.aeadCt mst
          return ((none, mkSaltCache), mst')
      else if sp.sameEph then
        match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid sp.spqrSalt?) with
        | some (_, (r0, _)) => do
          let (_, mst') ← hmForgeP jt (S.N_send_tot + r0) ad msg.aeadCt mst
          return ((none, mkSaltCache), mst')
        | none => do
          let (_, mst') ← hmForgeP jt (S.N_send_tot + recvCount) ad msg.aeadCt mst
          return ((none, ((s.sid, sp.spqrSalt?), (recvCount, default)) :: mkSaltCache), mst')
      else do
        let (_, mst') ← hmForgeP jt (S.N_send_tot + recvCount) ad msg.aeadCt mst
        return ((none, mkSaltCache), mst')
    | none => do
      let (_, mst') ← hmForgeP jt (S.N_send_tot + recvCount) ad msg.aeadCt mst
      return ((none, mkSaltCache), mst')
  else do
    let mk : MessageKeys ← primQ (.deriveMsgKeys sp.mkSeed sp.spqrSalt?)
    let pt? : Option Bytes ← primQ (.aeadDec mk ad msg.aeadCt)
    let some pt := pt? | return ((none, mkSaltCache), mst)
    return ((some (sp.drKey, sp.rk1, sp.ck1_1, pt, sp.roCache', sp.rootRoCache'),
      mkSaltCache), mst)

theorem prfMuRun_tryForge_bind {β : Type} (jt i : ℕ) (ad ct : Bytes)
    (k : Bool → OracleComp AeadMuIntSimSpec β) (mst : PrfHmacMuState) :
    prfMuRun jt (tryForgeMuQ i ad ct >>= k) mst =
      embedPrim (spec := prfHmacSpec) (hmForgeP jt i ad ct mst) >>= fun p =>
        prfMuRun jt (k p.1) p.2 := by
  rw [prfMuRun_bind, prfMuRun_tryForgeMuQ, prfHmacMuStep_tryForge]

local macro "hm_leaf" : tactic =>
  `(tactic| (rw [prfMuRun_tryForge_bind, embedPrim_bind]
             refine bind_congr fun p => ?_
             rcases p with ⟨_, _⟩
             exact prfMuRun_pure _ _ _))

theorem prfMuRun_finishAuthRecvScheduleMuPrim {S : Setup} (jt : ℕ) (kEntry : PrincipalEntry)
    (msg : PreKeyMsg) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (sp : AuthIntRecvSchedPrep S) (mst : PrfHmacMuState) :
    prfMuRun jt (finishAuthRecvScheduleMuPrim kEntry msg recvCount mkSaltCache sp) mst =
      embedPrim (spec := prfHmacSpec)
        (hmSchedFinP jt kEntry msg recvCount mkSaltCache sp mst) := by
  simp only [finishAuthRecvScheduleMuPrim, hmSchedFinP]
  by_cases hI : sp.useIdealBranch = true
  · simp only [hI, ↓reduceIte]
    rcases hm : sp.matchedSess? with _ | s
    · simp only
      hm_leaf
    · simp only
      split_ifs
      · exact prfMuRun_pure _ _ _
      · hm_leaf
      · split <;> rename_i heq <;> simp only [heq] <;> hm_leaf
      · hm_leaf
  · simp only [Bool.not_eq_true] at hI
    simp only [hI, Bool.false_eq_true, ↓reduceIte, primMuQ, prfMuRun_bind, prfMuRun_embedPrimMu,
      bind_map_left, embedPrim_bind]
    refine bind_congr fun mk => bind_congr fun pt? => ?_
    rcases pt? with _ | pt <;> rfl

def hmSchedP (S : Setup) (jt : ℕ) (hstDec : AuthHybridState S) (recvCount : Nat)
    (mkSaltCache : AuthMkSaltCache S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) (mst : PrfHmacMuState) :
    OracleComp PrimBaseSpec ((HmSchedOut × AuthMkSaltCache S) × PrfHmacMuState) := do
  match ← prepAuthIntRecvSchedPrim S hstDec kEntry bEntry opkPk? secrets msg with
  | none => pure ((none, mkSaltCache), mst)
  | some sp => hmSchedFinP jt kEntry msg recvCount mkSaltCache sp mst

theorem prfMuRun_evalAuthRecvScheduleMuPrim (S : Setup) (jt : ℕ) (hstDec : AuthHybridState S)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (mst : PrfHmacMuState) :
    prfMuRun jt (evalAuthRecvScheduleMuPrim S hstDec recvCount mkSaltCache kEntry bEntry opkPk?
        secrets msg) mst =
      embedPrim (spec := prfHmacSpec)
        (hmSchedP S jt hstDec recvCount mkSaltCache kEntry bEntry opkPk? secrets msg mst) := by
  simp only [evalAuthRecvScheduleMuPrim, hmSchedP]
  rw [prfMuRun_bind, prfMuRun_embedPrimMu, bind_map_left, embedPrim_bind]
  refine bind_congr fun sp? => ?_
  rcases sp? with _ | sp
  · rfl
  · exact prfMuRun_finishAuthRecvScheduleMuPrim jt kEntry msg recvCount mkSaltCache sp mst

def hmRecvTail (S : Setup) (jt : ℕ) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) (d : HmRecvData S)
    (fin : HmSchedOut → AuthResponse × AuthHybridState S) :
    OracleComp PrimBaseSpec (HmRes S) := do
  let ((res?, cache'), mst') ← hmSchedP S jt d.hstDec hst.recvCount hst.mkSaltCache d.kEntry
    d.bEntry d.opkPk? d.secrets msg mst
  pure (((fin res?).1,
    { toAuthHybridState := (fin res?).2
      recvCount := hst.recvCount + 1
      mkSaltCache := cache' }), mst')

/-! ## Fused Step -/

/-- Pre-oracle `PrimBaseSpec` stage of one `Auth` query in the fused `PrfHmac` reduction. -/
def hmPre (S : Setup) (jt : ℕ) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) : OracleComp PrimBaseSpec (HmRes S ⊕ HmSendCont S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.inl ((.noneResp, hst), mst))
    else hmSendPre S jt (.sendOPK u i) u bundle m0 m1 hst mst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.inl ((.noneResp, hst), mst))
    else hmSendPre S jt (.sendNoOPK u i) u bundle m0 m1 hst mst
  | .recvOPK k j o msg => do
    match ← hmRecvOPKPrepP S k j o msg hst.toAuthHybridState with
    | none => pure (.inl ((.noneResp, { hst with recvCount := hst.recvCount + 1 }), mst))
    | some d =>
      Sum.inl <$> hmRecvTail S jt msg hst mst d
        (finishErasedRecvOPK k j o d.usedTriples' d.senderIsHonest d.hstDec)
  | .recvNoOPK k j l msg => do
    match ← hmRecvNoOPKPrepP S k j l msg hst.toAuthHybridState with
    | none => pure (.inl ((.noneResp, { hst with recvCount := hst.recvCount + 1 }), mst))
    | some d =>
      Sum.inl <$> hmRecvTail S jt msg hst mst d
        (finishErasedRecvNoOPK k j l d.usedTriples' d.senderIsHonest d.hstDec)
  | q => (fun r => .inl (r, mst)) <$> stepAuthOtherPrim true S q hst

theorem prfMuRun_recv_eq (S : Setup) (jt : ℕ) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) (prepM : OracleComp PrimBaseSpec (Option (HmRecvData S)))
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      HmSchedOut → AuthResponse × AuthHybridState S) :
    prfMuRun jt (do
      let some prep ← embedPrimMu (Option.map (HmRecvData.toPrep mkFinish) <$> prepM)
        | return (.noneResp, { hst with recvCount := hst.recvCount + 1 })
      let (res?, mkSaltCache') ←
        evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
      let (resp, hst') := prep.finish res?
      return (resp, {
        toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' }))
      mst =
    embedPrim (spec := prfHmacSpec) (do
      match ← prepM with
      | none => pure (.inl ((.noneResp, { hst with recvCount := hst.recvCount + 1 }), mst))
      | some d =>
        Sum.inl <$> hmRecvTail S jt msg hst mst d
          (mkFinish d.usedTriples' d.senderIsHonest d.hstDec)) >>= hmResume := by
  rw [prfMuRun_bind, prfMuRun_embedPrimMu, bind_map_left, embedPrim_map, bind_map_left,
    embedPrim_bind, bind_assoc]
  refine bind_congr fun d? => ?_
  rcases d? with _ | d
  · rfl
  · simp only [Option.map_some, HmRecvData.toPrep, hmRecvTail]
    rw [prfMuRun_bind, prfMuRun_evalAuthRecvScheduleMuPrim, embedPrim_map, embedPrim_bind,
      bind_map_left, bind_assoc]
    refine bind_congr fun x => ?_
    simp only [prfMuRun_pure, embedPrim_pure, pure_bind, hmResume]

theorem prfMuRun_stepAuthMuPrim (S : Setup) (jt : ℕ) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    prfMuRun jt (stepAuthMuPrim S q hst) mst =
      embedPrim (spec := prfHmacSpec) (hmPre S jt q hst mst) >>= hmResume := by
  cases q
  case sendOPK u i bundle m0 m1 =>
    simp only [stepAuthMuPrim, hmPre]
    split
    · rfl
    · exact prfMuRun_runAuthSendMuPrim S jt _ u bundle m0 m1 hst mst
  case sendNoOPK u i bundle m0 m1 =>
    simp only [stepAuthMuPrim, hmPre]
    split
    · rfl
    · exact prfMuRun_runAuthSendMuPrim S jt _ u bundle m0 m1 hst mst
  case recvOPK k j o msg =>
    simp only [stepAuthMuPrim, hmPre]
    rw [prepareAuthRecvOPKPrim_eq]
    exact prfMuRun_recv_eq S jt msg hst mst _ (finishErasedRecvOPK k j o)
  case recvNoOPK k j l msg =>
    simp only [stepAuthMuPrim, hmPre]
    rw [prepareAuthRecvNoOPKPrim_eq]
    exact prfMuRun_recv_eq S jt msg hst mst _ (finishErasedRecvNoOPK k j l)
  all_goals
    simp only [stepAuthMuPrim, hmPre]
    rw [prfMuRun_embedPrimMu, embedPrim_map, bind_map_left]
    simp only [hmResume, bind_pure_comp]

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
