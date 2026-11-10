/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacDsl
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacShallow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval

/-!
# Encodings and Invariants for the `PrfHmac` Reduction

Value encodings of shallow `PrfHmac` states into `ReductionDsl` types and list-length invariants
for the evaluation proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead
open OracleSpec OracleComp

/-! ## Encodings -/

/-- Injects flat shallow key indices into `muKeyIdTy`, mapping `< N_send_tot` to session IDs and
`N_send_tot + rc` to `.inr rc`. -/
def natToMuKeyIdVal (S : Setup) (i : Nat) : muKeyIdTy.denote :=
  if i < S.N_send_opk_tot then
    .inl (.inl (i / S.N_send_opk, i % S.N_send_opk))
  else if i < S.N_send_tot then
    let k := i - S.N_send_opk_tot
    .inl (.inr (.inl (k / S.N_send_no_opk, k % S.N_send_no_opk)))
  else
    .inr (i - S.N_send_tot)

def muStToVal (st : PrfHmacMuState) : muStTy.denote :=
  (st.keys.map (fun e => ((.inr e.1 : muKeyIdTy.denote), (e.2.1, msgKeysToVal e.2.2))),
    (st.chal.map (fun e => ((.inr e.1 : muKeyIdTy.denote), e.2)), (st.pending, st.bad)))

def muStToValS (S : Setup) (st : PrfHmacMuState) : muStTy.denote :=
  (st.keys.map (fun e => (natToMuKeyIdVal S e.1, (e.2.1, msgKeysToVal e.2.2))),
    (st.chal.map (fun e => (natToMuKeyIdVal S e.1, e.2)), (st.pending, st.bad)))

def hmStToVal {S : Setup} (jt : Nat) (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    hmStTy.denote :=
  (jt, (authHybridStateFixedToVal hst, muStToValS S mst))

def encContToVal (c : HmEncCont) : encContTy.denote :=
  ((.inr c.i : muKeyIdTy.denote), (c.r, (c.ad, (c.ct, muStToVal c.st))))

def encContToValS (S : Setup) (c : HmEncCont) : encContTy.denote :=
  (natToMuKeyIdVal S c.i, (c.r, (c.ad, (c.ct, muStToValS S c.st))))

def encPreToVal : (Option Bytes × PrfHmacMuState) ⊕ HmEncCont → encPreTy.denote
  | .inl (ct?, st) => .inl (ct?, muStToVal st)
  | .inr c => .inr (encContToVal c)

def encPreToValS (S : Setup) : (Option Bytes × PrfHmacMuState) ⊕ HmEncCont → encPreTy.denote
  | .inl (ct?, st) => .inl (ct?, muStToValS S st)
  | .inr c => .inr (encContToValS S c)

def intPrepToVal {S : Setup} (p : AuthIntSendPrep S) : intPrepTy.denote :=
  (principalEntryToVal p.uEntry, (p.peerPrincipal?.map (Prod.map id principalEntryToVal),
    ((p.isFreshPeer, (p.isIdealSend, p.msgPlain)),
      ((p.ekASk, (p.ekAPk, (p.ss, (p.kemCt, (p.ephASk, p.ephAPk))))),
        (drKeyToVal p.drKey, ((p.rk1, (p.ck1_0, (p.mkSeed, p.ck1_1))),
          (p.spqrSalt?, (p.pqRatchetMsg, (p.ad, ((p.spkHon, (p.opkHon, p.pqspkHon)),
            (p.roCache'.map (Prod.map id drKeyToVal), p.rootRoCache')))))))))))

def hmSendContToVal {S : Setup} (c : HmSendCont S) : hmSendContTy.denote :=
  (sessionIdToVal c.sid, (preKeyBundleToVal c.bundle, ((c.m0, c.m1),
    (intPrepToVal c.p, (authHybridStateFixedToVal c.hst, encContToValS S c.enc)))))

def hmResToVal {S : Setup} (r : HmRes S) : hmResTy.denote :=
  ((authRespToVal r.1.1, authHybridStateFixedToVal r.1.2), muStToValS S r.2)

def hmPreToVal {S : Setup} : HmRes S ⊕ HmSendCont S → hmPreTy.denote
  | .inl r => .inl (hmResToVal r)
  | .inr c => .inr (hmSendContToVal c)

def hmRecvDataToVal {S : Setup} (d : HmRecvData S) : hmRecvDataTy.denote :=
  (principalEntryToVal d.kEntry, (spkBundleEntryToVal d.bEntry, (d.opkPk?, (d.secrets,
    (authHybridStateToVal d.hstDec, (d.usedTriples', d.senderIsHonest))))))

def schedPrepToVal {S : Setup} (sp : AuthIntRecvSchedPrep S) : schedPrepTy.denote :=
  (sp.isUncorruptedHonestSender, (sp.matchedSess?.map idealAuthSessionToVal,
    (sp.useIdealBranch, (drKeyToVal sp.drKey, (sp.roCache'.map (Prod.map id drKeyToVal),
      (sp.sameEph, (sp.rk1, (sp.ck1_0, (sp.rootRoCache', (sp.mkSeed, (sp.ck1_1,
        sp.spqrSalt?)))))))))))

def schedOutToVal (o : HmSchedOut) : schedOutTy.denote :=
  o.map fun (dk, rk1, ck, pt, ro, root) =>
    (drKeyToVal dk, (rk1, (ck, (pt, (ro.map (Prod.map id drKeyToVal), root)))))

def hmCacheToVal {S : Setup} (cache : AuthMkSaltCache S) : authMkSaltCacheTy.denote :=
  cache.map (fun ((sid, salt?), (rc, mk)) => ((sessionIdToVal sid, salt?), (rc, msgKeysToVal mk)))

def schedResToVal {S : Setup} (r : (HmSchedOut × AuthMkSaltCache S) × PrfHmacMuState) :
    schedResTy.denote :=
  ((schedOutToVal r.1.1, hmCacheToVal r.1.2), muStToValS S r.2)

/-! ## Invariants -/

/-- List-length bounds on `PrfHmacMuState`. -/
structure MuBounded (n : Nat) (st : PrfHmacMuState) : Prop where
  keys_le    : st.keys.length ≤ n
  chal_le    : st.chal.length ≤ n
  pending_le : st.pending.length ≤ n

theorem MuBounded.mono {n m : Nat} {st : PrfHmacMuState} (h : n ≤ m) (hB : MuBounded n st) :
    MuBounded m st :=
  ⟨Nat.le_trans hB.keys_le h, Nat.le_trans hB.chal_le h, Nat.le_trans hB.pending_le h⟩

/-- Combined state invariant of the fused `PrfHmac` reduction at step `n`. -/
structure HmInv {S : Setup} (n : Nat) (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    Prop where
  bnd : AuthListsBounded n hst
  won : hst.toAuthHybridState.base.hasWonAuth = false
  mu  : MuBounded n mst

theorem HmInv.mono {S : Setup} {n m : Nat} {hst : AuthHybridStateFixed S} {mst : PrfHmacMuState}
    (h : n ≤ m) (hI : HmInv n hst mst) : HmInv m hst mst :=
  ⟨hI.bnd.mono h, hI.won, hI.mu.mono h⟩

/-- Strengthened state invariant bounding `idealSessions.length ≤ n`. -/
structure HmInvV2 {S : Setup} (n : Nat) (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    Prop extends HmInv n hst mst where
  ideal_le : hst.toAuthHybridState.idealSessions.length ≤ n

theorem HmInvV2.mono {S : Setup} {n m : Nat} {hst : AuthHybridStateFixed S} {mst : PrfHmacMuState}
    (h : n ≤ m) (hI : HmInvV2 n hst mst) : HmInvV2 m hst mst :=
  ⟨hI.toHmInv.mono h, Nat.le_trans hI.ideal_le h⟩

/-- Invariant of a paused send at step `n` whose completion yields `HmInv (n + 1)`. -/
structure HmSendCont.Bounded {S : Setup} (n : Nat) (c : HmSendCont S) : Prop where
  pending_le : c.enc.st.pending.length ≤ n
  post_inv   : ∀ t, HmInv (n + 1) (c.post t).1.2 (c.post t).2

structure HmSendCont.BoundedV2 {S : Setup} (n : Nat) (c : HmSendCont S) : Prop where
  pending_le : c.enc.st.pending.length ≤ n
  post_inv   : ∀ t, HmInvV2 (n + 1) (c.post t).1.2 (c.post t).2

def HmPreLeaf {S : Setup} (n : Nat) : HmRes S ⊕ HmSendCont S → Prop
  | .inl r => HmInv (n + 1) r.1.2 r.2
  | .inr c => c.Bounded n

def HmPreLeafV2 {S : Setup} (n : Nat) : HmRes S ⊕ HmSendCont S → Prop
  | .inl r => HmInvV2 (n + 1) r.1.2 r.2
  | .inr c => c.BoundedV2 n

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
