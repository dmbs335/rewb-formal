import REWB.MaskedTraversalDirty

/-! Dirty keys are generated from the actual recorded light imports and
validated live threshold records. The loops below use only bounded
neighbor reads and maintained sparse deduplication; they never enumerate
an occurrence class. These counts do not by themselves prove that an
unmarked descriptor/cursor is unchanged. That locality obligation is
deliberately separate from the executable provenance and budget here.

Collection is permitted during partial/equal-depth merges. Applying
resets is deferred until the driver reaches a complete positive band.
-/
namespace REWB.MaskedTraversalDirty
open REWB.MaskedOrdered REWB.MaskedTraversalFrontier
variable {h : Nat}

def PatchValid (capacity length : Nat) (p : Patch h) : Prop :=
  p.before.Valid length ∧ p.position<capacity ∧
    p.update=MaskedTraversalFrontier.insert capacity length p.position p.before

theorem importLoop_patches (capacity length : Nat) (ps : List Nat) (out : Imported h)
    (hv : out.frontier.Valid length) (hc : capacity=2^h)
    (hb : ∀p,p∈ps→p<capacity)
    (hp : ∀p,p∈out.revPatches→PatchValid capacity length p) :
    ∀p,p∈(importLoop capacity length ps out).revPatches→PatchValid capacity length p := by
  induction ps generalizing out with
  | nil => exact hp
  | cons p ps ih =>
    apply ih (push capacity length p out)
      (insert_valid capacity length p out.frontier hv hc (hb p List.mem_cons_self))
      (fun x hx=>hb x (List.mem_cons_of_mem p hx))
    intro patch hm
    change patch∈⟨p,out.frontier,insert capacity length p out.frontier⟩::out.revPatches at hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨hv,hb p List.mem_cons_self,rfl⟩
    · exact hp patch hm

theorem merge_patches (capacity length : Nat) (left right : Frontier h)
    (hl : left.Valid length) (hr : right.Valid length) (hc : capacity=2^h) :
    ∀p,p∈(MaskedTraversalFrontier.merge capacity length left right).revPatches→PatchValid capacity length p := by
  unfold MaskedTraversalFrontier.merge
  split
  · exact importLoop_patches capacity length left.positions (initial right) hr hc
      (fun p hp=>by have hb:=hl.bounded p hp; omega) (by intro p hp; cases hp)
  · exact importLoop_patches capacity length right.positions (initial left) hl hc
      (fun p hp=>by have hb:=hr.bounded p hp; omega) (by intro p hp; cases hp)

def patches (capacity : Nat) : List (Patch h)→Marked h→Marked h
  | [],out => {out with work:=out.work+1}
  | p::ps,out =>
    let marked:=markChange p.before.state.leaders p.update.frontier.state.leaders capacity p.position out
    patches capacity ps {marked with work:=marked.work+4}

def PatchKeys (ps : List (Patch h)) (capacity x : Nat) : Prop :=
  ∃p,p∈ps ∧ x∈(prepareChange p.before.state.leaders p.update.frontier.state.leaders capacity p.position).keys

theorem patches_spec (capacity length : Nat) (ps : List (Patch h)) (out : Marked h)
    (hv : out.keys.Valid) (hc : capacity=2^h)
    (hp : ∀p,p∈ps→PatchValid capacity length p) :
    (patches capacity ps out).keys.Valid ∧
    (∀x,x∈(patches capacity ps out).keys.tree.entries ↔ PatchKeys ps capacity x ∨ x∈out.keys.tree.entries) ∧
    (patches capacity ps out).requests≤out.requests+9*ps.length ∧
    (patches capacity ps out).keys.positions.length≤out.keys.positions.length+9*ps.length ∧
    (patches capacity ps out).work≤out.work+(308*h+274)*ps.length+1 := by
  induction ps generalizing out with
  | nil =>
    refine ⟨hv,?_,?_,?_,?_⟩
    · intro x; simp [patches,PatchKeys]
    · simp [patches]
    · simp [patches]
    · simp [patches]
  | cons p ps ih =>
    obtain ⟨hb,hbound,heq⟩:=hp p List.mem_cons_self
    have ha : p.update.frontier.Valid length := by
      rw [heq]
      exact insert_valid capacity length p.position p.before hb hc hbound
    have hs:=markChange_spec p.before.state.leaders p.update.frontier.state.leaders capacity p.position out
      hv hb.invariant.leadGood hb.invariant.leadFits ha.invariant.leadGood ha.invariant.leadFits hc (by omega)
    let marked:=markChange p.before.state.leaders p.update.frontier.state.leaders capacity p.position out
    have ht:=ih {marked with work:=marked.work+4} hs.1 (fun a ha=>hp a (List.mem_cons_of_mem p ha))
    rw [patches]
    refine ⟨ht.1,?_,?_,?_,?_⟩
    · intro x
      rw [ht.2.1]
      change (PatchKeys ps capacity x ∨ x∈marked.keys.tree.entries) ↔ _
      rw [hs.2.1]
      simp only [PatchKeys,List.mem_cons,exists_eq_or_imp]
      simp only [or_assoc,or_left_comm]
    · have hh:=ht.2.2.1
      change _≤marked.requests+9*ps.length at hh
      have hs':=hs.2.2.1
      change marked.requests≤out.requests+9 at hs'
      change _≤out.requests+9*(ps.length+1)
      dsimp only [marked] at hh hs' ⊢
      omega
    · have hh:=ht.2.2.2.1
      change _≤marked.keys.positions.length+9*ps.length at hh
      have hs':=hs.2.2.2.1
      change marked.keys.positions.length≤out.keys.positions.length+9 at hs'
      change _≤out.keys.positions.length+9*(ps.length+1)
      dsimp only [marked] at hh hs' ⊢
      omega
    · have hh:=ht.2.2.2.2
      change _≤marked.work+4+(308*h+274)*ps.length+1 at hh
      have hs':=hs.2.2.2.2
      change marked.work≤out.work+308*h+270 at hs'
      change _≤out.work+(308*h+274)*(ps.length+1)+1
      rw [Nat.mul_succ]
      dsimp only [marked] at hh hs' ⊢
      omega

def live (before after : Tree h) (capacity : Nat) : List MaskedClusterLeaders.Record→Marked h→Marked h
  | [],out => {out with work:=out.work+1}
  | e::es,out =>
    let marked:=markChange before after capacity e.value.edge.2 out
    live before after capacity es {marked with work:=marked.work+4}

def LiveKeys (before after : Tree h) (es : List MaskedClusterLeaders.Record) (capacity x : Nat) : Prop :=
  ∃e,e∈es ∧ x∈(prepareChange before after capacity e.value.edge.2).keys

theorem live_spec (before after : Tree h) (capacity : Nat)
    (es : List MaskedClusterLeaders.Record) (out : Marked h)
    (hv : out.keys.Valid) (hbg : before.Good) (hbf : before.Fits 0)
    (hag : after.Good) (haf : after.Fits 0) (hc : capacity=2^h)
    (hb : ∀e,e∈es→e.value.edge.2<capacity) :
    (live before after capacity es out).keys.Valid ∧
    (∀x,x∈(live before after capacity es out).keys.tree.entries ↔
      LiveKeys before after es capacity x ∨ x∈out.keys.tree.entries) ∧
    (live before after capacity es out).requests≤out.requests+9*es.length ∧
    (live before after capacity es out).keys.positions.length≤out.keys.positions.length+9*es.length ∧
    (live before after capacity es out).work≤out.work+(308*h+274)*es.length+1 := by
  induction es generalizing out with
  | nil =>
    refine ⟨hv,?_,?_,?_,?_⟩
    · intro x; simp [live,LiveKeys]
    · simp [live]
    · simp [live]
    · simp [live]
  | cons e es ih =>
    have hs:=markChange_spec before after capacity e.value.edge.2 out hv hbg hbf hag haf hc
      (by have he:=hb e List.mem_cons_self; omega)
    let marked:=markChange before after capacity e.value.edge.2 out
    have ht:=ih {marked with work:=marked.work+4} hs.1 (fun a ha=>hb a (List.mem_cons_of_mem e ha))
    rw [live]
    refine ⟨ht.1,?_,?_,?_,?_⟩
    · intro x
      rw [ht.2.1]
      change (LiveKeys before after es capacity x ∨ x∈marked.keys.tree.entries) ↔ _
      rw [hs.2.1]
      simp only [LiveKeys,List.mem_cons,exists_eq_or_imp]
      simp only [or_assoc,or_left_comm]
    · have hh:=ht.2.2.1
      change _≤marked.requests+9*es.length at hh
      have hs':=hs.2.2.1
      change marked.requests≤out.requests+9 at hs'
      change _≤out.requests+9*(es.length+1)
      dsimp only [marked] at hh hs' ⊢
      omega
    · have hh:=ht.2.2.2.1
      change _≤marked.keys.positions.length+9*es.length at hh
      have hs':=hs.2.2.2.1
      change marked.keys.positions.length≤out.keys.positions.length+9 at hs'
      change _≤out.keys.positions.length+9*(es.length+1)
      dsimp only [marked] at hh hs' ⊢
      omega
    · have hh:=ht.2.2.2.2
      change _≤marked.work+4+(308*h+274)*es.length+1 at hh
      have hs':=hs.2.2.2.2
      change marked.work≤out.work+308*h+270 at hs'
      change _≤out.work+(308*h+274)*(es.length+1)+1
      rw [Nat.mul_succ]
      dsimp only [marked] at hh hs' ⊢
      omega

/-- Consume the already executed scheduler result; no queue drain is
rerun. The exact-result premise in `crossing_spec` ties its records to
actual threshold validation rather than a supplied event count. -/
def crossing (before : MaskedClusterLeaders.State h) (after : MaskedClusterLeaders.Shortened h)
    (capacity : Nat) (out : Marked h) : Marked h :=
  live before.leaders after.state.leaders capacity after.live out

theorem crossing_spec (capacity old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (after : MaskedClusterLeaders.Shortened h) (he : after=MaskedClusterLeaders.shorten capacity fresh s)
    (out : Marked h) (hv : out.keys.Valid) (hi : MaskedClusterLeaders.Invariant old s)
    (hf : MaskedClusterLeaders.Future old s) (hc : capacity=2^h) (hle : fresh≤old) :
    (crossing s after capacity out).keys.Valid ∧
    (crossing s after capacity out).requests≤out.requests+9*after.popped ∧
    (crossing s after capacity out).keys.positions.length≤out.keys.positions.length+9*after.popped ∧
    (crossing s after capacity out).work≤out.work+(308*h+274)*after.popped+1 := by
  subst after
  dsimp only [crossing]
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hb:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hn:=MaskedThresholdEvents.shorten_work (h+1) fresh s.occurrences capacity s.queue hi.queueGood
  have hs:=live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live out hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hb e he; omega)
  have hlen : (MaskedClusterLeaders.shorten capacity fresh s).live.length≤
      (MaskedClusterLeaders.shorten capacity fresh s).popped := hn.2.1
  refine ⟨hs.1,?_,?_,?_⟩
  · have hh:=hs.2.2.1; change _≤out.requests+9*_; omega
  · have hh:=hs.2.2.2.1; change _≤out.keys.positions.length+9*_; omega
  · have hh:=hs.2.2.2.2
    have hm:=Nat.mul_le_mul_left (308*h+274) hlen
    change _≤out.work+(308*h+274)*_+1
    omega

end REWB.MaskedTraversalDirty
