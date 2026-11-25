import REWB.MaskedTraversalFrontier

/-! Actual small-to-large geometric merging.  Only maintained light-side
positions are imported.  The heavy queue is retained; the light queue is
discarded only after that child's edge has already been scheduled.

Every import records its actual before/after snapshots for later local
bank repair.  These are reverse accumulators, not copied old logs.  No
whole occurrence class is scanned to discover changed neighborhoods. -/
namespace REWB.MaskedTraversalFrontier
variable {h : Nat}

structure Patch (h : Nat) where
  position : Nat
  before : Frontier h
  update : Inserted h
  deriving Repr

structure Imported (h : Nat) where
  frontier : Frontier h
  revPatches : List (Patch h)
  generated : Nat
  imports : Nat
  work : Nat
  deriving Repr

def initial (s : Frontier h) : Imported h := ⟨s,[],0,0,0⟩

def push (capacity length p : Nat) (out : Imported h) : Imported h :=
  let updated:=insert capacity length p out.frontier
  ⟨updated.frontier,⟨p,out.frontier,updated⟩::out.revPatches,
    out.generated+updated.generated,out.imports+1,out.work+updated.work+5⟩

def importLoop (capacity length : Nat) : List Nat→Imported h→Imported h
  | [],out => {out with work:=out.work+1}
  | p::ps,out => importLoop capacity length ps (push capacity length p out)

structure ImportSpec (length : Nat) (ps : List Nat) (before after : Imported h) : Prop where
  valid : after.frontier.Valid length
  members : ∀x,x∈after.frontier.state.occurrences.entries ↔
    x∈ps ∨ x∈before.frontier.state.occurrences.entries
  generated : after.generated≤before.generated+4*ps.length
  imports : after.imports=before.imports+ps.length
  work : after.work≤before.work+(129*h+158)*ps.length+1
  queue : MaskedThresholdQueue.count after.frontier.state.queue+before.generated=
    MaskedThresholdQueue.count before.frontier.state.queue+after.generated
  patches : after.revPatches.length=before.revPatches.length+ps.length

theorem importLoop_spec (capacity length : Nat) (ps : List Nat) (out : Imported h)
    (hv : out.frontier.Valid length) (hc : capacity=2^h)
    (hb : ∀p,p∈ps → p<capacity) :
    ImportSpec length ps out (importLoop capacity length ps out) := by
  induction ps generalizing out with
  | nil =>
    refine ⟨hv,?_,?_,rfl,?_,rfl,rfl⟩
    · intro x
      simp [importLoop]
    · simp [importLoop]
    · simp [importLoop]
  | cons p ps ih =>
    have hp:=hb p List.mem_cons_self
    have hs:=insert_valid capacity length p out.frontier hv hc hp
    have hw:=insert_measured capacity length p out.frontier hv hc hp
    have ht:=ih (push capacity length p out) hs
      (fun q hq=>hb q (List.mem_cons_of_mem p hq))
    change ImportSpec length (p::ps) out (importLoop capacity length ps (push capacity length p out))
    refine ⟨ht.valid,?_,?_,?_,?_,?_,?_⟩
    · intro x
      rw [ht.members]
      change (x∈ps ∨ x∈(insert capacity length p out.frontier).frontier.state.occurrences.entries) ↔ _
      rw [insert_mem capacity length p x out.frontier hv hc hp,List.mem_cons]
      simp only [eq_comm,or_assoc,or_left_comm]
    · have hh:=ht.generated
      change _≤out.generated+(insert capacity length p out.frontier).generated+4*ps.length at hh
      change _≤out.generated+4*(ps.length+1)
      omega
    · have hh:=ht.imports
      change _=out.imports+1+ps.length at hh
      change _=out.imports+(ps.length+1)
      omega
    · have hh:=ht.work
      change _≤out.work+(insert capacity length p out.frontier).work+5+(129*h+158)*ps.length+1 at hh
      change _≤out.work+(129*h+158)*(ps.length+1)+1
      rw [Nat.mul_succ]
      omega
    · have hh:=ht.queue
      change MaskedThresholdQueue.count (importLoop capacity length ps (push capacity length p out)).frontier.state.queue+
          (out.generated+(insert capacity length p out.frontier).generated)=
        MaskedThresholdQueue.count (insert capacity length p out.frontier).frontier.state.queue+
          (importLoop capacity length ps (push capacity length p out)).generated at hh
      have hq:=hw.2.2
      omega
    · have hh:=ht.patches
      change _=out.revPatches.length+1+ps.length at hh
      change _=out.revPatches.length+(ps.length+1)
      omega

structure Merged (h : Nat) extends Imported h where
  keptLeft : Bool
  discarded : Nat
  deriving Repr

def merge (capacity length : Nat) (left right : Frontier h) : Merged h :=
  if left.state.occurrences.count≤right.state.occurrences.count then
    let out:=importLoop capacity length left.positions (initial right)
    ⟨{out with work:=out.work+5},false,MaskedThresholdQueue.count left.state.queue⟩
  else
    let out:=importLoop capacity length right.positions (initial left)
    ⟨{out with work:=out.work+5},true,MaskedThresholdQueue.count right.state.queue⟩

theorem merge_valid (capacity length : Nat) (left right : Frontier h)
    (hl : left.Valid length) (hr : right.Valid length) (hc : capacity=2^h) :
    (merge capacity length left right).frontier.Valid length := by
  simp only [merge]
  split
  · exact (importLoop_spec capacity length left.positions (initial right) hr hc
      (fun p hp=>by have h:=hl.bounded p hp; omega)).valid
  · exact (importLoop_spec capacity length right.positions (initial left) hl hc
      (fun p hp=>by have h:=hr.bounded p hp; omega)).valid

theorem merge_mem (capacity length : Nat) (left right : Frontier h)
    (hl : left.Valid length) (hr : right.Valid length) (hc : capacity=2^h) (x : Nat) :
    x∈(merge capacity length left right).frontier.state.occurrences.entries ↔
      x∈left.state.occurrences.entries ∨ x∈right.state.occurrences.entries := by
  simp only [merge]
  split
  · have hm:=(importLoop_spec capacity length left.positions (initial right) hr hc
      (fun p hp=>by have h:=hl.bounded p hp; omega)).members x
    simpa only [initial,hl.positions.mem_iff] using hm
  · have hm:=(importLoop_spec capacity length right.positions (initial left) hl hc
      (fun p hp=>by have h:=hr.bounded p hp; omega)).members x
    simpa only [initial,hr.positions.mem_iff,or_comm] using hm

theorem merge_measured (capacity length : Nat) (left right : Frontier h)
    (hl : left.Valid length) (hr : right.Valid length) (hc : capacity=2^h) :
    (merge capacity length left right).imports=
      min left.state.occurrences.count right.state.occurrences.count ∧
    (merge capacity length left right).generated≤4*(merge capacity length left right).imports ∧
    (merge capacity length left right).work≤(129*h+158)*(merge capacity length left right).imports+6 ∧
    MaskedThresholdQueue.count (merge capacity length left right).frontier.state.queue+
      (merge capacity length left right).discarded=
      MaskedThresholdQueue.count left.state.queue+MaskedThresholdQueue.count right.state.queue+
        (merge capacity length left right).generated ∧
    (merge capacity length left right).revPatches.length=(merge capacity length left right).imports := by
  have hlc:=hl.count
  have hrc:=hr.count
  simp only [merge]
  split
  · rename_i hh
    have hs:=importLoop_spec capacity length left.positions (initial right) hr hc
      (fun p hp=>by have h:=hl.bounded p hp; omega)
    have hg:=hs.generated
    have hm:=hs.imports
    have hw:=hs.work
    have hq:=hs.queue
    have hp:=hs.patches
    simp only [initial,Nat.zero_add,List.length_nil] at hg hm hw hq hp
    dsimp only [initial]
    rw [hm]
    refine ⟨?_,hg,by omega,by omega,by omega⟩
    rw [Nat.min_eq_left hh,hlc]
  · rename_i hh
    have hs:=importLoop_spec capacity length right.positions (initial left) hl hc
      (fun p hp=>by have h:=hr.bounded p hp; omega)
    have hg:=hs.generated
    have hm:=hs.imports
    have hw:=hs.work
    have hq:=hs.queue
    have hp:=hs.patches
    simp only [initial,Nat.zero_add,List.length_nil] at hg hm hw hq hp
    dsimp only [initial]
    rw [hm]
    refine ⟨?_,hg,by omega,by omega,by omega⟩
    rw [Nat.min_eq_right (by omega),hrc]

end REWB.MaskedTraversalFrontier
