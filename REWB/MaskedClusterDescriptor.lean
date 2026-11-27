import REWB.MaskedClusterLeaderTrace

/-! Actual cluster descriptors from the cached occurrence and leader
trees. The query performs a constant number of membership/neighbor
queries, never scans entries, and receives no AP or anchor certificate.
Singletons use period=1 and repetitions=0 as the point-compiler convention.
The arithmetic-progression interpretation requires a complete class and
is proved separately. -/
namespace REWB.MaskedClusterDescriptor
open REWB.MaskedOrdered
variable {h : Nat}

structure Descriptor where
  first : Nat
  last : Nat
  period : Nat
  repetitions : Nat
  next : Option Nat
  previous : Option Nat
  following : Option Nat
  deriving Repr, DecidableEq

def Descriptor.nextAt (d : Descriptor) (textLength : Nat) : Nat := d.next.getD textLength

/-- Locate the containing leader only for an actual occurrence. The
inclusive predecessor is implemented by the strict query at p+1. -/
def locate (s : MaskedClusterLeaders.State h) (capacity p : Nat) : Option Nat×Nat :=
  let member:=Tree.contains s.occurrences capacity p
  if member.1 then
    let leader:=Tree.pred s.leaders capacity (p+1)
    (leader.1,member.2+leader.2+4)
  else (none,member.2+2)

theorem locate_work (s : MaskedClusterLeaders.State h) (capacity p : Nat) :
    (locate s capacity p).2≤11*h+9 := by
  have hm:=Tree.contains_work s.occurrences capacity p
  have hp:=Tree.pred_work s.leaders capacity (p+1)
  simp only [locate]
  split <;> omega

def finish (occurrences : Tree h) (capacity first last : Nat) (next : Option Nat) : Descriptor×Nat :=
  let successor:=Tree.succ occurrences capacity first
  let predecessor:=Tree.pred occurrences capacity last
  let following:=match next with
    | none => (none,1)
    | some p =>
      let after:=Tree.succ occurrences capacity p
      (after.1,after.2+1)
  let q:=if first<last then successor.1.getD first-first else 1
  let previous:=if first<last then predecessor.1 else none
  (⟨first,last,q,(last-first)/q,next,previous,following.1⟩,
    successor.2+predecessor.2+following.2+15)

theorem finish_work (occurrences : Tree h) (capacity first last : Nat) (next : Option Nat) :
    (finish occurrences capacity first last next).2≤21*h+25 := by
  have hs:=Tree.succ_work occurrences capacity first
  have hp:=Tree.pred_work occurrences capacity last
  cases next with
  | none => simp only [finish]; omega
  | some p =>
    have hf:=Tree.succ_work occurrences capacity p
    simp only [finish]
    omega

/-- Describe an actual leader. Invalid requests return none. The final
cluster uses the cached occurrence maximum rather than a sentinel scan. -/
def describeLeader (s : MaskedClusterLeaders.State h) (capacity first : Nat) : Option Descriptor×Nat :=
  let member:=Tree.contains s.leaders capacity first
  if member.1 then
    let next:=Tree.succ s.leaders capacity first
    let last:=match next.1 with
      | none => (s.occurrences.last,1)
      | some p => Tree.pred s.occurrences capacity p
    match last.1 with
    | none => (none,member.2+next.2+last.2+5)
    | some p =>
      let d:=finish s.occurrences capacity first p next.1
      (some d.1,member.2+next.2+last.2+d.2+6)
  else (none,member.2+2)

theorem describeLeader_work (s : MaskedClusterLeaders.State h) (capacity first : Nat) :
    (describeLeader s capacity first).2≤39*h+39 := by
  have hm:=Tree.contains_work s.leaders capacity first
  have hn:=Tree.succ_work s.leaders capacity first
  simp only [describeLeader]
  split
  · cases he : (Tree.succ s.leaders capacity first).1 with
    | none =>
      simp only [he]
      cases hl : s.occurrences.last with
      | none => simp only [hl]; omega
      | some last =>
        simp only [hl]
        have hf:=finish_work s.occurrences capacity first last none
        omega
    | some p =>
      have hl:=Tree.pred_work s.occurrences capacity p
      simp only [he]
      cases hp : (Tree.pred s.occurrences capacity p).1 with
      | none => simp only [hp]; omega
      | some last =>
        simp only [hp]
        have hf:=finish_work s.occurrences capacity first last (some p)
        omega
  · omega

def describe (s : MaskedClusterLeaders.State h) (capacity p : Nat) : Option Descriptor×Nat :=
  let leader:=locate s capacity p
  match leader.1 with
  | none => (none,leader.2+1)
  | some first =>
    let d:=describeLeader s capacity first
    (d.1,leader.2+d.2+2)

theorem describe_work (s : MaskedClusterLeaders.State h) (capacity p : Nat) :
    (describe s capacity p).2≤50*h+50 := by
  have hl:=locate_work s capacity p
  simp only [describe]
  cases he : (locate s capacity p).1 with
  | none => simp only [he]; omega
  | some first =>
    simp only [he]
    have hd:=describeLeader_work s capacity first
    omega

end REWB.MaskedClusterDescriptor
