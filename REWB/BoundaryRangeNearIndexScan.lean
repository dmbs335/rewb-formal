import REWB.BoundaryRangeNearIndexCost

/-! Counted bounded scans over the short block. All expensive matching
queries use the already-built variant cache. The loops enumerate split
and local endpoint positions only, never candidate copy lengths. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
variable {σ : Nat}

def scan (probe : Nat→Bool×Nat) : Nat→Nat→Bool×Nat
  | _,0 => (false,1)
  | start,fuel+1 =>
    let here:=probe start
    let rest:=scan probe (start+1) fuel
    (here.1 || rest.1,here.2+rest.2+3)

theorem scan_correct (probe : Nat→Bool×Nat) (start fuel : Nat) :
    (scan probe start fuel).1=true ↔
      ∃p,start≤p ∧ p<start+fuel ∧ (probe p).1=true := by
  induction fuel generalizing start with
  | zero =>
    simp only [scan,Bool.false_eq_true,false_iff,Nat.add_zero]
    rintro ⟨p,hp,he,_⟩
    omega
  | succ fuel ih =>
    simp only [scan,Bool.or_eq_true,ih]
    constructor
    · rintro (h | ⟨p,hp,he,h⟩)
      · exact ⟨start,by omega,by omega,h⟩
      · exact ⟨p,by omega,by omega,h⟩
    · rintro ⟨p,hp,he,h⟩
      by_cases hps : p=start
      · subst p; exact Or.inl h
      · exact Or.inr ⟨p,by omega,by omega,h⟩

theorem scan_work (probe : Nat→Bool×Nat) (start fuel budget : Nat)
    (hp : ∀p,start≤p→p<start+fuel→(probe p).2≤budget) :
    (scan probe start fuel).2≤fuel*(budget+3)+1 := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    have hh:=hp start (by omega) (by omega)
    have ht:=ih (start+1) (by intro p hl hr; exact hp p (by omega) (by omega))
    simp only [scan,Nat.succ_mul]
    omega

def regular (d : DFA (Fin σ)) (ranges : Range.Index d) (lo hi : Nat) : Bool×Nat :=
  let out:=Range.query d ranges lo hi
  (d.final (out.map.get d.initial),out.work+2)

theorem regular_correct (d : DFA (Fin σ)) (w : Word (Fin σ)) (lo hi : Nat)
    (hl : lo≤hi) (hr : hi≤w.length) :
    (regular d (Range.build d w) lo hi).1=true ↔ d.accepts (Spec.slice w lo hi) := by
  simp only [regular,Range.query_correct d w lo hi hl hr,DFA.accepts]

theorem regular_work (d : DFA (Fin σ)) (w : Word (Fin σ)) (lo hi : Nat)
    (hl : lo≤hi) (hr : hi≤w.length) :
    (regular d (Range.build d w) lo hi).2≤rangeBudget d w.length+2 :=
  Nat.add_le_add_right (Range.query_work d w lo hi hl hr) 2

def atSeparated {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right p : Nat) : Bool×Nat :=
  let k:=regular K idx.kranges left p
  let found:=separated idx p right
  (k.1 && found.1,k.2+found.2+2)

def atEnd {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (right p a : Nat) : Bool×Nat :=
  if h : a≤idx.length then
    let source : Fin (w.length+1):=⟨a,by rw [idx.length_eq] at h; omega⟩
    let c:=regular C idx.cranges a p
    let found:=fixedEnd idx p source right
    (c.1 && found.1,c.2+found.2+3)
  else (false,1)

def endsAt {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right p : Nat) : Bool×Nat :=
  let k:=regular K idx.kranges left p
  let found:=scan (atEnd idx right p) (idx.lower+1) (p-idx.lower)
  (k.1 && found.1,k.2+found.2+2)

def atStart {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (right p j : Nat) : Bool×Nat :=
  if h : j≤idx.length then
    let target : Fin (w.length+1):=⟨j,by rw [idx.length_eq] at h; omega⟩
    let d:=regular D idx.dranges p j
    let found:=fixedStart idx p target right
    (d.1 && found.1,d.2+found.2+3)
  else (false,1)

def startsAt {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right p : Nat) : Bool×Nat :=
  let k:=regular K idx.kranges left p
  let found:=scan (atStart idx right p) p (min idx.upper (right+1)-p)
  (k.1 && found.1,k.2+found.2+2)

def querySeparated {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right : Nat) : Bool×Nat :=
  scan (atSeparated idx left right) left (idx.upper-left)

def queryEnd {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right : Nat) : Bool×Nat :=
  scan (endsAt idx left right) left (idx.upper-left)

def queryStart {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right : Nat) : Bool×Nat :=
  scan (startsAt idx left right) left (idx.upper-left)

def queryThree {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right : Nat) : Bool×Nat :=
  let a:=querySeparated idx left right
  let b:=queryEnd idx left right
  let c:=queryStart idx left right
  (a.1 || b.1 || c.1,a.2+b.2+c.2+2)

end REWB.BoundaryRange.NearIndex
