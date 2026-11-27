import REWB.BoundaryApplicationAggregate

/-! A linear static E aggregate for an actual endpoint bit vector.
Cell 0 is the identity and cell t>0 reads w[t-1]; a bit at t seeds
E.initial after that cell's letter. The balanced prefix query through
r+1 cells therefore reads exactly w[t:r]. Cached length and height
keep the online query independent of the original text representation. -/
namespace REWB.BoundaryApplication.Separated.Suffix
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

def cell (E : DFA (Fin σ)) (map : Range.Map E.stateCount) (bit : Bool) : Table 1 E.stateCount :=
  ⟨map,Vector.ofFn (fun _=>Vector.ofFn (fun q=>bit && decide (q=E.initial)))⟩

def cells (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) :
    Array (Table 1 E.stateCount) :=
  let rows:=FixedEnd.rows E w
  Array.ofFn (fun i : Fin (w.length+1)=>cell E (rows[i.val]?.getD (Range.one E.stateCount)) (bits.get i))

structure Index (E : DFA (Fin σ)) where
  length : Nat
  height : Nat
  tree : BoundaryIndex.Tree 1 E.stateCount height
  work : Nat

def build (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) : Index E :=
  let input:=cells E w bits
  let h:=BoundaryIndex.Tree.heightFor input.size
  let out:=BoundaryIndex.Tree.build input h 0
  ⟨input.size-1,h,out.1,out.2+input.size*(3*E.stateCount+6)+4⟩

def query (E : DFA (Fin σ)) (idx : Index E) (right : Nat) : Bool×Nat :=
  let out:=TokenIndex.query E (fun _=>true) idx.tree (right+1)
  (out.1,out.2+1)

theorem cells_size (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) :
    (cells E w bits).size=w.length+1 := Array.size_ofFn

theorem build_height (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) :
    (build E w bits).height=BoundaryApplication.height w.length := by
  simp only [build,cells_size,BoundaryApplication.height]

theorem build_good (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) :
    BoundaryIndex.Tree.Good (build E w bits).tree := BoundaryIndex.Tree.build_good _ _ _

theorem build_trans (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1))
    (i : Merge.Position (build E w bits).height) :
    (Merge.point (build E w bits).tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get := by
  change (Merge.point (BoundaryIndex.Tree.build (cells E w bits) _ 0).1 i).trans=_
  rw [MergeBuild.point_build]
  simp only [cells,Array.getElem?_ofFn]
  by_cases hi : i.val<w.length+1
  · simp only [dif_pos hi,Option.getD_some,cell,Table.view]
    rfl
  · rw [dif_neg hi,Option.getD_none,Table.view_one]
    have hnone : (FixedEnd.rows E w)[i.val]?=none :=
      Array.getElem?_eq_none (by rw [FixedEnd.rows_size]; omega)
    rw [hnone,Option.getD_none]
    funext q
    simp only [View.one,Table.get_ofFn,id_eq]

theorem build_active (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1))
    (i : Merge.Position (build E w bits).height) (c : Fin 1) (q : Fin E.stateCount) :
    (Merge.point (build E w bits).tree i).active c q=true ↔
      ∃target : Fin (w.length+1),target.val=i.val ∧ bits.get target=true ∧ q=E.initial := by
  change (Merge.point (BoundaryIndex.Tree.build (cells E w bits) _ 0).1 i).active c q=true ↔ _
  rw [MergeBuild.point_build]
  simp only [cells,Array.getElem?_ofFn]
  by_cases hi : i.val<w.length+1
  · simp only [dif_pos hi,Option.getD_some,cell,Table.view,Table.get_ofFn,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨hb,hq⟩
      exact ⟨⟨i.val,hi⟩,rfl,hb,hq⟩
    · rintro ⟨target,he,hb,hq⟩
      have ht : target=⟨i.val,hi⟩ := Fin.ext he
      subst target
      exact ⟨hb,hq⟩
  · simp only [dif_neg hi,Option.getD_none,Table.view_one,View.one,Bool.false_eq_true]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨target,he,_,_⟩
      have hh:=target.isLt
      omega

theorem query_correct (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1))
    (right : Nat) (hr : right≤w.length) :
    (query E (build E w bits) right).1=true ↔
      ∃target : Fin (w.length+1),target.val≤right ∧ bits.get target=true ∧ E.accepts (slice w target.val right) := by
  have hcap : w.length+1≤2^(build E w bits).height := by
    rw [build_height]
    exact BoundaryIndex.Tree.capacity (w.length+1)
  rw [show (query E (build E w bits) right).1=(TokenIndex.query E (fun _=>true) (build E w bits).tree (right+1)).1 from rfl,
    Aggregate.query_correct E w _ (build_good E w bits) hcap (build_trans E w bits) (fun _=>true) right hr]
  constructor
  · rintro ⟨i,hi,c,q,_,hactive,hE⟩
    obtain ⟨target,he,hbits,hq⟩:=(build_active E w bits i c q).mp hactive
    subst q
    exact ⟨target,by omega,hbits,by simpa only [DFA.accepts,he] using hE⟩
  · rintro ⟨target,ht,hbits,hE⟩
    let i : Merge.Position (build E w bits).height:=⟨target.val,by have hh:=target.isLt; omega⟩
    refine ⟨i,ht,⟨0,by decide⟩,E.initial,rfl,?_,hE⟩
    exact (build_active E w bits i _ E.initial).mpr ⟨target,rfl,hbits,rfl⟩

def budget (E : DFA (Fin σ)) (n : Nat) : Nat :=
  2*(n+2)*(BoundaryIndex.Tree.joinBudget 1 E.stateCount+BoundaryIndex.Tree.leafBudget 1 E.stateCount)+
    (n+1)*(3*E.stateCount+6)+4

theorem build_work (E : DFA (Fin σ)) (w : Word (Fin σ)) (bits : Vector Bool (w.length+1)) :
    (build E w bits).work≤budget E w.length := by
  have hh:=BoundaryIndex.Tree.build_steps (cells E w bits) (BoundaryIndex.Tree.heightFor (cells E w bits).size) 0
  have hc:=Nat.mul_le_mul_right (BoundaryIndex.Tree.joinBudget 1 E.stateCount+BoundaryIndex.Tree.leafBudget 1 E.stateCount)
    (BoundaryIndex.Tree.capacity_upper (cells E w bits).size)
  simp only [build,cells_size,budget]
  simp only [cells_size,Nat.add_assoc,Nat.reduceAdd] at hc hh ⊢
  omega

theorem query_work (E : DFA (Fin σ)) (idx : Index E) (right : Nat) :
    (query E idx right).2≤(idx.height+1)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2 := by
  have hh:=TokenIndex.query_steps E (fun _ : Fin 1=>true) idx.tree (right+1)
  change (TokenIndex.query E (fun _=>true) idx.tree (right+1)).2+1≤_
  simp only [Nat.one_mul] at hh
  omega

end REWB.BoundaryApplication.Separated.Suffix
