import REWB.BoundaryApplicationIndex
import REWB.BoundaryIndexQuery

/-! Exact endpoint semantics of the static E cells. A marker at cell t
is after that cell's letter; the aggregate through cell r therefore
advances it by precisely w[t:r], including empty endpoint intervals. -/
namespace REWB.BoundaryApplication.Aggregate
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ k m h : Nat}

theorem product_active (xs : List (View k m)) (c : Fin k) (q : Fin m) :
    (View.product xs).active c q=true ↔
      ∃i,i<xs.length ∧ ∃a,xs[i]?=some a ∧ ∃p,a.active c p=true ∧
        (View.product (xs.drop (i+1))).trans p=q := by
  induction xs with
  | nil =>
    change false=true ↔ _
    simp only [Bool.false_eq_true,List.length_nil,Nat.not_lt_zero,false_and,exists_false]
  | cons a xs ih =>
    change (View.mul a (View.product xs)).active c q=true ↔ _
    rw [View.mul_active,ih]
    constructor
    · rintro (⟨i,hi,b,hb,p,hp,hq⟩ | ⟨p,hp,hq⟩)
      · exact ⟨i+1,by simpa only [List.length_cons] using Nat.add_lt_add_right hi 1,
          b,hb,p,hp,hq⟩
      · exact ⟨0,by simp,a,rfl,p,hp,hq⟩
    · rintro ⟨i,hi,b,hb,p,hp,hq⟩
      cases i with
      | zero =>
        have he : a=b := Option.some.inj hb
        subst b
        exact Or.inr ⟨p,hp,hq⟩
      | succ i =>
        exact Or.inl ⟨i,by simp only [List.length_cons] at hi; omega,b,hb,p,hp,hq⟩

theorem product_trans (E : DFA (Fin σ)) (xs : List (View k E.stateCount)) (w : Word (Fin σ))
    (hm : xs.map View.trans=w.map (fun a=>fun q=>E.step q a)) (q : Fin E.stateCount) :
    (View.product xs).trans q=E.run q w := by
  induction xs generalizing w q with
  | nil =>
    cases w with
    | nil => rfl
    | cons a w => cases hm
  | cons a xs ih =>
    cases w with
    | nil => cases hm
    | cons b w =>
      have hh:=List.cons.inj hm
      change (View.product xs).trans (a.trans q)=E.run (E.step q b) w
      rw [hh.1]
      exact ih w hh.2 _

theorem suffix_trans (E : DFA (Fin σ)) (w : Word (Fin σ))
    (tree : BoundaryIndex.Tree k E.stateCount h)
    (hcap : w.length+1≤2^h)
    (ht : ∀i : Merge.Position h,(Merge.point tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get)
    (l r : Nat) (hl : l≤r) (hr : r≤w.length) (q : Fin E.stateCount) :
    (View.product ((BoundaryIndex.Tree.leaves tree).drop (l+1) |>.take (r-l))).trans q=
      E.run q (slice w l r) := by
  apply product_trans E _ _ _ q
  apply List.ext_getElem?
  intro i
  by_cases hi : i<r-l
  · have hiw : l+i<w.length := by omega
    have hit : l+1+i<2^h := by omega
    simp only [List.getElem?_map,List.getElem?_take,if_pos hi,List.getElem?_drop,
      slice,List.getElem?_eq_getElem hiw,Option.map]
    rw [BoundaryIndex.Tree.get_correct tree (l+1+i) hit]
    change some (Merge.point tree ⟨l+1+i,hit⟩).trans=
      some (fun q=>E.step q w[l+i])
    rw [ht]
    change some (((FixedEnd.rows E w)[l+1+i]?.getD (Vector.ofFn id)).get)=_
    rw [show l+1+i=(l+i)+1 by omega,FixedEnd.rows_succ E w (l+i) hiw]
    simp only [Option.getD_some]
    congr 1
    funext s
    exact Range.letter_get E w[l+i] s
  · simp only [List.getElem?_map,List.getElem?_take,if_neg hi,slice,Option.map]

theorem queryPrefix_active (E : DFA (Fin σ)) (w : Word (Fin σ))
    (tree : BoundaryIndex.Tree k E.stateCount h) (hg : BoundaryIndex.Tree.Good tree)
    (hcap : w.length+1≤2^h)
    (ht : ∀i : Merge.Position h,(Merge.point tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get)
    (r : Nat) (hr : r≤w.length) (c : Fin k) (q : Fin E.stateCount) :
    (BoundaryIndex.Tree.queryPrefix tree (r+1)).1.view.active c q=true ↔
      ∃i : Merge.Position h,i.val≤r ∧ ∃p,(Merge.point tree i).active c p=true ∧
        E.run p (slice w i.val r)=q := by
  rw [BoundaryIndex.Tree.queryPrefix_correct tree hg,product_active]
  have hsize : ((BoundaryIndex.Tree.leaves tree).take (r+1)).length=r+1 := by
    rw [List.length_take,BoundaryIndex.Tree.leaves_length]
    omega
  constructor
  · rintro ⟨i,hi,a,ha,p,hp,hq⟩
    rw [hsize] at hi
    have hiti : i<2^h := by omega
    have he : a=Merge.point tree ⟨i,hiti⟩ := by
      rw [List.getElem?_take,if_pos hi,BoundaryIndex.Tree.get_correct tree i hiti] at ha
      exact (Option.some.inj ha).symm
    subst a
    refine ⟨⟨i,hiti⟩,by change i≤r; omega,p,hp,?_⟩
    rw [List.drop_take,show r+1-(i+1)=r-i by omega,
      suffix_trans E w tree hcap ht i r (by omega) hr p] at hq
    exact hq
  · rintro ⟨i,hi,p,hp,hq⟩
    refine ⟨i.val,by rw [hsize]; omega,Merge.point tree i,?_,p,hp,?_⟩
    · rw [List.getElem?_take,if_pos (by omega : i.val<r+1),BoundaryIndex.Tree.get_correct tree i.val i.isLt]
      rfl
    · rw [List.drop_take,show r+1-(i.val+1)=r-i.val by omega,
        suffix_trans E w tree hcap ht i.val r hi hr p]
      exact hq

theorem query_correct (E : DFA (Fin σ)) (w : Word (Fin σ))
    (tree : BoundaryIndex.Tree k E.stateCount h) (hg : BoundaryIndex.Tree.Good tree)
    (hcap : w.length+1≤2^h)
    (ht : ∀i : Merge.Position h,(Merge.point tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get)
    (select : Fin k→Bool) (r : Nat) (hr : r≤w.length) :
    (TokenIndex.query E select tree (r+1)).1=true ↔
      ∃i : Merge.Position h,i.val≤r ∧ ∃c p,select c=true ∧
        (Merge.point tree i).active c p=true ∧ E.final (E.run p (slice w i.val r))=true := by
  simp only [TokenIndex.query,Counted.accepted_value,accepted_true]
  constructor
  · rintro ⟨c,q,hc,hactive,hfinal⟩
    obtain ⟨i,hi,p,hp,hq⟩:=(queryPrefix_active E w tree hg hcap ht r hr c q).mp hactive
    exact ⟨i,hi,c,p,hc,hp,by rw [hq]; exact hfinal⟩
  · rintro ⟨i,hi,c,p,hc,hp,hfinal⟩
    exact ⟨c,E.run p (slice w i.val r),hc,
      (queryPrefix_active E w tree hg hcap ht r hr c _).mpr ⟨i,hi,p,hp,rfl⟩,hfinal⟩

end REWB.BoundaryApplication.Aggregate
