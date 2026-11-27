import REWB.OneUseRangeBorderChoice

/-! Actual logarithmically many suffix-class choices with a clipped
prefix beginning. Only the cached dyadic rows are traversed. -/
namespace REWB.OneUseRange.Border.Regular
open REWB.BoundaryBorder REWB.BoundaryBorder.Regular REWB.Spec REWB.Periodic
variable {α : Type} {σ n h : Nat}

def row (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (out : Window.Selected) (base a j r : Nat) : Bool×Nat :=
  let left:=choice A B E ai bi ei out.first base a j r
  let right:=choice A B E ai bi ei out.second base a j r
  (left.1 || right.1,left.2+right.2+3)

theorem row_correct (A B E : DFA α) (w : Word α) (fallback : α) (out : Window.Selected) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : RowSupported (ArrayText.read w.toArray fallback) a j out)
    (ha : a≤w.length) (hr : r≤w.length) :
    (row A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) out base a j r).1=true ↔
        ∃p,out.Holds p ∧ p≤a ∧ endAt j a p≤r ∧ Predicate A B E w base p a j r := by
  simp only [row,Bool.or_eq_true,choice_correct A B E w fallback out.first base a j r hbase hs.1 ha hr,
    choice_correct A B E w fallback out.second base a j r hbase hs.2 ha hr]
  constructor
  · rintro (⟨p,hp,hrest⟩|⟨p,hp,hrest⟩)
    · exact ⟨p,Or.inl hp,hrest⟩
    · exact ⟨p,Or.inr hp,hrest⟩
  · rintro ⟨p,hp,hrest⟩
    rcases hp with hp|hp
    · exact Or.inl ⟨p,hp,hrest⟩
    · exact Or.inr ⟨p,hp,hrest⟩

theorem row_work (A B E : DFA α) (w : Word α) (fallback : α) (out : Window.Selected) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : RowSupported (ArrayText.read w.toArray fallback) a j out)
    (ha : a≤w.length) (hr : r≤w.length) :
    (row A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) out base a j r).2≤2*choiceBudget A B E w.length+3 := by
  have hl:=choice_work A B E w fallback out.first base a j r hbase hs.1 ha hr
  have hh:=choice_work A B E w fallback out.second base a j r hbase hs.2 ha hr
  simp only [row]
  omega

def rows (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (base a j r : Nat) : List Window.Selected→Bool×Nat
  | [] => (false,1)
  | x::xs =>
      let head:=row A B E ai bi ei x base a j r
      let tail:=rows A B E ai bi ei base a j r xs
      (head.1 || tail.1,head.2+tail.2+3)

theorem rows_correct (A B E : DFA α) (w : Word α) (fallback : α) (outs : List Window.Selected) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : RowsSupported (ArrayText.read w.toArray fallback) a j outs)
    (ha : a≤w.length) (hr : r≤w.length) :
    (rows A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base a j r outs).1=true ↔
        ∃p,(∃out,out∈outs ∧ out.Holds p) ∧ p≤a ∧ endAt j a p≤r ∧ Predicate A B E w base p a j r := by
  induction outs with
  | nil => simp only [rows,List.not_mem_nil,false_and,exists_false,Bool.false_eq_true]
  | cons out outs ih =>
    have hh:=row_correct A B E w fallback out base a j r hbase (hs out List.mem_cons_self) ha hr
    have ht:=ih (fun v hv=>hs v (List.mem_cons_of_mem _ hv))
    simp only [rows,Bool.or_eq_true,hh,ht]
    constructor
    · rintro (⟨p,hp,hrest⟩|⟨p,⟨v,hv,hp⟩,hrest⟩)
      · exact ⟨p,⟨out,List.mem_cons_self,hp⟩,hrest⟩
      · exact ⟨p,⟨v,List.mem_cons_of_mem _ hv,hp⟩,hrest⟩
    · rintro ⟨p,⟨v,hv,hp⟩,hrest⟩
      rcases List.mem_cons.mp hv with he|ht
      · subst v
        exact Or.inl ⟨p,hp,hrest⟩
      · exact Or.inr ⟨p,⟨v,ht,hp⟩,hrest⟩

theorem rows_work (A B E : DFA α) (w : Word α) (fallback : α) (outs : List Window.Selected) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : RowsSupported (ArrayText.read w.toArray fallback) a j outs)
    (ha : a≤w.length) (hr : r≤w.length) :
    (rows A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base a j r outs).2≤outs.length*(2*choiceBudget A B E w.length+6)+1 := by
  induction outs with
  | nil => simp only [rows,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons out outs ih =>
    have hh:=row_work A B E w fallback out base a j r hbase (hs out List.mem_cons_self) ha hr
    have ht:=ih (fun v hv=>hs v (List.mem_cons_of_mem _ hv))
    simp only [rows,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def dyadic (A B E : DFA (Fin σ)) (idx : WindowIndex.Index n h)
    (ai : BoundaryApplication.Range.Index A) (bi : BoundaryApplication.Range.Index B)
    (ei : BoundaryApplication.Range.Index E) (base a : Nat) (j : Fin (n+1)) (r : Nat) : Bool×Nat :=
  let choices:=Dyadic.query idx a j
  let found:=rows A B E ai bi ei base a j.val r choices.rows
  (found.1,choices.work+found.2+2)

theorem dyadic_correct (A B E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (base a : Nat) (j : Fin (w.toArray.size+1)) (r : Nat) (hbase : base≤a-(r-j.val)) (ha : a≤w.length) (hr : r≤w.length) :
    (dyadic A B E (WindowIndex.prepare w.toArray fallback)
      (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base a j r).1=true ↔
        ∃p,p<a ∧ endAt j.val a p≤r ∧
          slice w p a=slice w j.val (endAt j.val a p) ∧ Predicate A B E w base p a j.val r := by
  simp only [dyadic,rows_correct A B E w fallback _ base a j.val r hbase
    (dyadic_supported w.toArray fallback a j) ha hr]
  change (∃p,(Dyadic.query (WindowIndex.prepare w.toArray fallback) a j).Holds p ∧ _)↔_
  constructor
  · rintro ⟨p,hp,hpa,hpr,hpred⟩
    have he:=(Dyadic.query_iff_slices w fallback a j ha p).mp hp
    exact ⟨p,he.1,hpr,he.2.2,hpred⟩
  · rintro ⟨p,hpa,hpr,he,hpred⟩
    exact ⟨p,(Dyadic.query_iff_slices w fallback a j ha p).mpr
      ⟨hpa,by change endAt j.val a p≤w.length; omega,he⟩,by omega,hpr,hpred⟩

theorem dyadic_work (A B E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (base a : Nat) (j : Fin (w.toArray.size+1)) (r : Nat) (hbase : base≤a-(r-j.val)) (ha : a≤w.length) (hr : r≤w.length) :
    (dyadic A B E (WindowIndex.prepare w.toArray fallback)
      (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base a j r).2≤
        317*(MaskedSuffixClass.height w.length)^2+
          MaskedSuffixClass.height w.length*(2*choiceBudget A B E w.length+6)+6 := by
  have hd:=Dyadic.query_work_closed w.toArray fallback a j
  have hw:=rows_work A B E w fallback (Dyadic.query (WindowIndex.prepare w.toArray fallback) a j).rows
    base a j.val r hbase (dyadic_supported w.toArray fallback a j) ha hr
  simp only [Dyadic.query_length,WindowIndex.prepare_scales,List.size_toArray] at hw
  simp only [List.size_toArray] at hd
  change (Dyadic.query (WindowIndex.prepare w.toArray fallback) a j).work≤
    317*(MaskedSuffixClass.height w.length)^2+3 at hd
  simp only [dyadic]
  omega


theorem dyadic_work_closed (A B E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (base a : Nat) (j : Fin (w.toArray.size+1)) (r : Nat) (hbase : base≤a-(r-j.val)) (ha : a≤w.length) (hr : r≤w.length) :
    (dyadic A B E (WindowIndex.prepare w.toArray fallback)
      (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base a j r).2≤
        (2*fixedBudget A B E+521)*((w.length+1).log2+1)^2 := by
  have hw:=dyadic_work A B E w fallback base a j r hbase ha hr
  have hc : choiceBudget A B E w.length≤(fixedBudget A B E+96)*MaskedSuffixClass.height w.length :=
    choiceBudget_height A B E w.length
  let H:=MaskedSuffixClass.height w.length
  have hp : 1≤H := by dsimp [H,MaskedSuffixClass.height]; omega
  have hq : 1≤H^2 := by have hh:=Nat.mul_le_mul hp hp; simpa only [Nat.one_mul,Nat.pow_two] using hh
  have ht : 2*choiceBudget A B E w.length+6≤(2*fixedBudget A B E+198)*H := by
    have hm:=Nat.mul_le_mul_left 2 hc
    have hh:=Nat.mul_le_mul_left 6 hp
    dsimp only [H] at *
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at *
    omega
  have hm:=Nat.mul_le_mul_left H ht
  have he : H*((2*fixedBudget A B E+198)*H)=(2*fixedBudget A B E+198)*H^2 := by
    rw [Nat.pow_two]; ac_rfl
  rw [he] at hm
  have h6:=Nat.mul_le_mul_left 6 hq
  change (dyadic A B E (WindowIndex.prepare w.toArray fallback)
    (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
    (BoundaryApplication.Range.build E w) base a j r).2≤(2*fixedBudget A B E+521)*H^2
  change (dyadic A B E (WindowIndex.prepare w.toArray fallback)
    (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
    (BoundaryApplication.Range.build E w) base a j r).2≤317*H^2+H*(2*choiceBudget A B E w.length+6)+6 at hw
  simp only [Nat.add_mul] at hm ⊢
  omega


end REWB.OneUseRange.Border.Regular
