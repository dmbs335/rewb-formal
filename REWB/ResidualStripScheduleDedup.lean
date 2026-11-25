import REWB.ResidualStripScheduleGeometry
import REWB.CountedProjection

/-! Executed exact-key deduplication and long-strip selection. Conversion,
key/trie work, filtering and emitted-list steps are charged. No output
list is searched to decide whether a strip has appeared before. -/
namespace REWB.ResidualStripSchedule
open REWB.IndexedGrid REWB.GlobalCoverage REWB.RunGeometry
variable {σ : Nat}

def pack (R : Strip) : Bounds := ⟨R.lo,R.hi,R.distance⟩
def unpack (R : Bounds) : Strip := ⟨R.lo,R.hi,R.period⟩

@[simp] theorem unpack_pack (R : Strip) : unpack (pack R)=R := by cases R; rfl
@[simp] theorem pack_unpack (R : Bounds) : pack (unpack R)=R := by cases R; rfl

theorem unpack_injective {R S : Bounds} (he : unpack R=unpack S) : R=S := by
  simpa only [pack_unpack] using congrArg pack he

structure Selected where
  strips : List Strip := []
  count : Nat := 0
  work : Nat := 1
  deriving Repr

def select (L : Nat) : List Bounds→Selected
  | [] => {}
  | R::Rs =>
      let tail:=select L Rs
      if L≤R.hi-R.lo then
        ⟨unpack R::tail.strips,tail.count+1,tail.work+6⟩
      else ⟨tail.strips,tail.count,tail.work+3⟩

def selectLoop (L : Nat) (acc : List Strip) (count work : Nat) : List Bounds→Selected
  | [] => ⟨acc.reverse,count,work+1⟩
  | R::Rs =>
      if L≤R.hi-R.lo then selectLoop L (unpack R::acc) (count+1) (work+6) Rs
      else selectLoop L acc count (work+3) Rs

theorem selectLoop_spec (L : Nat) (acc : List Strip) (count work : Nat) (Rs : List Bounds) :
    selectLoop L acc count work Rs=
      ⟨acc.reverse++(select L Rs).strips,count+(select L Rs).count,work+(select L Rs).work⟩ := by
  induction Rs generalizing acc count work with
  | nil => simp [selectLoop,select]
  | cons R Rs ih =>
    simp only [selectLoop,select]
    split <;> rw [ih] <;> simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    · congr 1 <;> omega
    · congr 1 <;> omega

def selectTR (L : Nat) (Rs : List Bounds) : Selected := selectLoop L [] 0 0 Rs

@[csimp] theorem select_eq_selectTR : select=selectTR := by
  funext L Rs
  simp only [selectTR,selectLoop_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem select_mem (L : Nat) (Rs : List Bounds) (R : Strip) :
    R∈(select L Rs).strips ↔ pack R∈Rs ∧ L≤span R := by
  induction Rs with
  | nil => simp [select]
  | cons S Ss ih =>
    simp only [select]
    split
    next hs =>
      rw [List.mem_cons,ih,List.mem_cons]
      constructor
      · rintro (he|⟨hm,hl⟩)
        · subst R
          exact ⟨Or.inl (pack_unpack S),hs⟩
        · exact ⟨Or.inr hm,hl⟩
      · rintro ⟨(he|hm),hl⟩
        · left
          simpa only [unpack_pack] using congrArg unpack he
        · exact Or.inr ⟨hm,hl⟩
    next hs =>
      rw [ih,List.mem_cons]
      constructor
      · rintro ⟨hm,hl⟩; exact ⟨Or.inr hm,hl⟩
      · rintro ⟨(he|hm),hl⟩
        · have he' : R=unpack S := by simpa only [unpack_pack] using congrArg unpack he
          subst R
          exact False.elim (hs hl)
        · exact ⟨hm,hl⟩

theorem select_count (L : Nat) (Rs : List Bounds) :
    (select L Rs).count=(select L Rs).strips.length := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih => simp only [select]; split <;> simp only [List.length_cons,ih]

theorem select_length (L : Nat) (Rs : List Bounds) : (select L Rs).strips.length≤Rs.length := by
  induction Rs with
  | nil => simp [select]
  | cons R Rs ih => simp only [select,List.length_cons]; split <;> simp only [List.length_cons] <;> omega

theorem select_work (L : Nat) (Rs : List Bounds) : (select L Rs).work≤6*Rs.length+1 := by
  induction Rs with
  | nil => simp [select]
  | cons R Rs ih => simp only [select,List.length_cons,Nat.mul_succ]; split <;> dsimp only <;> omega

theorem select_nodup (L : Nat) (Rs : List Bounds) (hn : Rs.Nodup) : (select L Rs).strips.Nodup := by
  induction Rs with
  | nil => exact List.nodup_nil
  | cons R Rs ih =>
    obtain ⟨hf,ht⟩:=List.nodup_cons.mp hn
    simp only [select]
    split
    · apply List.nodup_cons.mpr
      exact ⟨fun hm=>hf (by simpa only [pack_unpack] using ((select_mem L Rs (unpack R)).mp hm).1),ih ht⟩
    · exact ih ht

def dedup (n L : Nat) (Rs : List Strip) : Selected :=
  let converted:=CountedProjection.map (fun R=>(pack R,3)) Rs
  let unique:=RunDedup.run n converted.1
  let chosen:=select L unique.runs
  {chosen with work:=converted.2+unique.work+chosen.work+3}

theorem dedup_count (n L : Nat) (Rs : List Strip) :
    (dedup n L Rs).count=(dedup n L Rs).strips.length :=
  select_count _ _

theorem dedup_nodup (n L : Nat) (Rs : List Strip) : (dedup n L Rs).strips.Nodup :=
  select_nodup _ _ (RunDedup.run_nodup _ _)

theorem dedup_mem (n L : Nat) (Rs : List Strip)
    (hb : ∀R,R∈Rs→RunDedup.Bounded n (pack R)) (R : Strip) :
    R∈(dedup n L Rs).strips ↔ R∈Rs ∧ L≤span R := by
  simp only [dedup,CountedProjection.map_value]
  rw [select_mem,RunDedup.run_mem n (Rs.map pack) (by
    intro S hS
    obtain ⟨R,hR,rfl⟩:=List.mem_map.mp hS
    exact hb R hR)]
  constructor
  · rintro ⟨hm,hl⟩
    obtain ⟨S,hS,he⟩:=List.mem_map.mp hm
    have he' : S=R := by simpa only [unpack_pack] using congrArg unpack he
    exact ⟨he' ▸ hS,hl⟩
  · rintro ⟨hm,hl⟩
    exact ⟨List.mem_map.mpr ⟨R,hm,rfl⟩,hl⟩

theorem dedup_work (n L : Nat) (Rs : List Strip) :
    (dedup n L Rs).work≤(26*((n+1).log2+1)+15)*Rs.length+5 := by
  have hr:=RunDedup.run_work n (Rs.map pack)
  have hl:=RunDedup.run_length n (Rs.map pack)
  have hs:=select_work L (RunDedup.run n (Rs.map pack)).runs
  simp only [List.length_map] at hr hl
  simp only [dedup,CountedProjection.map_plain_steps,CountedProjection.map_value]
  change Rs.length*4+1+(RunDedup.run n (Rs.map pack)).work+
    (select L (RunDedup.run n (Rs.map pack)).runs).work+3≤_
  simp only [Nat.add_mul] at hr ⊢
  rw [Nat.mul_comm Rs.length 4]
  omega

theorem strip_bounded (f : Nat→Fin σ) (n : Nat) (R : Strip)
    (hv : MaximalStrip f n R.lo R.hi R.distance) : RunDedup.Bounded n (pack R) := by
  obtain ⟨hd,hl,hn,_⟩:=hv
  change R.lo≤n ∧ R.hi≤n ∧ R.distance≤n
  exact ⟨by omega,by omega,by omega⟩

/-- The existing grid generator is evaluated once; expensive residual
queries subsequently consume only this duplicate-free long list. -/
def generate (f : Nat→Fin σ) (n s L : Nat) : Selected :=
  let raw:=IndexedGrid.generate f n s
  let out:=dedup n L raw.strips
  {out with work:=raw.preparation+raw.queryWork+6*raw.probes+out.work+3}

theorem generate_mem (f : Nat→Fin σ) (n s L : Nat) (R : Strip) :
    R∈(generate f n s L).strips ↔ R∈(IndexedGrid.generate f n s).strips ∧ L≤span R :=
  dedup_mem _ _ _ (fun R hR=>strip_bounded f n R (IndexedGrid.generate_sound f n s R hR)) R

theorem generate_count (f : Nat→Fin σ) (n s L : Nat) :
    (generate f n s L).count=(generate f n s L).strips.length := dedup_count _ _ _

theorem generate_nodup (f : Nat→Fin σ) (n s L : Nat) : (generate f n s L).strips.Nodup :=
  dedup_nodup _ _ _

theorem generate_sound (f : Nat→Fin σ) (n s L : Nat) (R : Strip)
    (hR : R∈(generate f n s L).strips) : MaximalStrip f n R.lo R.hi R.distance ∧ L≤span R := by
  obtain ⟨hm,hl⟩:=(generate_mem f n s L R).mp hR
  exact ⟨IndexedGrid.generate_sound f n s R hm,hl⟩

theorem generate_span (f : Nat→Fin σ) (n s L : Nat) :
    totalSpan (generate f n s L).strips≤n^2 :=
  totalSpan_bound f n _ (fun R hR=>(generate_sound f n s L R hR).1) (generate_nodup f n s L)

theorem generate_length (f : Nat→Fin σ) (n s L : Nat) (hL : 0<L) :
    (generate f n s L).strips.length≤n^2/L :=
  long_count f n L _ hL (fun R hR=>(generate_sound f n s L R hR).1)
    (generate_nodup f n s L) (fun R hR=>(generate_sound f n s L R hR).2)

theorem generate_complete (f : Nat→Fin σ) (n s L p e k : Nat)
    (hs : 0<s) (hSL : s≤L) (hc : Copy f n p e k) (hl : L≤e-p) :
    ∃R,R∈(generate f n s L).strips ∧ R.lo≤p ∧ e≤R.hi ∧ R.distance=k-p := by
  obtain ⟨R,hR,ha,hb,hq⟩:=IndexedGrid.generate_complete f n s p e k hs hc (by omega)
  exact ⟨R,(generate_mem f n s L R).mpr ⟨hR,by simp only [span]; omega⟩,ha,hb,hq⟩

end REWB.ResidualStripSchedule
