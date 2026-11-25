import REWB.ResidualStripScheduleCuts

/-! The actual residual job list, with cached query/probe counters. The
tail-recursive implementation retains earlier immutable values and
copies only emitted job cells. Equality cells from the packing proof
never occur in this execution. -/
namespace REWB.ResidualStripSchedule
open REWB.IndexedGrid REWB.GlobalCoverage
variable {α : Type} {σ : Nat}

def collect (D L : Nat) : List Strip→Jobs
  | [] => {}
  | R::Rs =>
      let head:=one D L R
      let tail:=collect D L Rs
      let joined:=CountedProjection.append head.jobs tail.jobs
      ⟨joined.1,head.queries+tail.queries,head.probes+tail.probes,
        head.work+tail.work+joined.2+2⟩

def collectTail (D L : Nat) (acc : List Job) (queries probes work : Nat) : List Strip→Jobs
  | [] => ⟨acc.reverse,queries,probes,work+1⟩
  | R::Rs =>
      let head:=one D L R
      collectTail D L (head.jobs.reverseAux acc) (queries+head.queries) (probes+head.probes)
        (work+head.work+head.queries+3) Rs

theorem collectTail_spec (D L : Nat) (acc : List Job) (queries probes work : Nat) (Rs : List Strip) :
    collectTail D L acc queries probes work Rs=
      ⟨acc.reverse++(collect D L Rs).jobs,queries+(collect D L Rs).queries,
        probes+(collect D L Rs).probes,work+(collect D L Rs).work⟩ := by
  induction Rs generalizing acc queries probes work with
  | nil => simp [collectTail,collect]
  | cons R Rs ih =>
    rw [collectTail,ih]
    simp only [collect,List.reverseAux_eq,List.reverse_append,List.reverse_reverse,
      CountedProjection.append_value,CountedProjection.append_steps,List.append_assoc]
    rw [(local_counts D L R).1]
    congr 1 <;> omega

def collectTR (D L : Nat) (Rs : List Strip) : Jobs := collectTail D L [] 0 0 0 Rs

@[csimp] theorem collect_eq_collectTR : collect=collectTR := by
  funext D L Rs
  simp only [collectTR,collectTail_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem collect_mem (D L : Nat) (Rs : List Strip) (W : Job) :
    W∈(collect D L Rs).jobs ↔ ∃R,R∈Rs ∧ W∈(one D L R).jobs := by
  induction Rs with
  | nil => simp [collect]
  | cons R Rs ih =>
    simp only [collect,CountedProjection.append_value,List.mem_append,ih,List.mem_cons]
    constructor
    · rintro (hW|⟨S,hS,hW⟩)
      · exact ⟨R,Or.inl rfl,hW⟩
      · exact ⟨S,Or.inr hS,hW⟩
    · rintro ⟨S,(he|hS),hW⟩
      · subst S; exact Or.inl hW
      · exact Or.inr ⟨S,hS,hW⟩

theorem collect_counts (D L : Nat) (Rs : List Strip) :
    (collect D L Rs).queries=(collect D L Rs).jobs.length ∧
    (collect D L Rs).queries≤(collect D L Rs).probes+Rs.length ∧
    (collect D L Rs).work≤13*(collect D L Rs).probes+12*Rs.length+1 := by
  induction Rs with
  | nil => exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons R Rs ih =>
    have hh:=local_counts D L R
    simp only [collect,CountedProjection.append_value,CountedProjection.append_steps,
      List.length_append,List.length_cons,Nat.mul_add,Nat.mul_succ]
    omega

theorem collect_probe_mass (D L : Nat) (Rs : List Strip) (hD : 0<D)
    (ho : ∀R,R∈Rs→R.lo≤R.hi) :
    (collect D L Rs).probes*D≤2*totalSpan Rs+2*Rs.length*D := by
  induction Rs with
  | nil => simp [collect,totalSpan]
  | cons R Rs ih =>
    have hh:=local_probe_mass D L R hD (ho R List.mem_cons_self)
    have ht:=ih (fun S hS=>ho S (List.mem_cons_of_mem R hS))
    simp only [collect,totalSpan,List.length_cons,Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega

private theorem divide_extra (x a b D : Nat) (hD : 0<D) (hx : x*D≤a+b*D) :
    x≤a/D+b := by
  by_cases hb : x≤b
  · exact Nat.le_trans hb (Nat.le_add_left b (a/D))
  · have hm:=Nat.mul_le_mul_right D (by omega : b≤x)
    have hd : (x-b)*D≤a := by rw [Nat.sub_mul]; omega
    have hh:=(Nat.le_div_iff_mul_le hD).mpr hd
    omega

/-- Actual probes, including rejected edge cuts, obey the strip-area
budget. The two extra grid endpoints are charged to each distinct strip. -/
theorem collect_probes (f : Nat→α) (n D L : Nat) (Rs : List Strip) (hD : 0<D)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup) :
    (collect D L Rs).probes≤(2*n^2)/D+2*Rs.length := by
  have hh:=collect_probe_mass D L Rs hD (fun R hR=>by have h:=(hv R hR).2.1; omega)
  have hm:=Nat.mul_le_mul_left 2 (totalSpan_bound f n Rs hv hn)
  apply divide_extra _ _ _ D hD
  omega

theorem collect_queries (f : Nat→α) (n D L : Nat) (Rs : List Strip) (hD : 0<D) (hL : 0<L)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup)
    (hl : ∀R,R∈Rs→L≤span R) :
    (collect D L Rs).queries≤(2*n^2)/D+3*(n^2/L) := by
  have hp:=collect_probes f n D L Rs hD hv hn
  have hc:=collect_counts D L Rs
  have hm:=long_count f n L Rs hL hv hn hl
  omega

theorem collect_work (f : Nat→α) (n D L : Nat) (Rs : List Strip) (hD : 0<D) (hL : 0<L)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup)
    (hl : ∀R,R∈Rs→L≤span R) :
    (collect D L Rs).work≤13*((2*n^2)/D)+38*(n^2/L)+1 := by
  have hp:=collect_probes f n D L Rs hD hv hn
  have hc:=collect_counts D L Rs
  have hm:=long_count f n L Rs hL hv hn hl
  omega

structure Prepared where
  strips : Selected
  batch : Jobs
  work : Nat
  deriving Repr

def prepare (f : Nat→Fin σ) (n s L D : Nat) : Prepared :=
  let strips:=generate f n s L
  let batch:=collect D L strips.strips
  ⟨strips,batch,strips.work+batch.work+3⟩

theorem prepare_queries (f : Nat→Fin σ) (n s L D : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D).batch.queries≤(2*n^2)/D+3*(n^2/L) :=
  collect_queries f n D L _ hD hL (fun R hR=>(generate_sound f n s L R hR).1)
    (generate_nodup f n s L) (fun R hR=>(generate_sound f n s L R hR).2)

theorem prepare_length (f : Nat→Fin σ) (n s L D : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D).batch.jobs.length≤(2*n^2)/D+3*(n^2/L) := by
  change (collect D L (generate f n s L).strips).jobs.length≤_
  rw [←(collect_counts D L (generate f n s L).strips).1]
  exact prepare_queries f n s L D hD hL

end REWB.ResidualStripSchedule
