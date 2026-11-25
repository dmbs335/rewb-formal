import REWB.ExactKeys
import REWB.P1Target
import REWB.SmallPeriodRuns

/-! Exact full-word keys for P1 inner copies shorter than three periods.
    Each run materializes one rank for every phase, residual length, and
    quotient m < 3. Later target events perform one array read and do
    not construct or traverse the keyed word again.

    The initial registry is arbitrary: source substrings may be interned
    first. All prior IDs and all run-table IDs remain valid in the common
    final registry. Counters are the executable trie counters from
    ExactKeys, not a complete machine-level cost model. -/
namespace REWB.P1ShortKeys
open REWB.Periodic REWB.RunGeometry REWB.ExactKeys
variable {σ : Nat}

def word (s : Nat→Fin σ) (q phase rho m : Nat) : KeyWord σ :=
  P1Target.keyWord (segment s phase q) rho m

def index (q phase rho m : Nat) : Nat := (phase*q+rho)*3+m

theorem index_lt (q phase rho m : Nat)
    (hp : phase<q) (hr : rho<q) (hm : m<3) : index q phase rho m<q*q*3 := by
  have hbase : phase*q+rho<q*q := by
    calc
      phase*q+rho < phase*q+q := Nat.add_lt_add_left hr _
      _ = (phase+1)*q := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ q*q := Nat.mul_le_mul_right q (by omega)
  calc
    index q phase rho m < (phase*q+rho)*3+3 := Nat.add_lt_add_left hm _
    _ = (phase*q+rho+1)*3 := by omega
    _ ≤ q*q*3 := Nat.mul_le_mul_right 3 (by omega)

theorem index_div_three (q phase rho m : Nat) (hm : m<3) :
    index q phase rho m/3=phase*q+rho := by
  unfold index
  rw [Nat.add_comm _ m,Nat.add_mul_div_right m _ (by decide),Nat.div_eq_of_lt hm,Nat.zero_add]

theorem index_decode (q phase rho m : Nat) (hr : rho<q) (hm : m<3) :
    index q phase rho m/3/q=phase ∧
    (index q phase rho m/3)%q=rho ∧ index q phase rho m%3=m := by
  have hq : 0<q := by omega
  rw [index_div_three q phase rho m hm]
  refine ⟨?_,?_,?_⟩
  · rw [Nat.add_comm _ rho,Nat.add_mul_div_right rho phase hq,Nat.div_eq_of_lt hr,Nat.zero_add]
  · rw [Nat.add_comm _ rho,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr]
  · unfold index
    rw [Nat.add_comm _ m,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hm]

/-- The mixed-radix ordering is phase, then residue, then m. -/
def words (s : Nat→Fin σ) (q : Nat) : List (KeyWord σ) :=
  (List.range (q*q*3)).map (fun i=>word s q (i/3/q) ((i/3)%q) (i%3))

theorem words_length (s : Nat→Fin σ) (q : Nat) : (words s q).length=3*q^2 := by
  simp only [words,List.length_map,List.length_range,Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  ac_rfl

theorem words_get (s : Nat→Fin σ) (q phase rho m : Nat)
    (hp : phase<q) (hr : rho<q) (hm : m<3) :
    (words s q)[index q phase rho m]?=some (word s q phase rho m) := by
  obtain ⟨hphase,hrho,hm'⟩ := index_decode q phase rho m hr hm
  simp only [words,List.getElem?_map,List.getElem?_range (index_lt q phase rho m hp hr hm),
    Option.map,hphase,hrho,hm']

theorem word_length (s : Nat→Fin σ) (q phase rho m : Nat) (hr : rho≤q) :
    (word s q phase rho m).length=m*q+rho := by
  simp only [word,P1Target.keyWord,List.length_append,repeatWord_length,segment_length,
    List.length_take,Nat.min_eq_left hr]

theorem word_length_le (s : Nat→Fin σ) (q phase rho m : Nat) (hm : m<3) :
    (word s q phase rho m).length≤3*q := by
  simp only [word,P1Target.keyWord,List.length_append,repeatWord_length,segment_length,
    List.length_take]
  have hmul := Nat.mul_le_mul_right q (show m≤2 by omega)
  have hmin := Nat.min_le_right rho q
  omega

theorem characters_map_le {X : Type} (f : X→KeyWord σ) (xs : List X) (c : Nat)
    (h : ∀ x,x∈xs→(f x).length≤c) : characters (xs.map f)≤xs.length*c := by
  induction xs with
  | nil => simp [characters]
  | cons x xs ih =>
    change (f x).length+characters (xs.map f)≤(xs.length+1)*c
    rw [Nat.add_mul,Nat.one_mul]
    have hx := h x (by simp)
    have hs := ih (fun y hy=>h y (by simp [hy]))
    omega

theorem words_characters (s : Nat→Fin σ) (q : Nat) :
    characters (words s q)≤9*q^3 := by
  have h := characters_map_le
    (fun i=>word s q (i/3/q) ((i/3)%q) (i%3)) (List.range (q*q*3)) (3*q)
    (fun i _=>word_length_le s q _ _ _ (Nat.mod_lt _ (by decide)))
  rw [List.length_range] at h
  change characters (words s q)≤(q*q*3)*(3*q) at h
  have he : (q*q*3)*(3*q)=9*q^3 := by
    rw [show (9:Nat)=3*3 by decide]
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  rwa [he] at h

def workConstant (σ : Nat) : Nat := 9*(3*σ+1)

structure PhaseRanks (σ : Nat) where
  registry : Registry σ
  ranks : Array Nat
  work : Nat

def internShorts (R : Registry σ) (s : Nat→Fin σ) (q : Nat) : PhaseRanks σ :=
  let b := internMany R (words s q)
  ⟨b.registry,(b.entries.map Prod.snd).toArray,b.work⟩

theorem internShorts_size (R : Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (internShorts R s q).ranks.size=3*q^2 := by
  have h := congrArg List.length (internMany_words R (words s q))
  simp only [List.length_map,words_length] at h
  simpa only [internShorts,List.size_toArray,List.length_map] using h

theorem internShorts_get (R : Registry σ) (s : Nat→Fin σ) (q phase rho m : Nat)
    (hp : phase<q) (hr : rho<q) (hm : m<3) :
    ∃ r,(internShorts R s q).ranks[index q phase rho m]?=some r ∧
      lookup (internShorts R s q).registry.tree (word s q phase rho m)=some r := by
  have hw := congrArg (fun ws : List (KeyWord σ)=>ws[index q phase rho m]?)
    (internMany_words R (words s q))
  dsimp only at hw
  rw [List.getElem?_map,words_get s q phase rho m hp hr hm] at hw
  cases he : (internMany R (words s q)).entries[index q phase rho m]? with
  | none => simp [he] at hw
  | some e =>
    have hew : e.1=word s q phase rho m := by
      simpa only [he,Option.map,Option.some.injEq] using hw
    refine ⟨e.2,?_,?_⟩
    · simp only [internShorts,List.getElem?_toArray,List.getElem?_map,he,Option.map]
    · change lookup (internMany R (words s q)).registry.tree (word s q phase rho m)=some e.2
      rw [← hew]
      exact internMany_entries R _ e (List.mem_of_getElem? he)

theorem internShorts_preserves (R : Registry σ) (s : Nat→Fin σ) (q : Nat)
    (v : KeyWord σ) (r : Nat) (hr : lookup R.tree v=some r) :
    lookup (internShorts R s q).registry.tree v=some r :=
  internMany_preserves R (words s q) v r hr

theorem internShorts_valid (R : Registry σ) (hR : R.Valid) (s : Nat→Fin σ) (q : Nat) :
    (internShorts R s q).registry.Valid := internMany_valid R hR (words s q)

theorem internShorts_next (R : Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (internShorts R s q).registry.next≤R.next+3*q^2 := by
  have h := internMany_next R (words s q)
  rwa [words_length] at h

theorem internShorts_cost (R : Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (internShorts R s q).work≤workConstant σ*q^3+3*q^2 := by
  have h := internMany_cost R (words s q)
  rw [words_length] at h
  calc
    _ ≤ (3*σ+1)*characters (words s q)+3*q^2 := h
    _ ≤ (3*σ+1)*(9*q^3)+3*q^2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (words_characters s q)) _
    _ = _ := by unfold workConstant; ac_rfl

structure RunTables (σ : Nat) where
  registry : Registry σ
  tables : List (Bounds×Array Nat)
  work : Nat

def buildRunTables (R : Registry σ) (f : Nat→Fin σ) : List Bounds→RunTables σ
  | [] => ⟨R,[],0⟩
  | run::runs =>
    let a := internShorts R (shift f run.lo) run.period
    let b := buildRunTables a.registry f runs
    ⟨b.registry,(run,a.ranks)::b.tables,a.work+b.work⟩

theorem buildRunTables_preserves (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds)
    (v : KeyWord σ) (r : Nat) (hr : lookup R.tree v=some r) :
    lookup (buildRunTables R f runs).registry.tree v=some r := by
  induction runs generalizing R with
  | nil => exact hr
  | cons run runs ih => exact ih _ (internShorts_preserves R _ _ v r hr)

theorem buildRunTables_valid (R : Registry σ) (hR : R.Valid) (f : Nat→Fin σ)
    (runs : List Bounds) : (buildRunTables R f runs).registry.Valid := by
  induction runs generalizing R with
  | nil => exact hR
  | cons run runs ih => exact ih _ (internShorts_valid R hR _ _)

theorem buildRunTables_runs (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds) :
    (buildRunTables R f runs).tables.map Prod.fst=runs := by
  induction runs generalizing R with
  | nil => rfl
  | cons run runs ih =>
    change run::(buildRunTables _ f runs).tables.map Prod.fst=run::runs
    rw [ih]

theorem buildRunTables_sizes (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds) :
    ∀ e,e∈(buildRunTables R f runs).tables→e.2.size=3*e.1.period^2 := by
  induction runs generalizing R with
  | nil => intro e he; simp [buildRunTables] at he
  | cons run runs ih =>
    intro e he
    change e∈(run,(internShorts R (shift f run.lo) run.period).ranks)::
      (buildRunTables _ f runs).tables at he
    rcases List.mem_cons.mp he with he|he
    · subst e
      exact internShorts_size R _ _
    · exact ih _ e he

/-- Every table refers to the final shared registry, including tables
    built before later runs were processed. -/
theorem buildRunTables_exact (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds) :
    ∀ e,e∈(buildRunTables R f runs).tables→∀ phase rho m,
      phase<e.1.period→rho<e.1.period→m<3→
      ∃ r,e.2[index e.1.period phase rho m]?=some r ∧
        lookup (buildRunTables R f runs).registry.tree
          (word (shift f e.1.lo) e.1.period phase rho m)=some r := by
  induction runs generalizing R with
  | nil => intro e he; simp [buildRunTables] at he
  | cons run runs ih =>
    intro e he phase rho m hp hr hm
    change e∈(run,(internShorts R (shift f run.lo) run.period).ranks)::
      (buildRunTables _ f runs).tables at he
    rcases List.mem_cons.mp he with he|he
    · subst e
      obtain ⟨r,hget,hlookup⟩ := internShorts_get R (shift f run.lo) run.period phase rho m hp hr hm
      exact ⟨r,hget,buildRunTables_preserves _ f runs _ r hlookup⟩
    · exact ih _ e he phase rho m hp hr hm

def tableRank (run : Bounds) (ranks : Array Nat) (phase rho m : Nat) : Option Nat :=
  ranks[index run.period phase rho m]?

theorem buildRunTables_rank (R : Registry σ) (hR : R.Valid) (f : Nat→Fin σ)
    (runs : List Bounds) (e : Bounds×Array Nat) (he : e∈(buildRunTables R f runs).tables)
    (phase rho m : Nat) (hp : phase<e.1.period) (hr : rho<e.1.period) (hm : m<3) :
    ∃ r,tableRank e.1 e.2 phase rho m=some r ∧
      r<(buildRunTables R f runs).registry.next ∧
      lookup (buildRunTables R f runs).registry.tree
        (word (shift f e.1.lo) e.1.period phase rho m)=some r := by
  obtain ⟨r,hget,hlookup⟩ := buildRunTables_exact R f runs e he phase rho m hp hr hm
  exact ⟨r,hget,(buildRunTables_valid R hR f runs).1 _ r hlookup,hlookup⟩

theorem buildRunTables_cost (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds) :
    (buildRunTables R f runs).work≤
      workConstant σ*RunBudget.phaseWork 2 runs+3*RunBudget.phaseWork 1 runs := by
  induction runs generalizing R with
  | nil => simp [buildRunTables,RunBudget.phaseWork]
  | cons run runs ih =>
    have ha := internShorts_cost R (shift f run.lo) run.period
    have hb := ih (internShorts R (shift f run.lo) run.period).registry
    change (internShorts R (shift f run.lo) run.period).work+
      (buildRunTables _ f runs).work≤_
    simp only [RunBudget.phaseWork,Nat.mul_add,show (2:Nat)+1=3 from rfl,
      show (1:Nat)+1=2 from rfl]
    omega

theorem buildRunTables_next (R : Registry σ) (f : Nat→Fin σ) (runs : List Bounds) :
    (buildRunTables R f runs).registry.next≤R.next+3*RunBudget.phaseWork 1 runs := by
  induction runs generalizing R with
  | nil => simp [buildRunTables,RunBudget.phaseWork]
  | cons run runs ih =>
    have ha := internShorts_next R (shift f run.lo) run.period
    have hb := ih (internShorts R (shift f run.lo) run.period).registry
    change (buildRunTables (internShorts R (shift f run.lo) run.period).registry f runs).registry.next≤_
    simp only [RunBudget.phaseWork,Nat.mul_add,show (1:Nat)+1=2 from rfl]
    omega

theorem buildRunTables_cubic_cost (R : Registry σ) (f : Nat→Fin σ) (n Q : Nat)
    (runs : List Bounds) (hd : runs.Nodup) (hv : ∀ r,r∈runs→r.Valid f n)
    (hc : ∀ r,r∈runs→r.period≤Q ∧ 3*r.period≤r.hi-r.lo) :
    (buildRunTables R f runs).work≤
      (workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n) := by
  have h2 := RunBudget.cubic_phase_bound f n 2 Q runs hd hv hc
  have h1 := RunBudget.cubic_phase_bound f n 1 Q runs hd hv hc
  simp only [Nat.pow_one] at h1
  calc
    _ ≤ workConstant σ*RunBudget.phaseWork 2 runs+3*RunBudget.phaseWork 1 runs :=
      buildRunTables_cost R f runs
    _ ≤ workConstant σ*(Q^2*(2*n*DyadicIndex.heightFor n))+
        3*(Q*(2*n*DyadicIndex.heightFor n)) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ h1)
    _ = _ := by rw [Nat.add_mul]; simp only [Nat.mul_assoc]

theorem concrete_cost (R : Registry σ) (f : Nat→Fin σ) (n Q : Nat) :
    (buildRunTables R f (SmallPeriodRuns.cubic f n Q)).work≤
      (workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n) :=
  buildRunTables_cubic_cost R f n Q _ (SmallPeriodRuns.cubic_nodup f n Q)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).1)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).2)

theorem concrete_next (R : Registry σ) (f : Nat→Fin σ) (n Q : Nat) :
    (buildRunTables R f (SmallPeriodRuns.cubic f n Q)).registry.next≤
      R.next+3*Q*(2*n*DyadicIndex.heightFor n) := by
  have h := buildRunTables_next R f (SmallPeriodRuns.cubic f n Q)
  have hp := SmallPeriodRuns.cubic_phase_bound f n Q 1
  simp only [Nat.pow_one] at hp
  have hh := Nat.add_le_add_left (Nat.mul_le_mul_left 3 hp) R.next
  simpa only [Nat.mul_assoc] using Nat.le_trans h hh

end REWB.P1ShortKeys
