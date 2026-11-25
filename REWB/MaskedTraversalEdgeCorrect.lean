import REWB.MaskedTraversalEdge

/-! Correctness of actual compressed-edge bands.  The theorem quantifies
over every integer length in a band, and the same occurrence tree is used
on both sides of every queue drain.  No supplied threshold list is used. -/
namespace REWB.MaskedTraversalEdge
open REWB.MaskedClusterLeaders
variable {h : Nat}

theorem future_mono (old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (hf : Future old s) (hle : fresh≤old) : Future fresh s := by
  intro edge he event hev hk
  exact hf edge he event hev (by omega)

theorem invariant_between (capacity old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant old s) (hf : Future old s) (hc : capacity=2^h)
    (hle : fresh≤old) (hclean : Clean fresh s) : Invariant fresh s := by
  refine ⟨hi.occGood,hi.occFits,hi.leadGood,hi.leadFits,?_,hi.queueGood⟩
  intro p
  constructor
  · intro hp
    exact leader_shorten _ old fresh p hle ((hi.represented p).mp hp)
  · intro hp
    apply (hi.represented p).mpr
    by_cases hold : Leader s.occurrences.entries old p
    · exact hold
    · obtain ⟨e,he,_,_⟩:=changed_leader_record capacity old fresh p s hi hf hc hp hold
      have hx:=(MaskedThresholdEvents.shorten_correct (h+1) fresh s.occurrences capacity
        s.queue hi.occGood hi.occFits hc hi.queueGood e).mp he
      have hk:=hclean e hx.1
      have hge:=hx.2.1
      omega

/-- Both actual adjacency threshold kinds (density and overlap) retain
their side of the cutoff throughout a band. -/
theorem threshold_between (old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (hf : Future old s) (hle : fresh≤old) (hclean : Clean fresh s)
    (edge : MaskedEventBudget.Edge) (he : edge∈MaskedEventBudget.edges s.occurrences.entries)
    (event : MaskedEventBudget.Threshold) (hev : event∈MaskedEventBudget.thresholds edge) :
    (event.level<fresh ↔ event.level<old) := by
  constructor
  · omega
  · intro hk
    exact hclean _ (hf edge he event hev hk)

inductive Chain : Nat→Nat→List (Band h)→Prop where
  | nil (floor : Nat) : Chain floor floor []
  | cons {floor cut high : Nat} {b : Band h} {bs : List (Band h)}
      (hhi : b.hi=high) (hlo : b.lo=cut+1) (hl : floor≤cut) (hh : cut<high)
      (tail : Chain floor cut bs) : Chain floor high (b::bs)

theorem Chain.coverage {floor high length : Nat} {bs : List (Band h)}
    (hc : Chain floor high bs) :
    (∃ b,b∈bs ∧ b.lo≤length ∧ length≤b.hi) ↔ floor<length ∧ length≤high := by
  induction hc with
  | nil => simp
  | @cons cut high b bs hhi hlo hl hh tail ih =>
    constructor
    · rintro ⟨a,ha,hal,hah⟩
      rcases List.mem_cons.mp ha with rfl|ha
      · rw [hhi] at hah
        rw [hlo] at hal
        omega
      · have ht:=ih.mp ⟨a,ha,hal,hah⟩
        omega
    · rintro ⟨hlength,hh_length⟩
      by_cases hcut : cut<length
      · exact ⟨b,List.mem_cons_self,by omega,by omega⟩
      · obtain ⟨a,ha,hal,hah⟩:=ih.mpr ⟨hlength,by omega⟩
        exact ⟨a,List.mem_cons_of_mem b ha,hal,hah⟩

theorem Chain.bounds {floor high : Nat} {bs : List (Band h)}
    (hc : Chain floor high bs) {b : Band h} (hb : b∈bs) :
    floor<b.lo ∧ b.lo≤b.hi ∧ b.hi≤high := by
  induction hc with
  | nil => simp at hb
  | @cons cut high a bs hhi hlo hl hh tail ih =>
    rcases List.mem_cons.mp hb with rfl|hb
    · omega
    · have ht:=ih hb
      omega

theorem Chain.unique {floor high length : Nat} {bs : List (Band h)}
    (hc : Chain floor high bs) {a b : Band h}
    (ha : a∈bs) (hb : b∈bs) (hal : a.lo≤length) (hah : length≤a.hi)
    (hbl : b.lo≤length) (hbh : length≤b.hi) : a=b := by
  induction hc generalizing a b with
  | nil => simp at ha
  | @cons cut high x xs hhi hlo hl hh tail ih =>
    rcases List.mem_cons.mp ha with rfl|hat
    · rcases List.mem_cons.mp hb with rfl|hbt
      · rfl
      · have ht:=tail.bounds hbt
        omega
    · rcases List.mem_cons.mp hb with rfl|hbt
      · have ht:=tail.bounds hat
        omega
      · exact ih hat hbt hal hah hbl hbh

structure Band.Valid (capacity : Nat) (origin : MaskedOrdered.Tree h) (b : Band h) : Prop where
  bounds : b.lo≤b.hi
  occurrences : b.snapshot.occurrences=origin
  invariant : Invariant b.hi b.snapshot
  future : Future b.hi b.snapshot
  clean : Clean b.lo b.snapshot
  crossing : b.crossing=shorten capacity (b.lo-1) b.snapshot

theorem Band.Valid.at {capacity length : Nat} {origin : MaskedOrdered.Tree h} {b : Band h}
    (hv : b.Valid capacity origin) (hc : capacity=2^h) (hl : b.lo≤length) (hh : length≤b.hi) :
    Invariant length b.snapshot ∧ Future length b.snapshot ∧ Clean length b.snapshot := by
  have hclean : Clean length b.snapshot := by
    intro e he
    have hk:=hv.clean e he
    omega
  exact ⟨invariant_between capacity b.hi length b.snapshot hv.invariant hv.future hc hh hclean,
    future_mono b.hi length b.snapshot hv.future hh,hclean⟩

structure Path.Valid (capacity floor high : Nat) (origin : MaskedOrdered.Tree h) (out : Path h) : Prop where
  invariant : Invariant floor out.state
  future : Future floor out.state
  clean : Clean floor out.state
  occurrences : out.state.occurrences=origin
  chain : Chain floor high out.bands
  bands : ∀ b,b∈out.bands → b.Valid capacity origin

theorem walk_valid (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hle : floor≤high) (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h)
    (hclean : Clean high s) :
    (walk capacity floor high s).Valid capacity floor high s.occurrences := by
  induction high using Nat.strongRecOn generalizing s with
  | ind high ih =>
    by_cases hh : floor<high
    · let boundary:=next floor high s
      let crossing:=shorten capacity boundary.length s
      have hlt : boundary.length<high := next_lt floor high s hh
      have hge : floor≤boundary.length := next_ge floor high s hh
      have hsi:=shorten_invariant capacity high boundary.length s hi hf hc (by omega)
      have hsf:=shorten_future capacity high boundary.length s hi hf (by omega)
      have hsc:=shorten_clean capacity high boundary.length s hi
      have ht:=ih boundary.length hlt crossing.state hge hsi hsf hsc
      have hn:=next_spec capacity floor high s hh hi hclean
      rw [walk,dif_pos hh]
      change Path.Valid capacity floor high s.occurrences
        ⟨(walk capacity floor boundary.length crossing.state).state,
          ⟨boundary.length+1,high,s,crossing⟩::(walk capacity floor boundary.length crossing.state).bands,
          _,_⟩
      refine ⟨ht.invariant,ht.future,ht.clean,ht.occurrences,?_,?_⟩
      · exact Chain.cons rfl rfl hge hlt ht.chain
      · intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        · refine ⟨?_,rfl,hi,hf,?_,?_⟩
          · change boundary.length+1≤high
            omega
          · intro e he
            have hk:=hn.1 e he
            change e.key≤boundary.length at hk
            change e.key<boundary.length+1
            omega
          · simp only [Nat.add_sub_cancel]
            rfl
        · exact ht.bands b hb
    · have heq : high=floor := by omega
      subst high
      rw [walk,dif_neg (Nat.lt_irrefl floor)]
      exact ⟨hi,hf,hclean,rfl,Chain.nil floor,by intro b hb; simp at hb⟩

theorem walk_occurrences (capacity floor high : Nat) (s : MaskedClusterLeaders.State h) :
    (walk capacity floor high s).state.occurrences=s.occurrences := by
  induction high using Nat.strongRecOn generalizing s with
  | ind high ih =>
    rw [walk]
    split
    · exact ih _ (next_lt floor high s ‹_›) _
    · rfl

theorem run_valid (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hh : floor<high) (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h) :
    (run capacity floor high s).path.Valid capacity floor high s.occurrences := by
  have hs:=walk_valid capacity floor high (shorten capacity high s).state (by omega)
    (shorten_invariant capacity high high s hi hf hc (Nat.le_refl _))
    (shorten_future capacity high high s hi hf (Nat.le_refl _)) hc
    (shorten_clean capacity high high s hi)
  simp only [run,if_pos hh]
  exact ⟨hs.invariant,hs.future,hs.clean,hs.occurrences,hs.chain,hs.bands⟩

theorem run_occurrences (capacity floor high : Nat) (s : MaskedClusterLeaders.State h) :
    (run capacity floor high s).path.state.occurrences=s.occurrences := by
  simp only [run]
  split
  · exact walk_occurrences capacity floor high _
  · rfl

end REWB.MaskedTraversalEdge
