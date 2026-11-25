import REWB.MaskedTraversalDirty
import REWB.MaskedClusterDescriptorAnchor

/-! Order lemmas for the remaining structural dirty-set locality proof.
All relations refer to actual ordered-tree membership and exact neighbor
specifications. No descriptor equality or affected-key oracle is assumed.
-/
namespace REWB.MaskedTraversalNeighbor
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor
variable {h : Nat}

def Adds (before after : List Nat) (p : Nat) : Prop :=
  ∀x,x∈after↔x=p ∨ x∈before

theorem Adds.old {before after : List Nat} {p x : Nat} (ha : Adds before after p)
    (hx : x∈before) : x∈after := (ha x).mpr (Or.inr hx)

theorem Adds.away {before after : List Nat} {p x : Nat} (ha : Adds before after p)
    (hx : x≠p) : x∈after↔x∈before := by rw [ha]; simp only [hx,false_or]

theorem leader_below (before after : List Nat) (p L x : Nat) (ha : Adds before after p) (hx : x<p) :
    MaskedClusterLeaders.Leader after L x↔MaskedClusterLeaders.Leader before L x := by
  constructor
  · rintro ⟨hm,hs⟩
    refine ⟨(ha.away (by omega)).mp hm,?_⟩
    intro r hr hrx
    exact hs r (ha.old hr) hrx
  · rintro ⟨hm,hs⟩
    refine ⟨ha.old hm,?_⟩
    intro r hr hrx
    rcases (ha r).mp hr with rfl|hr
    · omega
    · exact hs r hr hrx

theorem leader_after (before after : List Nat) (p a L x : Nat) (ha : Adds before after p)
    (hm : a∈before) (hpa : p<a) (hax : a<x) :
    MaskedClusterLeaders.Leader after L x↔MaskedClusterLeaders.Leader before L x := by
  constructor
  · rintro ⟨hx,hs⟩
    refine ⟨(ha.away (by omega)).mp hx,?_⟩
    intro r hr hrx
    exact hs r (ha.old hr) hrx
  · rintro ⟨hx,hs⟩
    refine ⟨ha.old hx,?_⟩
    intro r hr hrx
    rcases (ha r).mp hr with rfl|hr
    · have hh:=hs a hm hax
      omega
    · exact hs r hr hrx

theorem leader_old (before after : List Nat) (p L x : Nat) (ha : Adds before after p) (hx : x≠p)
    (hl : MaskedClusterLeaders.Leader after L x) : MaskedClusterLeaders.Leader before L x :=
  ⟨(ha.away hx).mp hl.1,fun r hr hrx=>hl.2 r (ha.old hr) hrx⟩

theorem max_unique (xs : List Nat) (a b : Option Nat) (ha : Tree.MaxSpec xs a) (hb : Tree.MaxSpec xs b) : a=b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => change xs=[] at ha; rw [ha] at hb; cases hb.1
  | some a =>
    cases b with
    | none => change xs=[] at hb; rw [hb] at ha; cases ha.1
    | some b => congr 1; exact Nat.le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

theorem succ_spec_congr (before after : List Nat) (x : Nat) (q : Option Nat)
    (he : ∀r,x<r→(r∈after↔r∈before)) (hs : Tree.SuccSpec before x q) : Tree.SuccSpec after x q := by
  cases q with
  | none =>
    intro r hr
    by_cases hxr : x<r
    · have hh:=hs r ((he r hxr).mp hr); omega
    · omega
  | some q =>
    refine ⟨(he q hs.2.1).mpr hs.1,hs.2.1,?_⟩
    intro r hr hxr
    exact hs.2.2 r ((he r hxr).mp hr) hxr

theorem succ_spec_bounded (before after : List Nat) (x q bound : Nat)
    (he : ∀r,r<bound→(r∈after↔r∈before)) (hs : Tree.SuccSpec before x (some q))
    (hq : q<bound) : Tree.SuccSpec after x (some q) := by
  refine ⟨(he q hq).mpr hs.1,hs.2.1,?_⟩
  intro r hr hxr
  by_cases hrb : r<bound
  · exact hs.2.2 r ((he r hrb).mp hr) hxr
  · omega

theorem pred_add_below (before after : List Nat) (p x : Nat) (q : Option Nat)
    (ha : Adds before after p) (hp : x≤p) (hs : Tree.PredSpec before x q) : Tree.PredSpec after x q := by
  cases q with
  | none =>
    intro r hr
    rcases (ha r).mp hr with rfl|hr
    · exact hp
    · exact hs r hr
  | some q =>
    refine ⟨ha.old hs.1,hs.2.1,?_⟩
    intro r hr hrx
    rcases (ha r).mp hr with rfl|hr
    · omega
    · exact hs.2.2 r hr hrx

theorem pred_add_above (before after : List Nat) (p x q : Nat)
    (ha : Adds before after p) (hp : p≤q) (hs : Tree.PredSpec before x (some q)) : Tree.PredSpec after x (some q) := by
  refine ⟨ha.old hs.1,hs.2.1,?_⟩
  intro r hr hrx
  rcases (ha r).mp hr with rfl|hr
  · exact hp
  · exact hs.2.2 r hr hrx

theorem max_add_below (before after : List Nat) (p q : Nat)
    (ha : Adds before after p) (hp : p≤q) (hs : Tree.MaxSpec before (some q)) : Tree.MaxSpec after (some q) := by
  refine ⟨ha.old hs.1,?_⟩
  intro r hr
  rcases (ha r).mp hr with rfl|hr
  · exact hp
  · exact hs.2 r hr

theorem succ_add_below (before after : List Nat) (p x q : Nat)
    (ha : Adds before after p) (hp : q≤p) (hs : Tree.SuccSpec before x (some q)) : Tree.SuccSpec after x (some q) := by
  refine ⟨ha.old hs.1,hs.2.1,?_⟩
  intro r hr hxr
  rcases (ha r).mp hr with rfl|hr
  · exact hp
  · exact hs.2.2 r hr hxr

theorem succ_add_above (before after : List Nat) (p x : Nat) (q : Option Nat)
    (ha : Adds before after p) (hp : p≤x) (hs : Tree.SuccSpec before x q) : Tree.SuccSpec after x q := by
  apply succ_spec_congr before after x q _ hs
  intro r hr
  exact ha.away (by omega)

theorem around_left (t : Tree h) (capacity p x : Nat) (hg : t.Good) (hf : t.Fits 0) (hc : capacity=2^h)
    (hx : x∈t.entries) (hxp : x≤p) (hn : x∉(MaskedTraversalDirty.around t capacity p).keys) :
    ∃a b,a∈t.entries ∧ b∈t.entries ∧ x<a ∧ a<b ∧ b≤p := by
  have hl:=Tree.pred_correct t capacity (p+1) hg hf hc
  cases hb : (Tree.pred t capacity (p+1)).1 with
  | none => rw [hb] at hl; have hh:=hl x hx; omega
  | some b =>
    rw [hb] at hl
    have hxb:=hl.2.2 x hx (by omega)
    have hne : x≠b := by
      intro he
      apply hn
      simp only [MaskedTraversalDirty.Around.keys,MaskedTraversalDirty.around,hb,List.mem_append,Option.mem_toList]
      exact Or.inl (Or.inl (Or.inr (by simp [he])))
    have he:=Tree.pred_correct t capacity b hg hf hc
    cases ha : (Tree.pred t capacity b).1 with
    | none => rw [ha] at he; have hh:=he x hx; omega
    | some a =>
      rw [ha] at he
      have hxa:=he.2.2 x hx (by omega)
      have hne' : x≠a := by
        intro heq
        apply hn
        simp only [MaskedTraversalDirty.Around.keys,MaskedTraversalDirty.around,hb,
          MaskedTraversalDirty.optionalPred,ha,List.mem_append,Option.mem_toList]
        exact Or.inl (Or.inl (Or.inl (by simp [heq])))
      exact ⟨a,b,he.1,hl.1,by omega,he.2.1,Nat.lt_succ_iff.mp hl.2.1⟩

theorem around_right (t : Tree h) (capacity p x : Nat) (hg : t.Good) (hf : t.Fits 0) (hc : capacity=2^h)
    (hx : x∈t.entries) (hpx : p<x) (hn : x∉(MaskedTraversalDirty.around t capacity p).keys) :
    ∃a,a∈t.entries ∧ p<a ∧ a<x := by
  have hs:=Tree.succ_correct t capacity p hg hf hc
  cases ha : (Tree.succ t capacity p).1 with
  | none => rw [ha] at hs; have hh:=hs x hx; omega
  | some a =>
    rw [ha] at hs
    have hax:=hs.2.2 x hx hpx
    have hne : x≠a := by
      intro he
      apply hn
      simp only [MaskedTraversalDirty.Around.keys,MaskedTraversalDirty.around,ha,List.mem_append,Option.mem_toList]
      exact Or.inl (Or.inr (by simp [he]))
    exact ⟨a,hs.1,hs.2.1,by omega⟩

theorem describe_of_sound (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h) (d : Descriptor) (hd : Sound s capacity d) :
    (describeLeader s capacity d.first).1=some d := by
  have hm:=(Tree.contains_correct s.leaders capacity d.first hi.leadFits hc).mpr hd.firstLeader
  have hn:=succ_unique s.leaders.entries d.first _ d.next
    (Tree.succ_correct s.leaders capacity d.first hi.leadGood hi.leadFits hc) hd.nextSpec
  cases hnext : d.next with
  | none =>
    have hl:=max_unique s.occurrences.entries _ (some d.last)
      (Tree.last_spec s.occurrences 0 hi.occGood hi.occFits) (by simpa only [hnext] using hd.lastSpec)
    simp only [describeLeader,hm,if_true,hn,hnext,hl]
    rw [←hnext,←hd.materialized]
  | some p =>
    have hl:=pred_unique s.occurrences.entries p _ (some d.last)
      (Tree.pred_correct s.occurrences capacity p hi.occGood hi.occFits hc) (by simpa only [hnext] using hd.lastSpec)
    simp only [describeLeader,hm,if_true,hn,hnext,hl]
    rw [←hnext,←hd.materialized]

end REWB.MaskedTraversalNeighbor
