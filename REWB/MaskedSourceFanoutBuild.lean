import REWB.MaskedSourceFanout

/-! Exact reverse lookup and duplicate-free source fanout. Reference lists
are used only in specifications, never by the materialized builder. -/
namespace REWB.MaskedSourceFanout
open REWB.RunGeometry REWB.MaskedPeriodic.Batch
variable {σ : Nat}

def memberIds : List Bounds→Nat→Nat→List Nat
  | [],_,_ => []
  | R::Rs,id,p =>
    let rest:=memberIds Rs (id+1) p
    if R.lo≤p ∧ p<R.lo+span R then rest++[id] else rest

theorem loop_read (Rs : List Bounds) (id p : Nat) (out : Built)
    (hb : ∀ R,R∈Rs → R.lo+span R≤out.rows.size) :
    read (loop Rs id out).rows p=
      ⟨memberIds Rs id p++(read out.rows p).ids,
        (memberIds Rs id p).length+(read out.rows p).count⟩ := by
  induction Rs generalizing id out with
  | nil => simp [loop,memberIds]
  | cons R Rs ih =>
    have ht : ∀ S,S∈Rs → S.lo+span S≤
        (fill id (span R) R.lo {out with work:=out.work+3}).rows.size := by
      intro S hS
      rw [fill_size]
      exact hb S (List.mem_cons_of_mem R hS)
    rw [loop,ih (id+1) _ ht,fill_read id (span R) R.lo p
      {out with work:=out.work+3} (hb R List.mem_cons_self)]
    by_cases hp : R.lo≤p ∧ p<R.lo+span R
    · simp [memberIds,hp,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [memberIds,hp]

theorem read_replicate (n p : Nat) : read (Array.replicate n ({} : Cell)) p={} := by
  unfold read
  rw [Array.getElem?_replicate]
  split <;> rfl

theorem build_read (n p : Nat) (Rs : List Bounds)
    (hb : ∀ R,R∈Rs → R.lo≤R.hi ∧ R.hi≤n) :
    read (build n Rs).rows p=⟨memberIds Rs 0 p,(memberIds Rs 0 p).length⟩ := by
  have hh : ∀ R,R∈Rs → R.lo+span R≤(Array.replicate (n+1) ({} : Cell)).size := by
    intro R hR
    have hr:=hb R hR
    simp only [Array.size_replicate,span]
    omega
  rw [build,loop_read Rs 0 p _ hh,read_replicate]
  simp

theorem memberIds_mem (Rs : List Bounds) (id p k : Nat) :
    k∈memberIds Rs id p ↔
      ∃ R,(R,k)∈Rs.zipIdx id ∧ R.lo≤p ∧ p<R.lo+span R := by
  induction Rs generalizing id with
  | nil => simp [memberIds]
  | cons R Rs ih =>
    change k∈(if R.lo≤p ∧ p<R.lo+span R then memberIds Rs (id+1) p++[id]
      else memberIds Rs (id+1) p) ↔ _
    by_cases hp : R.lo≤p ∧ p<R.lo+span R
    · rw [if_pos hp,List.mem_append,List.mem_singleton,ih]
      simp only [List.zipIdx_cons,List.mem_cons]
      constructor
      · rintro (⟨S,hS,hs⟩|hk)
        · exact ⟨S,Or.inr hS,hs⟩
        · subst k
          exact ⟨R,Or.inl rfl,hp⟩
      · rintro ⟨S,hS,hs⟩
        rcases hS with he|ht
        · cases he
          exact Or.inr rfl
        · exact Or.inl ⟨S,ht,hs⟩
    · rw [if_neg hp,ih]
      simp only [List.zipIdx_cons,List.mem_cons]
      constructor
      · rintro ⟨S,hS,hs⟩
        exact ⟨S,Or.inr hS,hs⟩
      · rintro ⟨S,hS,hs⟩
        rcases hS with he|ht
        · cases he
          exact False.elim (hp hs)
        · exact ⟨S,ht,hs⟩

theorem memberIds_lower (Rs : List Bounds) (id p k : Nat) (hk : k∈memberIds Rs id p) :
    id≤k := by
  obtain ⟨R,hR,_⟩:=(memberIds_mem Rs id p k).mp hk
  exact List.le_snd_of_mem_zipIdx hR

theorem memberIds_nodup (Rs : List Bounds) (id p : Nat) : (memberIds Rs id p).Nodup := by
  induction Rs generalizing id with
  | nil => simp [memberIds]
  | cons R Rs ih =>
    simp only [memberIds]
    split
    · change (memberIds Rs (id+1) p++[id]).Pairwise (fun a b=>a≠b)
      rw [List.pairwise_append]
      refine ⟨ih (id+1),by simp,?_⟩
      intro a ha b hb
      have hge:=memberIds_lower Rs (id+1) p a ha
      have he : b=id := List.mem_singleton.mp hb
      omega
    · exact ih (id+1)

theorem build_mem (n p k : Nat) (Rs : List Bounds)
    (hb : ∀ R,R∈Rs → R.lo≤R.hi ∧ R.hi≤n) :
    k∈(read (build n Rs).rows p).ids ↔
      ∃ R,Rs[k]?=some R ∧ R.lo≤p ∧ p≤R.hi := by
  rw [build_read n p Rs hb,memberIds_mem]
  constructor
  · rintro ⟨R,hr,hlo,hhi⟩
    have hm:=List.fst_mem_of_mem_zipIdx hr
    have hR:=hb R hm
    refine ⟨R,List.mk_mem_zipIdx_iff_getElem?.mp hr,hlo,?_⟩
    unfold span at hhi
    omega
  · rintro ⟨R,hr,hlo,hhi⟩
    have hz : (R,k)∈Rs.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hr
    have hR:=hb R (List.fst_mem_of_mem_zipIdx hz)
    refine ⟨R,hz,hlo,?_⟩
    unfold span
    omega

theorem build_count (n p : Nat) (Rs : List Bounds)
    (hb : ∀ R,R∈Rs → R.lo≤R.hi ∧ R.hi≤n) :
    (read (build n Rs).rows p).count=(read (build n Rs).rows p).ids.length := by
  rw [build_read n p Rs hb]

theorem build_nodup (n p : Nat) (Rs : List Bounds)
    (hb : ∀ R,R∈Rs → R.lo≤R.hi ∧ R.hi≤n) :
    (read (build n Rs).rows p).ids.Nodup := by
  rw [build_read n p Rs hb]
  exact memberIds_nodup Rs 0 p

end REWB.MaskedSourceFanout
