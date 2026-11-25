import REWB.P1GlobalJoin
import REWB.ExactKeys
import REWB.CachedP1

/-! Short P1 source records are ordinary text factors, even when they
    have no periodic run. Their exact full-word identifiers are interned
    once; the chronological join then uses a constant true formula. -/
namespace REWB.P1ShortSources
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
variable {σ : Nat}

abbrev Token := Nat×Nat

/-- Enumerate starts and lengths below a supplied strict bound. -/
def choices (n B : Nat) : List Token :=
  ((List.range (n+1)).flatMap fun i=>(List.range B).map fun L=>(i,L)).filter
    (fun v=>decide (v.1+v.2≤n))

theorem choices_mem (n B i L : Nat) :
    (i,L)∈choices n B ↔ i≤n ∧ L<B ∧ i+L≤n := by
  rw [choices,List.mem_filter]
  constructor
  · rintro ⟨hm,hb⟩
    obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨b,hb',he⟩ := List.mem_map.mp hm
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨by have h := List.mem_range.mp ha; omega,List.mem_range.mp hb',of_decide_eq_true hb⟩
  · rintro ⟨hi,hL,hib⟩
    refine ⟨List.mem_flatMap.mpr ⟨i,List.mem_range.mpr (by omega),?_⟩,by simpa using hib⟩
    exact List.mem_map.mpr ⟨L,List.mem_range.mpr hL,rfl⟩

theorem choices_bound (n B : Nat) : (choices n B).length≤(n+1)*B := by
  have flat : ∀ xs : List Nat,
      (xs.flatMap (fun i=>(List.range B).map fun L=>(i,L))).length=xs.length*B := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_range,
        ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold choices
  apply Nat.le_trans (List.length_filter_le _ _)
  rw [flat,List.length_range]
  exact Nat.le_refl _

def cells : List Token→Nat
  | [] => 0
  | v::vs => v.2+cells vs

theorem cells_bound (vs : List Token) (B : Nat) (h : ∀ v,v∈vs→v.2≤B) :
    cells vs≤B*vs.length := by
  induction vs with
  | nil => simp [cells]
  | cons v vs ih =>
    have hv := h v (by simp)
    have hs := ih (fun z hz=>h z (by simp [hz]))
    change v.2+cells vs≤B*(vs.length+1)
    rw [Nat.mul_succ]
    omega

theorem choices_cells (n B : Nat) : cells (choices n B)≤B*((n+1)*B) := by
  apply Nat.le_trans (cells_bound (choices n B) B ?_)
  · exact Nat.mul_le_mul_left B (choices_bound n B)
  · intro v hv
    have h := (choices_mem n B v.1 v.2).mp hv
    omega

structure KeyBatch (σ : Nat) where
  registry : ExactKeys.Registry σ
  entries : List (Token×Nat)
  work : Nat

/-- Keep only the source coordinates and assigned rank, never a copy of
    the key word in the event list. -/
def buildKeys (R : ExactKeys.Registry σ) (f : Nat→Fin σ) : List Token→KeyBatch σ
  | [] => ⟨R,[],0⟩
  | v::vs =>
    let a := ExactKeys.assign R (segment f v.1 v.2)
    let b := buildKeys a.registry f vs
    ⟨b.registry,(v,a.rank)::b.entries,a.work+b.work⟩

private def buildKeysLoop (f : Nat→Fin σ) : ExactKeys.Registry σ→List Token→
    List (Token×Nat)→Nat→KeyBatch σ
  | R,[],rev,cost => ⟨R,rev.reverse,cost⟩
  | R,v::vs,rev,cost =>
    let a := ExactKeys.assign R (segment f v.1 v.2)
    buildKeysLoop f a.registry vs ((v,a.rank)::rev) (cost+a.work)

private theorem buildKeysLoop_eq (f : Nat→Fin σ) (R : ExactKeys.Registry σ)
    (vs : List Token) (rev : List (Token×Nat)) (cost : Nat) :
    buildKeysLoop f R vs rev cost=
      ⟨(buildKeys R f vs).registry,rev.reverse++(buildKeys R f vs).entries,
        cost+(buildKeys R f vs).work⟩ := by
  induction vs generalizing R rev cost with
  | nil => simp [buildKeysLoop,buildKeys]
  | cons v vs ih =>
    rw [buildKeysLoop,ih]
    simp only [buildKeys,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc]

def buildKeysTR (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token) : KeyBatch σ :=
  buildKeysLoop f R vs [] 0

/-- Registry state flows forward through a tail loop; emitted coordinates
    are reversed once. This avoids stack depth proportional to nQ. -/
@[csimp] theorem buildKeys_eq_buildKeysTR : @buildKeys=@buildKeysTR := by
  funext σ R f vs
  rw [buildKeysTR,buildKeysLoop_eq]
  simp only [List.reverse_nil,List.nil_append,Nat.zero_add]

theorem buildKeys_preserves (R : ExactKeys.Registry σ) (f : Nat→Fin σ)
    (vs : List Token) (word : Word (Fin σ)) (rank : Nat)
    (h : ExactKeys.lookup R.tree word=some rank) :
    ExactKeys.lookup (buildKeys R f vs).registry.tree word=some rank := by
  induction vs generalizing R with
  | nil => exact h
  | cons v vs ih =>
    exact ih _ (ExactKeys.assign_preserves R (segment f v.1 v.2) word rank h)

theorem buildKeys_valid (R : ExactKeys.Registry σ) (hR : R.Valid)
    (f : Nat→Fin σ) (vs : List Token) : (buildKeys R f vs).registry.Valid := by
  induction vs generalizing R with
  | nil => exact hR
  | cons v vs ih => exact ih _ (ExactKeys.assign_valid R hR (segment f v.1 v.2))

theorem buildKeys_tokens (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token) :
    (buildKeys R f vs).entries.map Prod.fst=vs := by
  induction vs generalizing R with
  | nil => rfl
  | cons v vs ih =>
    change v::(buildKeys _ f vs).entries.map Prod.fst=v::vs
    rw [ih]

theorem buildKeys_exact (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token)
    (e : Token×Nat) (he : e∈(buildKeys R f vs).entries) :
    ExactKeys.lookup (buildKeys R f vs).registry.tree (segment f e.1.1 e.1.2)=some e.2 := by
  induction vs generalizing R with
  | nil => simp [buildKeys] at he
  | cons v vs ih =>
    change e∈(v,(ExactKeys.assign R (segment f v.1 v.2)).rank)::
      (buildKeys (ExactKeys.assign R (segment f v.1 v.2)).registry f vs).entries at he
    rcases List.mem_cons.mp he with he|he
    · subst e
      exact buildKeys_preserves _ f vs _ _ (ExactKeys.assign_lookup R (segment f v.1 v.2))
    · exact ih _ he

theorem buildKeys_covers (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token)
    (v : Token) (hv : v∈vs) : ∃ rank,(v,rank)∈(buildKeys R f vs).entries := by
  rw [← buildKeys_tokens R f vs] at hv
  obtain ⟨e,he,hv⟩ := List.mem_map.mp hv
  exact ⟨e.2,by simpa only [← hv] using he⟩

theorem buildKeys_cost (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token) :
    (buildKeys R f vs).work≤(3*σ+1)*cells vs+vs.length := by
  induction vs generalizing R with
  | nil => simp [buildKeys,cells]
  | cons v vs ih =>
    have h1 := ExactKeys.intern_cost (segment f v.1 v.2) R.tree R.next
    rw [segment_length] at h1
    have h2 := ih (ExactKeys.assign R (segment f v.1 v.2)).registry
    change (ExactKeys.assign R (segment f v.1 v.2)).work+(buildKeys _ f vs).work≤
      (3*σ+1)*(v.2+cells vs)+(vs.length+1)
    change (ExactKeys.assign R (segment f v.1 v.2)).work≤(3*σ+1)*v.2+1 at h1
    rw [Nat.mul_add]
    omega

theorem buildKeys_next (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (vs : List Token) :
    (buildKeys R f vs).registry.next≤R.next+vs.length := by
  induction vs generalizing R with
  | nil => simp [buildKeys]
  | cons v vs ih =>
    have h1 := ExactKeys.intern_next_le (segment f v.1 v.2) R.tree R.next
    have h2 := ih (ExactKeys.assign R (segment f v.1 v.2)).registry
    change (ExactKeys.assign R (segment f v.1 v.2)).registry.next≤R.next+1 at h1
    change (buildKeys (ExactKeys.assign R (segment f v.1 v.2)).registry f vs).registry.next≤
      R.next+(vs.length+1)
    omega

def trueEntry (pos rank : Nat) : TimedJoin.TimedEntry := ⟨pos,⟨rank,[[]]⟩⟩

def prefixOK (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P) (i : Nat) : Bool :=
  P.A.final (BoundaryContexts.prefixAt P I i)

theorem prefixOK_correct (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n i : Nat)
    (hi : i≤n) :
    prefixOK P (BoundaryContexts.build P (segment f 0 n)).1 i=true ↔
      P.A.accepts (segment f 0 i) := by
  unfold prefixOK
  rw [BoundaryContexts.prefixAt_correct P (segment f 0 n) i (by rwa [segment_length]),
    SmallPeriodP2.segment_take f 0 n i hi]
  rfl

def sourceEvents (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (Token×Nat)) : List TimedJoin.TimedEntry :=
  (es.filter (fun e=>prefixOK P I e.1.1)).map fun e=>trueEntry (e.1.1+e.1.2) e.2

theorem sourceEvents_mem (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (Token×Nat)) (e : TimedJoin.TimedEntry) :
    e∈sourceEvents P I es ↔ ∃ z,z∈es ∧ prefixOK P I z.1.1=true ∧
      trueEntry (z.1.1+z.1.2) z.2=e := by
  simp only [sourceEvents,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hp⟩,he⟩
    exact ⟨z,hz,hp,he⟩
  · rintro ⟨z,hz,hp,he⟩
    exact ⟨z,⟨hz,hp⟩,he⟩

theorem sourceEvents_bound (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (Token×Nat)) : (sourceEvents P I es).length≤es.length := by
  simpa only [sourceEvents,List.length_map] using List.length_filter_le
    (fun e : Token×Nat=>prefixOK P I e.1.1) es

theorem trueEntry_good (pos rank K : Nat) :
    ExponentIntervals.Compatible K (trueEntry pos rank).entry.formula := by
  intro C hC a ha
  have hC' : C=[] := by simpa only [trueEntry,List.mem_singleton] using hC
  subst C
  simp at ha

theorem trueEntry_satisfies (pos rank : Nat) (env : List Int) :
    Satisfies (trueEntry pos rank).entry.formula env :=
  ⟨[],by simp [trueEntry],by intro a ha; simp at ha⟩

theorem sourceEvents_good (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (Token×Nat)) (K : Nat) : TimedJoin.Good K (sourceEvents P I es) := by
  intro e he
  obtain ⟨z,_,_,rfl⟩ := (sourceEvents_mem P I es e).mp he
  exact trueEntry_good _ _ _

theorem sourceEvents_weight (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (Token×Nat)) :
    TimedJoin.weight (sourceEvents P I es)=(sourceEvents P I es).length := by
  have aux : ∀ xs : List (Token×Nat),
      TimedJoin.weight (xs.map (fun e=>trueEntry (e.1.1+e.1.2) e.2))=xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons e es ih =>
      change 1+TimedJoin.weight (es.map (fun e=>trueEntry (e.1.1+e.1.2) e.2))=es.length+1
      omega
  unfold sourceEvents
  rw [aux,List.length_map]

theorem sourceEvents_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n B : Nat)
    (R : ExactKeys.Registry σ) (e : TimedJoin.TimedEntry)
    (he : e∈sourceEvents P (BoundaryContexts.build P (segment f 0 n)).1
      (buildKeys R f (choices n B)).entries) :
    ∃ i L,i+L≤n ∧ L<B ∧ e.pos=i+L ∧ e.entry.formula=[[]] ∧
      P.A.accepts (segment f 0 i) ∧
      ExactKeys.lookup (buildKeys R f (choices n B)).registry.tree
        (segment f i L)=some e.entry.key := by
  obtain ⟨z,hz,hp,rfl⟩ := (sourceEvents_mem P _ _ e).mp he
  have hm : z.1∈choices n B := by
    rw [← buildKeys_tokens R f (choices n B)]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  obtain ⟨hi,hL,hn⟩ := (choices_mem n B z.1.1 z.1.2).mp hm
  exact ⟨z.1.1,z.1.2,hn,hL,rfl,rfl,(prefixOK_correct P f n z.1.1 hi).mp hp,
    buildKeys_exact R f (choices n B) z hz⟩

theorem sourceEvents_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n B i L : Nat)
    (R : ExactKeys.Registry σ) (hn : i+L≤n) (hL : L<B)
    (hA : P.A.accepts (segment f 0 i)) :
    ∃ rank,trueEntry (i+L) rank∈sourceEvents P (BoundaryContexts.build P (segment f 0 n)).1
      (buildKeys R f (choices n B)).entries ∧
      ExactKeys.lookup (buildKeys R f (choices n B)).registry.tree
        (segment f i L)=some rank := by
  have hi : i≤n := by omega
  obtain ⟨rank,hr⟩ := buildKeys_covers R f (choices n B) (i,L)
    ((choices_mem n B i L).mpr ⟨hi,hL,hn⟩)
  refine ⟨rank,?_,buildKeys_exact R f (choices n B) ((i,L),rank) hr⟩
  exact (sourceEvents_mem P _ _ _).mpr
    ⟨((i,L),rank),hr,(prefixOK_correct P f n i hi).mpr hA,rfl⟩

theorem sourceEvents_positions (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n B : Nat)
    (R : ExactKeys.Registry σ) :
    ∀ e,e∈sourceEvents P (BoundaryContexts.build P (segment f 0 n)).1
      (buildKeys R f (choices n B)).entries→e.pos≤n := by
  intro e he
  obtain ⟨i,L,hn,_,he,_,_,_⟩ := sourceEvents_sound P f n B R e he
  rwa [he]

theorem generated_source_cost (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (n Q : Nat) :
    (buildKeys R f (choices n (3*Q))).work≤
      ((3*σ+1)*(3*Q)+1)*((n+1)*(3*Q)) := by
  apply Nat.le_trans (buildKeys_cost R f (choices n (3*Q)))
  have h := Nat.add_le_add
    (Nat.mul_le_mul_left (3*σ+1) (choices_cells n (3*Q))) (choices_bound n (3*Q))
  simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] using h

end REWB.P1ShortSources
