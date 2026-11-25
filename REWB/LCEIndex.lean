import REWB.RankIndex

/-! Longest-common-extension queries over the exact rank-doubling index.
The greedy descent halves the current block length at each level and
performs at most one comparison of two stored ranks per level. All
agreement statements retain explicit finite-text bounds. -/
namespace REWB.LCEIndex
open REWB.Periodic REWB.RankIndex
variable {α : Type} {σ : Nat}

def Agree (f : Nat→α) (n i j L : Nat) : Prop :=
  i+L≤n ∧ j+L≤n ∧ segment f i L=segment f j L

def IsLCE (f : Nat→α) (n i j L : Nat) : Prop :=
  Agree f n i j L ∧ ∀ k,Agree f n i j k→k≤L

theorem agree_zero (f : Nat→α) (n i j : Nat) (hi : i≤n) (hj : j≤n) :
    Agree f n i j 0 := ⟨by omega,by omega,rfl⟩

theorem agree_shorten (f : Nat→α) (n i j L k : Nat)
    (h : Agree f n i j L) (hk : k≤L) : Agree f n i j k := by
  refine ⟨by have hh:=h.1; omega,by have hh:=h.2.1; omega,?_⟩
  apply (segment_eq_points f i j k).mpr
  intro a ha
  exact (segment_eq_points f i j L).mp h.2.2 a (by omega)

theorem agree_tail (f : Nat→α) (n i j L c b : Nat)
    (h : Agree f n i j L) (hcb : c+b≤L) :
    segment f (i+c) b=segment f (j+c) b := by
  apply (segment_eq_points f (i+c) (j+c) b).mpr
  intro a ha
  have he := (segment_eq_points f i j L).mp h.2.2 (c+a) (by omega)
  simpa only [Nat.add_assoc] using he

theorem agree_extend (f : Nat→α) (n i j c b : Nat)
    (h : Agree f n i j c) (hni : i+(c+b)≤n) (hnj : j+(c+b)≤n)
    (hb : segment f (i+c) b=segment f (j+c) b) :
    Agree f n i j (c+b) := by
  refine ⟨hni,hnj,?_⟩
  rw [segment_append,segment_append,h.2.2,hb]

def blockEqual (I : Index) (n h i j : Nat) : Bool :=
  decide (capRead (rowAt I h) n i=capRead (rowAt I h) n j)

theorem blockEqual_correct (f : Nat→Fin σ) (n H h i j : Nat) (hh : h≤H) :
    blockEqual (build f n H) n h i j=true ↔
      segment (symbol f n) i (2^h)=segment (symbol f n) j (2^h) := by
  rw [blockEqual,decide_eq_true_eq,
    capRead_exact f n (2^h) (rowAt (build f n H) h) (rowAt_correct f n H h hh) i j]

/-- Return the extension length and the actual number of rank-pair
comparisons. `block` is carried explicitly, so no power is recomputed
inside the descent. -/
def go (I : Index) (n i j limit : Nat) : Nat→Nat→Nat→Nat×Nat
  | 0,_,c => (c,0)
  | h+1,block,c =>
    let half:=block/2
    if c+half≤limit then
      let same:=blockEqual I n h (i+c) (j+c)
      let r:=go I n i j limit h half (if same then c+half else c)
      (r.1,r.2+1)
    else go I n i j limit h half c

theorem go_queries (I : Index) (n i j limit h block c : Nat) :
    (go I n i j limit h block c).2≤h := by
  induction h generalizing block c with
  | zero => exact Nat.le_refl _
  | succ h ih =>
    rw [go]
    split
    · exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.le_trans (ih _ _) (by omega)

/-- The descent invariant is an agreed prefix c and a strict upper
bound c+2^h for every possible answer. A failed block comparison lowers
that upper bound; a successful one extends the actual agreed prefix. -/
theorem go_correct (f : Nat→Fin σ) (n H i j h c : Nat)
    (hh : h≤H)
    (hc : Agree (symbol f n) n i j c)
    (hmax : ∀ k,Agree (symbol f n) n i j k→k<c+2^h) :
    IsLCE (symbol f n) n i j
      (go (build f n H) n i j (min (n-i) (n-j)) h (2^h) c).1 := by
  induction h generalizing c with
  | zero =>
    refine ⟨hc,?_⟩
    intro k hk
    have hb := hmax k hk
    simp only [Nat.pow_zero] at hb
    change k≤c
    omega
  | succ h ih =>
    have hpow : 2^(h+1)=2^h*2 := Nat.pow_succ _ _
    have hhalf : 2^(h+1)/2=2^h := by rw [hpow,Nat.mul_div_cancel _ (by decide : 0<2)]
    rw [go,hhalf]
    by_cases hfit : c+2^h≤min (n-i) (n-j)
    · rw [if_pos hfit]
      by_cases heq : blockEqual (build f n H) n h (i+c) (j+c)=true
      · simp only [heq,ite_true]
        have hblock := (blockEqual_correct f n H h (i+c) (j+c) (by omega)).mp heq
        have hi := hc.1
        have hj := hc.2.1
        have hnew := agree_extend (symbol f n) n i j c (2^h) hc
          (by omega) (by omega) hblock
        exact ih (c+2^h) (by omega) hnew (by
          intro k hk
          have hm := hmax k hk
          rw [hpow] at hm
          omega)
      · have heq' : blockEqual (build f n H) n h (i+c) (j+c)=false := by
          cases ht : blockEqual (build f n H) n h (i+c) (j+c)
          · rfl
          · exact False.elim (heq ht)
        simp only [heq',Bool.false_eq_true,if_false]
        apply ih c (by omega) hc
        intro k hk
        by_cases hb : k<c+2^h
        · exact hb
        · have hblock := agree_tail (symbol f n) n i j k c (2^h) hk (by omega)
          exact False.elim (heq ((blockEqual_correct f n H h (i+c) (j+c) (by omega)).mpr hblock))
    · rw [if_neg hfit]
      apply ih c (by omega) hc
      intro k hk
      have hi := hk.1
      have hj := hk.2.1
      omega

def query (I : Index) (n H i j : Nat) : Nat×Nat :=
  go I n i j (min (n-i) (n-j)) H I.block 0

theorem query_correct (f : Nat→Fin σ) (n H i j : Nat)
    (hi : i≤n) (hj : j≤n) (hH : n<2^H) :
    IsLCE (symbol f n) n i j (query (build f n H) n H i j).1 := by
  unfold query
  rw [(build_last f n H).1]
  apply go_correct f n H i j H 0 (Nat.le_refl _) (agree_zero _ _ _ _ hi hj)
  intro k hk
  have hh := hk.1
  omega

theorem query_rankReads (f : Nat→Fin σ) (n H i j : Nat) :
    2*(query (build f n H) n H i j).2≤2*H :=
  Nat.mul_le_mul_left 2 (go_queries _ _ _ _ _ _ _ _)

/-- In-bounds padded-code equality is exactly original-symbol equality. -/
theorem symbol_equal (f : Nat→Fin σ) (n i j : Nat) (hi : i<n) (hj : j<n) :
    symbol f n i=symbol f n j ↔ f i=f j := by
  simp only [symbol,hi,hj,if_true]
  constructor
  · intro he
    apply Fin.ext
    omega
  · intro he
    rw [he]

theorem agree_symbol (f : Nat→Fin σ) (n i j L : Nat) :
    Agree (symbol f n) n i j L ↔ Agree f n i j L := by
  constructor
  · rintro ⟨hi,hj,he⟩
    refine ⟨hi,hj,(segment_eq_points f i j L).mpr ?_⟩
    intro a ha
    exact (symbol_equal f n (i+a) (j+a) (by omega) (by omega)).mp
      ((segment_eq_points (symbol f n) i j L).mp he a ha)
  · rintro ⟨hi,hj,he⟩
    refine ⟨hi,hj,(segment_eq_points (symbol f n) i j L).mpr ?_⟩
    intro a ha
    exact (symbol_equal f n (i+a) (j+a) (by omega) (by omega)).mpr
      ((segment_eq_points f i j L).mp he a ha)

theorem query_text_correct (f : Nat→Fin σ) (n H i j : Nat)
    (hi : i≤n) (hj : j≤n) (hH : n<2^H) :
    IsLCE f n i j (query (build f n H) n H i j).1 := by
  have hh := query_correct f n H i j hi hj hH
  exact ⟨(agree_symbol f n i j _).mp hh.1,
    fun k hk=>hh.2 k ((agree_symbol f n i j k).mpr hk)⟩

def height (n : Nat) : Nat := n.log2+1

def prepare (f : Nat→Fin σ) (n : Nat) : Index := build f n (height n)
def lce (I : Index) (n i j : Nat) : Nat×Nat := query I n (height n) i j

theorem lce_correct (f : Nat→Fin σ) (n i j : Nat) (hi : i≤n) (hj : j≤n) :
    IsLCE f n i j (lce (prepare f n) n i j).1 :=
  query_text_correct f n (height n) i j hi hj (Nat.lt_log2_self (n:=n))

theorem lce_rankReads (f : Nat→Fin σ) (n i j : Nat) :
    2*(lce (prepare f n) n i j).2≤2*(n.log2+1) := query_rankReads f n (height n) i j

theorem prepare_work (f : Nat→Fin σ) (n : Nat) :
    (prepare f n).countedWork≤(n+1)*((n.log2+1)*(16*width σ n+4)+1) :=
  build_work f n (height n)

def reverseText (f : Nat→α) (n i : Nat) : α := f (n-1-i)

theorem reverse_segment (f : Nat→α) (n a L : Nat) (ha : a+L≤n) :
    segment (reverseText f n) a L=(segment f (n-a-L) L).reverse := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    rw [segment,ih (a+1) (by omega)]
    have hstart : n-(a+1)-L=n-a-(L+1) := by omega
    rw [hstart]
    have hlast : n-a-(L+1)+L=n-1-a := by omega
    have hs := segment_append f (n-a-(L+1)) L 1
    rw [hlast] at hs
    rw [hs,List.reverse_append]
    simp only [segment,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.singleton_append,reverseText]

def SuffixAgree (f : Nat→α) (e k L : Nat) : Prop :=
  L≤e ∧ L≤k ∧ segment f (e-L) L=segment f (k-L) L

def IsLCS (f : Nat→α) (e k L : Nat) : Prop :=
  SuffixAgree f e k L ∧ ∀ t,SuffixAgree f e k t→t≤L

theorem suffix_iff_reverse (f : Nat→α) (n e k L : Nat) (he : e≤n) (hk : k≤n) :
    SuffixAgree f e k L ↔ Agree (reverseText f n) n (n-e) (n-k) L := by
  constructor
  · rintro ⟨hLe,hLk,heq⟩
    refine ⟨by omega,by omega,?_⟩
    rw [reverse_segment f n (n-e) L (by omega),
      reverse_segment f n (n-k) L (by omega),
      show n-(n-e)-L=e-L by omega,show n-(n-k)-L=k-L by omega,heq]
  · rintro ⟨hLe,hLk,heq⟩
    refine ⟨by omega,by omega,?_⟩
    rw [reverse_segment f n (n-e) L hLe,reverse_segment f n (n-k) L hLk,
      show n-(n-e)-L=e-L by omega,show n-(n-k)-L=k-L by omega] at heq
    simpa only [List.reverse_reverse] using congrArg List.reverse heq

def prepareReverse (f : Nat→Fin σ) (n : Nat) : Index := prepare (reverseText f n) n
def lcs (I : Index) (n e k : Nat) : Nat×Nat := lce I n (n-e) (n-k)

theorem lcs_correct (f : Nat→Fin σ) (n e k : Nat) (he : e≤n) (hk : k≤n) :
    IsLCS f e k (lcs (prepareReverse f n) n e k).1 := by
  have hh := lce_correct (reverseText f n) n (n-e) (n-k) (by omega) (by omega)
  exact ⟨(suffix_iff_reverse f n e k _ he hk).mpr hh.1,
    fun t ht=>hh.2 t ((suffix_iff_reverse f n e k t he hk).mp ht)⟩

theorem lcs_rankReads (f : Nat→Fin σ) (n e k : Nat) :
    2*(lcs (prepareReverse f n) n e k).2≤2*(n.log2+1) :=
  lce_rankReads (reverseText f n) n (n-e) (n-k)

theorem prepareReverse_work (f : Nat→Fin σ) (n : Nat) :
    (prepareReverse f n).countedWork≤(n+1)*((n.log2+1)*(16*width σ n+4)+1) :=
  prepare_work (reverseText f n) n

structure QueryResult where
  length : Nat
  pairs : Nat
  levels : Nat
  deriving Repr

/-- Count loop visits even when the remaining block does not fit.
The two data-dependent counters are incremented in the same descent;
there is no subsequent recount or scan. -/
def walk (I : Index) (n i j limit : Nat) : Nat→Nat→Nat→QueryResult
  | 0,_,c => ⟨c,0,0⟩
  | h+1,block,c =>
    let half:=block/2
    if c+half≤limit then
      let same:=blockEqual I n h (i+c) (j+c)
      let r:=walk I n i j limit h half (if same then c+half else c)
      ⟨r.length,r.pairs+1,r.levels+1⟩
    else
      let r:=walk I n i j limit h half c
      ⟨r.length,r.pairs,r.levels+1⟩

theorem walk_value (I : Index) (n i j limit h block c : Nat) :
    ((walk I n i j limit h block c).length,(walk I n i j limit h block c).pairs)=
      go I n i j limit h block c := by
  induction h generalizing block c with
  | zero => rfl
  | succ h ih =>
    simp only [walk,go]
    split
    · have hh:=ih (block/2) (if blockEqual I n h (i+c) (j+c) then c+block/2 else c)
      have h1:=congrArg Prod.fst hh
      have h2:=congrArg Prod.snd hh
      exact Prod.ext h1 (congrArg (fun x=>x+1) h2)
    · have hh:=ih (block/2) c
      exact hh

theorem walk_levels (I : Index) (n i j limit h block c : Nat) :
    (walk I n i j limit h block c).levels=h := by
  induction h generalizing block c with
  | zero => rfl
  | succ h ih =>
    simp only [walk]
    split <;> exact congrArg (fun x=>x+1) (ih _ _)

theorem walk_pairs (I : Index) (n i j limit h block c : Nat) :
    (walk I n i j limit h block c).pairs≤h := by
  have he:=congrArg Prod.snd (walk_value I n i j limit h block c)
  dsimp only at he
  rw [he]
  exact go_queries I n i j limit h block c

/-- A scalar accounting convention: six unit scalar slots per visited
level, four per rank-pair test, and one final return. Array reads are
kept separately: one level-row lookup plus two rank cells per test.
These counters describe the stated abstract operations, not Lean VM
instruction counts or allocator behavior. -/
def QueryResult.scalarWork (r : QueryResult) : Nat := 6*r.levels+4*r.pairs+1
def QueryResult.arrayReads (r : QueryResult) : Nat := 3*r.pairs
def QueryResult.countedWork (r : QueryResult) : Nat := r.scalarWork+r.arrayReads

theorem walk_work (I : Index) (n i j limit h block c : Nat) :
    (walk I n i j limit h block c).countedWork≤13*h+1 := by
  have hp:=walk_pairs I n i j limit h block c
  have hl:=walk_levels I n i j limit h block c
  unfold QueryResult.countedWork QueryResult.scalarWork QueryResult.arrayReads
  rw [hl]
  omega

def lceMeasured (I : Index) (n i j : Nat) : QueryResult :=
  walk I n i j (min (n-i) (n-j)) (height n) I.block 0

def lcsMeasured (I : Index) (n e k : Nat) : QueryResult :=
  lceMeasured I n (n-e) (n-k)

theorem lceMeasured_value (I : Index) (n i j : Nat) :
    ((lceMeasured I n i j).length,(lceMeasured I n i j).pairs)=lce I n i j :=
  walk_value I n i j (min (n-i) (n-j)) (height n) I.block 0

theorem lceMeasured_correct (f : Nat→Fin σ) (n i j : Nat) (hi : i≤n) (hj : j≤n) :
    IsLCE f n i j (lceMeasured (prepare f n) n i j).length := by
  have he:=congrArg Prod.fst (lceMeasured_value (prepare f n) n i j)
  dsimp only at he
  rw [he]
  exact lce_correct f n i j hi hj

theorem lcsMeasured_correct (f : Nat→Fin σ) (n e k : Nat) (he : e≤n) (hk : k≤n) :
    IsLCS f e k (lcsMeasured (prepareReverse f n) n e k).length := by
  have hh:=congrArg Prod.fst (lceMeasured_value (prepareReverse f n) n (n-e) (n-k))
  dsimp only at hh
  change IsLCS f e k (lceMeasured (prepareReverse f n) n (n-e) (n-k)).length
  rw [hh]
  exact lcs_correct f n e k he hk

theorem lceMeasured_levels (I : Index) (n i j : Nat) :
    (lceMeasured I n i j).levels=n.log2+1 :=
  walk_levels I n i j (min (n-i) (n-j)) (height n) I.block 0

theorem lceMeasured_work (I : Index) (n i j : Nat) :
    (lceMeasured I n i j).countedWork≤13*(n.log2+1)+1 :=
  walk_work I n i j (min (n-i) (n-j)) (height n) I.block 0

theorem lcsMeasured_work (I : Index) (n e k : Nat) :
    (lcsMeasured I n e k).countedWork≤13*(n.log2+1)+1 :=
  lceMeasured_work I n (n-e) (n-k)

end REWB.LCEIndex
