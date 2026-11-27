import REWB.ExactKeys

/-! Exact bounded-rank doubling for padded finite text.

Each level interns pairs of previous ranks in the verified binary trie.
Pair keys have fixed logarithmic width; the ranks are recompressed after
every level and stored in actual arrays. No probabilistic fingerprints,
unbounded mixed-radix integers, suffix oracle or sorting oracle is used. -/
namespace REWB.RankIndex
open REWB.Periodic
variable {σ : Nat}

def bits : Nat→Nat→List (Fin 2)
  | 0,_ => []
  | h+1,a => ⟨a%2,Nat.mod_lt a (by decide)⟩::bits h (a/2)

theorem bits_length (h a : Nat) : (bits h a).length=h := by
  induction h generalizing a with
  | zero => rfl
  | succ h ih => simp only [bits,List.length_cons,ih]

theorem bits_injective (h a b : Nat) (ha : a<2^h) (hb : b<2^h)
    (he : bits h a=bits h b) : a=b := by
  induction h generalizing a b with
  | zero => simp only [Nat.pow_zero] at ha hb; omega
  | succ h ih =>
    have he' := List.cons.inj he
    have hm := congrArg Fin.val he'.1
    have hpow : 2^(h+1)=2^h*2 := Nat.pow_succ _ _
    rw [hpow] at ha hb
    have hq := ih (a/2) (b/2) (by omega) (by omega) he'.2
    have h1 := Nat.mod_add_div a 2
    have h2 := Nat.mod_add_div b 2
    change a%2=b%2 at hm
    omega

def pairBits (h a b : Nat) : List (Fin 2) := bits h a++bits h b

theorem pairBits_length (h a b : Nat) : (pairBits h a b).length=2*h := by
  simp only [pairBits,List.length_append,bits_length]
  omega

theorem pairBits_exact (h a b c d : Nat)
    (ha : a<2^h) (hb : b<2^h) (hc : c<2^h) (hd : d<2^h) :
    pairBits h a b=pairBits h c d ↔ a=c ∧ b=d := by
  constructor
  · intro he
    obtain ⟨he1,he2⟩ := List.append_inj he (by simp only [bits_length])
    exact ⟨bits_injective h a c ha hc he1,bits_injective h b d hb hd he2⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def read (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0

/-- Tail-recursive batch interning preserves the existing exact trie
and its work counter while avoiding one stack frame per input key. -/
def internManyTR.go (R : ExactKeys.Registry σ)
    (acc : List (ExactKeys.KeyWord σ×Nat)) (work : Nat) :
    List (ExactKeys.KeyWord σ)→ExactKeys.Batch σ
  | [] => ⟨R,acc.reverse,work⟩
  | w::ws =>
    let a := ExactKeys.assign R w
    go a.registry ((w,a.rank)::acc) (work+a.work) ws

theorem internManyTR.go_spec (R : ExactKeys.Registry σ)
    (acc : List (ExactKeys.KeyWord σ×Nat)) (work : Nat)
    (ws : List (ExactKeys.KeyWord σ)) :
    go R acc work ws=
      ⟨(ExactKeys.internMany R ws).registry,
       acc.reverse++(ExactKeys.internMany R ws).entries,
       work+(ExactKeys.internMany R ws).work⟩ := by
  induction ws generalizing R acc work with
  | nil => simp [go,ExactKeys.internMany]
  | cons w ws ih =>
    rw [go,ih]
    simp only [ExactKeys.internMany,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc]

def internManyTR (R : ExactKeys.Registry σ) (ws : List (ExactKeys.KeyWord σ)) : ExactKeys.Batch σ :=
  internManyTR.go R [] 0 ws

@[csimp] theorem internMany_eq_internManyTR : @ExactKeys.internMany=@internManyTR := by
  funext σ R ws
  simp only [internManyTR,internManyTR.go_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

def compress (ws : List (List (Fin 2))) : ExactKeys.PhaseRanks 2 :=
  let b := ExactKeys.internMany ExactKeys.initial ws
  ⟨b.registry,(b.entries.map Prod.snd).toArray,b.work⟩

theorem compress_size (ws : List (List (Fin 2))) :
    (compress ws).ranks.size=ws.length := by
  have h := congrArg List.length (ExactKeys.internMany_words ExactKeys.initial ws)
  simp only [List.length_map] at h
  simpa only [compress,List.size_toArray,List.length_map] using h

theorem compress_get (ws : List (List (Fin 2))) (i : Nat) (w : List (Fin 2))
    (hi : ws[i]?=some w) :
    ExactKeys.lookup (compress ws).registry.tree w=some (read (compress ws).ranks i) := by
  have hw := congrArg (fun xs : List (List (Fin 2))=>xs[i]?)
    (ExactKeys.internMany_words ExactKeys.initial ws)
  change ((ExactKeys.internMany ExactKeys.initial ws).entries.map Prod.fst)[i]?=ws[i]? at hw
  rw [List.getElem?_map,hi] at hw
  cases he : (ExactKeys.internMany ExactKeys.initial ws).entries[i]? with
  | none => simp [he] at hw
  | some e =>
    have hew : e.1=w := by simpa only [he,Option.map,Option.some.injEq] using hw
    have hr : read (compress ws).ranks i=e.2 := by
      simp only [read,compress,List.getElem?_toArray,List.getElem?_map,he,Option.map,
        Option.getD_some]
    rw [hr,← hew]
    exact ExactKeys.internMany_entries ExactKeys.initial ws e (List.mem_of_getElem? he)

theorem compress_exact (ws : List (List (Fin 2))) (i j : Nat) (u v : List (Fin 2))
    (hi : ws[i]?=some u) (hj : ws[j]?=some v) :
    read (compress ws).ranks i=read (compress ws).ranks j ↔ u=v :=
  ExactKeys.rank_eq_iff _ (ExactKeys.internMany_valid _ ExactKeys.initial_valid ws)
    u v _ _ (compress_get ws i u hi) (compress_get ws j v hj)

theorem compress_bound (ws : List (List (Fin 2))) (i : Nat) (hi : i<ws.length) :
    read (compress ws).ranks i<ws.length := by
  have hx : ∃ w,ws[i]?=some w := by
    cases he : ws[i]? with
    | none => have hh := List.getElem?_eq_none_iff.mp he; omega
    | some w => exact ⟨w,rfl⟩
  obtain ⟨w,hw⟩ := hx
  have h := (ExactKeys.internMany_valid _ ExactKeys.initial_valid ws).1 w _
    (compress_get ws i w hw)
  have hb := ExactKeys.internMany_next (ExactKeys.initial : ExactKeys.Registry 2) ws
  change (ExactKeys.internMany ExactKeys.initial ws).registry.next≤0+ws.length at hb
  omega

/-- Code zero is the terminal padding symbol. Every actual symbol has
a positive code, so padding cannot collide with text. -/
def symbol (f : Nat→Fin σ) (n i : Nat) : Nat :=
  if i<n then (f i).val+1 else 0

theorem symbol_ge (f : Nat→Fin σ) (n i : Nat) (hi : n≤i) : symbol f n i=0 := by
  simp only [symbol,show ¬i<n by omega,if_false]

theorem segment_ge (f : Nat→Fin σ) (n i L : Nat) (hi : n≤i) :
    segment (symbol f n) i L=List.replicate L 0 := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih =>
    rw [segment,symbol_ge f n i hi,ih (i+1) (by omega)]
    rfl

theorem segment_cap (f : Nat→Fin σ) (n i L : Nat) :
    segment (symbol f n) (min i n) L=segment (symbol f n) i L := by
  by_cases hi : i≤n
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega),segment_ge f n n L (Nat.le_refl _),
      segment_ge f n i L (by omega)]

def capRead (row : Array Nat) (n i : Nat) : Nat := read row (min i n)

def Correct (f : Nat→Fin σ) (n L : Nat) (row : Array Nat) : Prop :=
  row.size=n+1 ∧ ∀ i j,i≤n→j≤n→
    (read row i=read row j ↔ segment (symbol f n) i L=segment (symbol f n) j L)

def Bounded (B : Nat) (row : Array Nat) : Prop :=
  ∀ i,i<row.size→read row i<B

theorem capRead_exact (f : Nat→Fin σ) (n L : Nat) (row : Array Nat)
    (h : Correct f n L row) (i j : Nat) :
    capRead row n i=capRead row n j ↔
      segment (symbol f n) i L=segment (symbol f n) j L := by
  rw [capRead,capRead,h.2 (min i n) (min j n) (Nat.min_le_right _ _) (Nat.min_le_right _ _),
    segment_cap,segment_cap]

theorem capRead_bound (n B : Nat) (row : Array Nat) (hs : row.size=n+1)
    (h : Bounded B row) (i : Nat) : capRead row n i<B := by
  apply h
  rw [hs]
  have hm := Nat.min_le_right i n
  omega

def bound (σ n : Nat) : Nat := max (n+1) (σ+1)
def width (σ n : Nat) : Nat := (bound σ n).log2+1

theorem bound_pow (σ n : Nat) : bound σ n<2^(width σ n) :=
  Nat.lt_log2_self (n:=bound σ n)

def base (f : Nat→Fin σ) (n : Nat) : Array Nat :=
  ((List.range (n+1)).map (symbol f n)).toArray

theorem base_size (f : Nat→Fin σ) (n : Nat) : (base f n).size=n+1 := by
  simp only [base,List.size_toArray,List.length_map,List.length_range]

theorem base_read (f : Nat→Fin σ) (n i : Nat) (hi : i≤n) :
    read (base f n) i=symbol f n i := by
  simp only [read,base,List.getElem?_toArray,List.getElem?_map,List.getElem?_range,
    show i<n+1 by omega,if_true,Option.map,Option.getD_some]

theorem base_correct (f : Nat→Fin σ) (n : Nat) : Correct f n 1 (base f n) := by
  refine ⟨base_size f n,?_⟩
  intro i j hi hj
  rw [base_read f n i hi,base_read f n j hj]
  simp only [segment,List.cons.injEq,and_true]

theorem base_bound (f : Nat→Fin σ) (n : Nat) : Bounded (bound σ n) (base f n) := by
  intro i hi
  rw [base_size] at hi
  rw [base_read f n i (by omega)]
  unfold symbol
  split
  · have hf := (f i).isLt
    have hm := Nat.le_max_right (n+1) (σ+1)
    change (f i).val+1<max (n+1) (σ+1)
    omega
  · have hm := Nat.le_max_left (n+1) (σ+1)
    change 0<max (n+1) (σ+1)
    omega

def keys (h n L : Nat) (row : Array Nat) : List (List (Fin 2)) :=
  (List.range (n+1)).map fun i=>pairBits h (capRead row n i) (capRead row n (i+L))

theorem keys_length (h n L : Nat) (row : Array Nat) : (keys h n L row).length=n+1 := by
  simp only [keys,List.length_map,List.length_range]

theorem keys_get (h n L : Nat) (row : Array Nat) (i : Nat) (hi : i≤n) :
    (keys h n L row)[i]?=some (pairBits h (capRead row n i) (capRead row n (i+L))) := by
  simp only [keys,List.getElem?_map,List.getElem?_range,show i<n+1 by omega,if_true,Option.map]

def double (h n L : Nat) (row : Array Nat) : ExactKeys.PhaseRanks 2 :=
  compress (keys h n L row)

theorem double_size (h n L : Nat) (row : Array Nat) :
    (double h n L row).ranks.size=n+1 := by
  rw [double,compress_size,keys_length]

theorem double_bound (h n L : Nat) (row : Array Nat) :
    Bounded (bound σ n) (double h n L row).ranks := by
  intro i hi
  rw [double_size] at hi
  have hh := compress_bound (keys h n L row) i (by rw [keys_length]; exact hi)
  have hb := Nat.le_max_left (n+1) (σ+1)
  rw [keys_length] at hh
  exact Nat.lt_of_lt_of_le hh hb

theorem double_correct (f : Nat→Fin σ) (n L : Nat) (row : Array Nat)
    (hc : Correct f n L row) (hb : Bounded (bound σ n) row) :
    Correct f n (L+L) (double (width σ n) n L row).ranks := by
  refine ⟨double_size _ _ _ _,?_⟩
  intro i j hi hj
  rw [double,compress_exact _ i j _ _ (keys_get _ _ _ _ i hi) (keys_get _ _ _ _ j hj)]
  have ht : ∀ a,capRead row n a<2^(width σ n) := fun a=>
    Nat.lt_trans (capRead_bound n (bound σ n) row hc.1 hb a) (bound_pow σ n)
  rw [pairBits_exact _ _ _ _ _ (ht i) (ht (i+L)) (ht j) (ht (j+L)),
    capRead_exact f n L row hc i j,capRead_exact f n L row hc (i+L) (j+L),
    segment_append,segment_append]
  constructor
  · rintro ⟨h1,h2⟩
    rw [h1,h2]
  · intro he
    exact List.append_inj he (by rw [segment_length,segment_length])

theorem keys_characters (h n L : Nat) (row : Array Nat) :
    ExactKeys.characters (keys h n L row)=(n+1)*(2*h) := by
  unfold keys
  rw [ExactKeys.characters_map _ _ (2*h) (fun _ _=>pairBits_length _ _ _),List.length_range]

theorem double_trieWork (h n L : Nat) (row : Array Nat) :
    (double h n L row).work≤(n+1)*(14*h+1) := by
  have hh := ExactKeys.internMany_cost (ExactKeys.initial : ExactKeys.Registry 2) (keys h n L row)
  rw [keys_characters,keys_length] at hh
  change (ExactKeys.internMany ExactKeys.initial (keys h n L row)).work≤_
  have he : (3*2+1)*((n+1)*(2*h))+(n+1)=(n+1)*(14*h+1) := by
    simp only [Nat.mul_add,Nat.mul_one]
    have he' : 7*((n+1)*(2*h))=(n+1)*(14*h) := by
      calc
        _ = (n+1)*((7*2)*h) := by ac_rfl
        _ = _ := rfl
    exact congrArg (fun x=>x+(n+1)) he'
  simpa only [he] using hh

structure Index where
  rows : Array (Array Nat)
  last : Array Nat
  block : Nat
  trieWork : Nat
  keyCells : Nat
  rankReads : Nat
  rankWrites : Nat
  deriving Repr

/-- The counter components are actual trie work, produced key cells,
previous-rank reads and stored-rank writes. Base symbol reads and the
outer level-array push occur linearly in the same schedule. -/
def build (f : Nat→Fin σ) (n : Nat) : Nat→Index
  | 0 => let a:=base f n; ⟨#[a],a,1,0,0,0,n+1⟩
  | h+1 =>
    let b:=build f n h
    let a:=double (width σ n) n b.block b.last
    ⟨b.rows.push a.ranks,a.ranks,b.block+b.block,
      b.trieWork+a.work,b.keyCells+(n+1)*(2*width σ n),
      b.rankReads+2*(n+1),b.rankWrites+(n+1)⟩

theorem build_last (f : Nat→Fin σ) (n h : Nat) :
    (build f n h).block=2^h ∧
      Correct f n (2^h) (build f n h).last ∧
      Bounded (bound σ n) (build f n h).last := by
  induction h with
  | zero => exact ⟨rfl,base_correct f n,base_bound f n⟩
  | succ h ih =>
    have hpow : 2^h+2^h=2^(h+1) := by rw [Nat.pow_succ]; omega
    have hc := double_correct f n (2^h) (build f n h).last ih.2.1 ih.2.2
    rw [hpow] at hc
    refine ⟨?_,?_,double_bound _ _ _ _⟩
    · change (build f n h).block+(build f n h).block=2^(h+1)
      rw [ih.1,hpow]
    · change Correct f n (2^(h+1))
        (double (width σ n) n (build f n h).block (build f n h).last).ranks
      rwa [ih.1]

theorem build_rows_size (f : Nat→Fin σ) (n h : Nat) : (build f n h).rows.size=h+1 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change ((build f n h).rows.push _).size=h+1+1
    rw [Array.size_push,ih]

theorem build_row (f : Nat→Fin σ) (n h k : Nat) (hk : k≤h) :
    ∃ row,(build f n h).rows[k]?=some row ∧
      Correct f n (2^k) row ∧ Bounded (bound σ n) row := by
  induction h with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact ⟨base f n,rfl,base_correct f n,base_bound f n⟩
  | succ h ih =>
    by_cases he : k=h+1
    · subst k
      refine ⟨(build f n (h+1)).last,?_,(build_last f n (h+1)).2⟩
      change ((build f n h).rows.push _)[h+1]?=
        some (double (width σ n) n (build f n h).block (build f n h).last).ranks
      rw [Array.getElem?_push,build_rows_size,if_pos rfl]
    · obtain ⟨row,hr,hc,hb⟩ := ih (by omega)
      refine ⟨row,?_,hc,hb⟩
      change ((build f n h).rows.push _)[k]?=some row
      rw [Array.getElem?_push,build_rows_size,if_neg he]
      exact hr

def rowAt (I : Index) (h : Nat) : Array Nat := I.rows[h]?.getD #[]

theorem rowAt_correct (f : Nat→Fin σ) (n h k : Nat) (hk : k≤h) :
    Correct f n (2^k) (rowAt (build f n h) k) := by
  obtain ⟨row,hr,hc,hb⟩ := build_row f n h k hk
  simpa only [rowAt,hr,Option.getD_some] using hc

theorem rowAt_bound (f : Nat→Fin σ) (n h k : Nat) (hk : k≤h) :
    Bounded (bound σ n) (rowAt (build f n h) k) := by
  obtain ⟨row,hr,hc,hb⟩ := build_row f n h k hk
  simpa only [rowAt,hr,Option.getD_some] using hb

theorem build_trieWork (f : Nat→Fin σ) (n h : Nat) :
    (build f n h).trieWork≤h*((n+1)*(14*width σ n+1)) := by
  induction h with
  | zero => simp [build]
  | succ h ih =>
    have hs := double_trieWork (width σ n) n (build f n h).block (build f n h).last
    change (build f n h).trieWork+
      (double (width σ n) n (build f n h).block (build f n h).last).work≤_
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add ih hs

theorem build_counts (f : Nat→Fin σ) (n h : Nat) :
    (build f n h).keyCells=h*((n+1)*(2*width σ n)) ∧
      (build f n h).rankReads=h*(2*(n+1)) ∧
      (build f n h).rankWrites=(h+1)*(n+1) := by
  induction h with
  | zero => simp [build]
  | succ h ih =>
    change (build f n h).keyCells+(n+1)*(2*width σ n)=_ ∧
      (build f n h).rankReads+2*(n+1)=_ ∧
      (build f n h).rankWrites+(n+1)=_
    rw [ih.1,ih.2.1,ih.2.2]
    simp [Nat.add_mul]

def Index.countedWork (I : Index) : Nat := I.trieWork+I.keyCells+I.rankReads+I.rankWrites

private theorem work_algebra (m h w : Nat) :
    h*(m*(14*w+1))+h*(m*(2*w))+h*(2*m)+(h+1)*m=m*(h*(16*w+4)+1) := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
  have h14 : h*(m*(14*w))=14*(m*(h*w)) := by ac_rfl
  have h2 : h*(m*(2*w))=2*(m*(h*w)) := by ac_rfl
  have h16 : m*(h*(16*w))=16*(m*(h*w)) := by ac_rfl
  have ha : h*m=m*h := Nat.mul_comm _ _
  have hb : h*(2*m)=2*(m*h) := by ac_rfl
  have hc : m*(h*4)=4*(m*h) := by ac_rfl
  rw [h14,h2,h16,ha,hb,hc]
  omega

theorem build_work (f : Nat→Fin σ) (n h : Nat) :
    (build f n h).countedWork≤(n+1)*(h*(16*width σ n+4)+1) := by
  have ht := build_trieWork f n h
  obtain ⟨hk,hr,hw⟩ := build_counts f n h
  unfold Index.countedWork
  rw [hk,hr,hw]
  have hcost := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right ht
    (h*((n+1)*(2*width σ n)))) (h*(2*(n+1)))) ((h+1)*(n+1))
  rwa [work_algebra] at hcost

end REWB.RankIndex
