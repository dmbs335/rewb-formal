import REWB.Microblock

/-! Two-level direct-addressed range products for a fixed text and changing
    Boolean masks. The dictionaries and macro routing are shared. A column
    selects one dictionary entry per block and builds a macro product index.
    A query reads at most two local intervals and one macro interval. -/
namespace REWB.BlockIndex
open REWB.RangeProducts
open REWB.Spec (slice)
variable {M α : Type}

def count (n b : Nat) : Nat := n / b + 1
def stop (n b i : Nat) : Nat := min ((i+1)*b) n
def len (n b i : Nat) : Nat := stop n b i - i*b

def block (w : List α) (b i : Nat) : List α :=
  slice w (i*b) (stop w.length b i)

theorem start_le (n b i : Nat) (hi : i<count n b) : i*b≤n := by
  have hh : i≤n/b := by unfold count at hi; omega
  exact Nat.le_trans (Nat.mul_le_mul_right b hh) (Nat.div_mul_le_self n b)

theorem start_stop (n b i : Nat) (hi : i<count n b) : i*b≤stop n b i := by
  unfold stop
  exact Nat.le_min.mpr ⟨Nat.mul_le_mul_right b (by omega),start_le n b i hi⟩

theorem stop_le (n b i : Nat) : stop n b i≤n := Nat.min_le_right _ _

theorem block_length (w : List α) (b i : Nat) (hi : i<count w.length b) :
    (block w b i).length=len w.length b i :=
  OuterColumn.slice_length w _ _ (start_stop _ _ _ hi) (stop_le _ _ _)

theorem len_le (n b i : Nat) : len n b i≤b := by
  have h : stop n b i≤(i+1)*b := Nat.min_le_left _ _
  unfold len
  rw [Nat.add_mul,Nat.one_mul] at h
  omega

def bits (m : Nat→Bool) (off : Nat) : Nat→List Bool
  | 0 => []
  | k+1 => m off :: bits m (off+1) k

theorem bits_decorated (m : Nat→Bool) (off : Nat) (w : List α) :
    (IndexedMarked.decorate m off w).map Prod.snd=bits m off w.length := by
  induction w generalizing off with
  | nil => rfl
  | cons c cs ih =>
    change m off :: (IndexedMarked.decorate m (off+1) cs).map Prod.snd =
      m off :: bits m (off+1) cs.length
    rw [ih]

private theorem map_take {X Y : Type} (f : X→Y) (xs : List X) (k : Nat) :
    (xs.map f).take k=(xs.take k).map f := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      change f x :: (xs.map f).take k=f x :: (xs.take k).map f
      rw [ih]

private theorem map_drop {X Y : Type} (f : X→Y) (xs : List X) (k : Nat) :
    (xs.map f).drop k=(xs.drop k).map f := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs => exact ih xs

theorem map_slice {X Y : Type} (f : X→Y) (xs : List X) (l r : Nat) :
    slice (xs.map f) l r=(slice xs l r).map f := by
  simp only [slice,map_drop,map_take]

def word (f : α × Bool→M) (w : List α) (m : Nat→Bool) : List M :=
  (IndexedMarked.decorate m 0 w).map f

theorem word_length (f : α × Bool→M) (w : List α) (m : Nat→Bool) :
    (word f w m).length=w.length := by
  simp only [word,List.length_map,IndexedMarked.decorate_length]

theorem block_word (f : α × Bool→M) (w : List α) (m : Nat→Bool) (b i : Nat) :
    block (word f w m) b i =
      (IndexedMarked.decorate m (i*b) (block w b i)).map f := by
  unfold block word
  rw [List.length_map,IndexedMarked.decorate_length,map_slice,IndexedMarked.decorate_slice]

structure Shared (M : Type) where
  n : Nat
  width : Nat
  dicts : Array (Microblock.Dictionary M)
  routes : Array (Array FlatIndex.Route)

def prepare (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat) : Shared M :=
  ⟨w.length,b,
    OuterTables.tabulate (count w.length b) (fun i=>Microblock.dictionary o f (block w b i)),
    FlatIndex.buildRoutes (count w.length b)⟩

abbrev Local (M : Type) := Array (Array M)

/-- Selection does not reconstruct the dictionary. Only a mask code is
    computed; the resulting local range table is reused by all queries. -/
def choose (S : Shared M) (m : Nat→Bool) (i : Nat) : Local M :=
  ((S.dicts[i]?).bind (fun d=>Microblock.select d
    (bits m (i*S.width) (len S.n S.width i)))).getD #[]

theorem choose_correct (o : Ops M) (f : α × Bool→M) (w : List α)
    (b : Nat) (m : Nat→Bool) (i : Nat) (hi : i<count w.length b) :
    choose (prepare o f w b) m i=Microblock.buildRanges o (block (word f w m) b i) := by
  unfold choose prepare
  rw [OuterTables.tabulate_get _ _ i hi]
  change (Microblock.select (Microblock.dictionary o f (block w b i))
    (bits m (i*b) (len w.length b i))).getD #[]=_
  rw [← block_length w b i hi,← bits_decorated]
  have h := Microblock.select_actual o f (IndexedMarked.decorate m (i*b) (block w b i))
  simp only [show (IndexedMarked.decorate m (i*b) (block w b i)).map Prod.fst=block w b i
    from IndexedMarked.decorate_text m (i*b) (block w b i)] at h
  rw [h,block_word]
  rfl

structure Column (M : Type) where
  locals : Array (Local M)
  middleIndex : Array (FlatIndex.Entry M)

/-- Macro word enumeration; no traversal of the original text is needed
    when selecting the macro cells from the local tables. -/
def positions (off : Nat) : Nat→List Nat
  | 0 => []
  | k+1 => off::positions (off+1) k

theorem positions_length (off k : Nat) : (positions off k).length=k := by
  induction k generalizing off with
  | zero => rfl
  | succ k ih => change (positions (off+1) k).length+1=k+1; rw [ih]

theorem positions_mem (off k i : Nat) (hi : i∈positions off k) :
    off≤i ∧ i<off+k := by
  induction k generalizing off with
  | zero => simp [positions] at hi
  | succ k ih =>
    change i∈off::positions (off+1) k at hi
    rcases List.mem_cons.mp hi with h|h
    · subst i; omega
    · have hh := ih (off+1) h; omega

theorem positions_drop (off k i : Nat) :
    (positions off k).drop i=positions (off+i) (k-i) := by
  induction i generalizing off k with
  | zero => simp only [List.drop_zero,Nat.add_zero,Nat.sub_zero]
  | succ i ih =>
    cases k with
    | zero => simp [positions]
    | succ k =>
      change (positions (off+1) k).drop i=positions (off+(i+1)) (k+1-(i+1))
      rw [ih,show off+1+i=off+(i+1) by omega,show k+1-(i+1)=k-i by omega]

theorem positions_take (off k i : Nat) (hi : i≤k) :
    (positions off k).take i=positions off i := by
  induction i generalizing off k with
  | zero => rfl
  | succ i ih =>
    cases k with
    | zero => omega
    | succ k =>
      change off :: (positions (off+1) k).take i=off::positions (off+1) i
      rw [ih _ _ (by omega)]

theorem positions_slice (k i j : Nat) (hij : i≤j) (hj : j≤k) :
    slice (positions 0 k) i j=positions i (j-i) := by
  unfold slice
  rw [positions_drop,Nat.zero_add,positions_take _ _ _ (by omega)]

def localAt (o : Ops M) (locals : Array (Local M)) (i l r : Nat) : Option M :=
  (locals[i]?).bind (fun tab=>Microblock.rangeAt tab l r)

def macroWord (o : Ops M) (S : Shared M) (locals : Array (Local M)) : List M :=
  (positions 0 (count S.n S.width)).map (fun i=>
    (localAt o locals i 0 (len S.n S.width i)).getD o.one)

def buildColumn (o : Ops M) (S : Shared M) (m : Nat→Bool) : Column M :=
  let locals := OuterTables.tabulate (count S.n S.width) (choose S m)
  ⟨locals,FlatIndex.build o (macroWord o S locals)⟩

theorem local_correct (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat)
    (m : Nat→Bool) (i l r : Nat) (hi : i<count w.length b)
    (hl : l≤r) (hr : r≤len w.length b i) :
    localAt o (buildColumn o (prepare o f w b) m).locals i l r =
      some (product o (slice (block (word f w m) b i) l r)) := by
  unfold localAt
  change ((OuterTables.tabulate (count w.length b) (choose (prepare o f w b) m))[i]?).bind _=_
  rw [OuterTables.tabulate_get _ _ i hi]
  change Microblock.rangeAt (choose (prepare o f w b) m i) l r=_
  rw [choose_correct o f w b m i hi]
  apply Microblock.rangeAt_correct
  · exact hl
  · have he := word_length f w m
    rw [block_length _ _ _ (by rwa [he]),he]
    exact hr

private theorem map_congr_on {X Y : Type} (xs : List X) (f g : X→Y)
    (h : ∀ x,x∈xs→f x=g x) : xs.map f=xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x::xs.map f=g x::xs.map g
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

def macroSpec (o : Ops M) (v : List M) (b : Nat) : List M :=
  (positions 0 (count v.length b)).map (fun i=>product o (block v b i))

theorem macroSpec_length (o : Ops M) (v : List M) (b : Nat) :
    (macroSpec o v b).length=count v.length b := by
  simp only [macroSpec,List.length_map,positions_length]

theorem macro_correct (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat)
    (m : Nat→Bool) :
    macroWord o (prepare o f w b) (buildColumn o (prepare o f w b) m).locals =
      macroSpec o (word f w m) b := by
  unfold macroWord macroSpec
  rw [word_length]
  apply map_congr_on
  intro i hi
  have hib := (positions_mem 0 (count w.length b) i hi).2
  simp only [Nat.zero_add] at hib
  have h := local_correct o f w b m i 0 (len w.length b i) hib (by omega) (Nat.le_refl _)
  change (localAt o (buildColumn o (prepare o f w b) m).locals i 0 (len w.length b i)).getD o.one=_
  rw [h]
  have he := word_length f w m
  have hl := block_length (word f w m) b i (by rwa [he])
  rw [he] at hl
  rw [← hl,NestedColumns.slice_full]
  rfl

theorem macro_query (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat)
    (m : Nat→Bool) (i j : Nat) (hij : i≤j) (hj : j≤count w.length b) :
    FlatIndex.query o (buildColumn o (prepare o f w b) m).middleIndex (prepare o f w b).routes i j =
      some (product o (slice (macroSpec o (word f w m) b) i j)) := by
  have h := macro_correct o f w b m
  change FlatIndex.query o
    (FlatIndex.build o (macroWord o (prepare o f w b) (buildColumn o (prepare o f w b) m).locals))
    (FlatIndex.buildRoutes (count w.length b)) i j=_
  rw [h]
  have he : (macroSpec o (word f w m) b).length=count w.length b := by
    rw [macroSpec_length,word_length]
  rw [← he]
  exact FlatIndex.query_correct o _ i j hij (by rwa [he])

/-- Full macro blocks in [i,i+k) concatenate to a single text interval. -/
theorem macro_product (o : Ops M) (v : List M) (b i k : Nat)
    (h : (i+k)*b≤v.length) :
    product o ((positions i k).map (fun j=>product o (block v b j)))=
      product o (slice v (i*b) ((i+k)*b)) := by
  induction k generalizing i with
  | zero => simp only [positions,List.map_nil,product,Nat.add_zero,OuterColumn.slice_self]
  | succ k ih =>
    have he : (i+1+k)*b=(i+(k+1))*b := by congr 1; omega
    have hm : (i+1)*b≤(i+(k+1))*b := Nat.mul_le_mul_right b (by omega)
    have hmid : (i+1)*b≤v.length := Nat.le_trans hm h
    change o.mul (product o (block v b i))
      (product o ((positions (i+1) k).map (fun j=>product o (block v b j))))=_
    rw [ih (i+1) (by rwa [he]),he]
    unfold block stop
    rw [Nat.min_eq_left hmid,← product_append]
    rw [← OuterColumn.slice_split v (i*b) ((i+1)*b) ((i+(k+1))*b)
      (Nat.mul_le_mul_right b (by omega)) hm]

theorem macro_slice (o : Ops M) (v : List M) (b i j : Nat)
    (hij : i≤j) (hj : j≤count v.length b) (he : j*b≤v.length) :
    product o (slice (macroSpec o v b) i j)=product o (slice v (i*b) (j*b)) := by
  unfold macroSpec
  rw [map_slice,positions_slice _ _ _ hij hj]
  have hsum : i+(j-i)=j := by omega
  have h := macro_product o v b i (j-i) (by rwa [hsum])
  rw [hsum] at h
  exact h

theorem sub_slice (v : List M) (a c l r : Nat)
    (hac : a≤c) (hc : c≤v.length) (hl : l≤r) (hr : r≤c-a) :
    slice (slice v a c) l r=slice v (a+l) (a+r) := by
  apply NestedColumns.slice_at (slice v a c)
    (slice v a (a+l)) (slice v (a+l) (a+r)) (slice v (a+r) c)
  · rw [OuterColumn.slice_split v a (a+l) c (by omega) (by omega),
      OuterColumn.slice_split v (a+l) (a+r) c (by omega) (by omega)]
    simp only [List.append_assoc]
  · rw [OuterColumn.slice_length v a (a+l) (by omega) (by omega)]
    omega
  · rw [OuterColumn.slice_length v a (a+l) (by omega) (by omega),
      OuterColumn.slice_length v (a+l) (a+r) (by omega) (by omega)]
    omega

theorem local_global (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat)
    (m : Nat→Bool) (i l r : Nat) (hi : i<count w.length b)
    (hl : l≤r) (hr : r≤len w.length b i) :
    localAt o (buildColumn o (prepare o f w b) m).locals i l r =
      some (product o (slice (word f w m) (i*b+l) (i*b+r))) := by
  rw [local_correct o f w b m i l r hi hl hr]
  unfold block
  rw [word_length,sub_slice _ _ _ _ _ (start_stop _ _ _ hi)
    (by rw [word_length]; exact stop_le _ _ _) hl hr]

/-- A constant number of direct array lookups and at most three monoid
    products, including the middle flat lookup. -/
def query (o : Ops M) (S : Shared M) (C : Column M) (l r : Nat) : Option M := do
  let i := l/S.width
  let j := r/S.width
  let x := l%S.width
  let y := r%S.width
  if i=j then
    localAt o C.locals i x y
  else
    let left ← localAt o C.locals i x (len S.n S.width i)
    let middle ← FlatIndex.query o C.middleIndex S.routes (i+1) j
    let right ← localAt o C.locals j 0 y
    return o.mul left (o.mul middle right)

theorem query_correct (o : Ops M) (f : α × Bool→M) (w : List α) (b : Nat)
    (m : Nat→Bool) (l r : Nat) (hb : 0<b) (hl : l≤r) (hr : r≤w.length) :
    query o (prepare o f w b) (buildColumn o (prepare o f w b) m) l r =
      some (product o (slice (word f w m) l r)) := by
  let n := w.length
  let i := l/b
  let j := r/b
  let x := l%b
  let y := r%b
  have hix : i*b+x=l := by
    dsimp [i,x]
    rw [Nat.mul_comm (l/b) b,Nat.add_comm]
    exact Nat.mod_add_div l b
  have hjy : j*b+y=r := by
    dsimp [j,y]
    rw [Nat.mul_comm (r/b) b,Nat.add_comm]
    exact Nat.mod_add_div r b
  have hij : i≤j := by
    change l/b≤r/b
    exact (Nat.le_div_iff_mul_le hb).mpr (Nat.le_trans (Nat.div_mul_le_self l b) hl)
  have hjn : j<count w.length b := by
    have h : j≤w.length/b :=
      (Nat.le_div_iff_mul_le hb).mpr (Nat.le_trans (Nat.div_mul_le_self r b) hr)
    unfold count
    omega
  have hin : i<count w.length b := by omega
  have hx : x<b := Nat.mod_lt _ hb
  have hy : y<b := Nat.mod_lt _ hb
  have hyl : y≤len n b j := by
    have h1 : j*b+y≤n := by omega
    have h2 : j*b+y≤(j+1)*b := by rw [Nat.add_mul,Nat.one_mul]; omega
    have hh : j*b+y≤min ((j+1)*b) n := Nat.le_min.mpr ⟨h2,h1⟩
    unfold len stop
    omega
  have hxl : x≤len n b i := by
    have h1 : i*b+x≤n := by omega
    have h2 : i*b+x≤(i+1)*b := by rw [Nat.add_mul,Nat.one_mul]; omega
    have hh : i*b+x≤min ((i+1)*b) n := Nat.le_min.mpr ⟨h2,h1⟩
    unfold len stop
    omega
  let C := buildColumn o (prepare o f w b) m
  change (if i=j then localAt o C.locals i x y else do
    let left ← localAt o C.locals i x (len n b i)
    let middle ← FlatIndex.query o C.middleIndex (prepare o f w b).routes (i+1) j
    let right ← localAt o C.locals j 0 y
    return o.mul left (o.mul middle right))=_
  by_cases he : i=j
  · rw [if_pos he]
    have hxy : x≤y := by rw [he] at hix; omega
    have hyr : y≤len n b i := by rwa [he]
    rw [local_global o f w b m i x y hin hxy hyr,hix,he,hjy]
  · have hij' : i+1≤j := by omega
    have hmid : (i+1)*b≤j*b := Nat.mul_le_mul_right b hij'
    have hjb : j*b≤n := by omega
    have hil : len n b i=b := by
      unfold len stop
      rw [Nat.min_eq_left (Nat.le_trans hmid hjb),Nat.add_mul,Nat.one_mul]
      omega
    rw [if_neg he]
    have hloc := local_global o f w b m i x (len n b i) hin hxl (Nat.le_refl _)
    have hlast := local_global o f w b m j 0 y hjn (Nat.zero_le _) hyl
    have hmacro := macro_query o f w b m (i+1) j hij' (by omega)
    rw [hloc,hmacro,hlast]
    simp only [Option.bind,Nat.add_zero,hix,hjy,hil]
    have hmacro' := macro_slice o (word f w m) b (i+1) j hij'
      (by rw [word_length]; omega) (by rw [word_length]; exact hjb)
    rw [hmacro',Nat.add_mul i 1 b,Nat.one_mul]
    change some (o.mul (product o (slice (word f w m) l (i*b+b)))
      (o.mul (product o (slice (word f w m) (i*b+b) (j*b)))
        (product o (slice (word f w m) (j*b) r))))=_
    rw [← product_append,← product_append]
    rw [← OuterColumn.slice_split _ (i*b+b) (j*b) r (by simpa [Nat.add_mul] using hmid) (by omega)]
    have hmid' : i*b+b≤j*b := by simpa only [Nat.add_mul,Nat.one_mul] using hmid
    rw [← OuterColumn.slice_split _ l (i*b+b) r (by omega) (by omega)]

end REWB.BlockIndex
