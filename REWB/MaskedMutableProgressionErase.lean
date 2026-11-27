import REWB.MaskedMutableProgression

/-! Point membership and source deletion by global physical position.
Each result is a new persistent version. Repeated deletion and positions
outside the run window are harmless; unchanged branches remain shared. -/
namespace REWB.MaskedMutableProgression
open MaskedOrdered

def member (idx : Index) (p : Nat) : Bool×Nat :=
  if p<idx.base ∨ idx.base+idx.len≤p then (false,3)
  else
    let r:=Tree.contains idx.tree idx.capacity (encode idx.len idx.step (p-idx.base))
    (r.1,r.2+9)

theorem member_correct (idx : Index) (hv : idx.Valid) (p : Nat) :
    (member idx p).1=true ↔ idx.Live p := by
  unfold member Index.Live
  split
  next ho => simp only [Bool.false_eq_true,false_iff]; omega
  next hin =>
    dsimp only
    rw [Tree.contains_correct idx.tree idx.capacity _ hv.2.2.1 hv.1]
    constructor
    · intro hm; exact ⟨by omega,by omega,hm⟩
    · exact fun h=>h.2.2

theorem member_work (idx : Index) (p : Nat) : (member idx p).2≤4*idx.levels+11 := by
  unfold member
  split
  · omega
  · have hh:=Tree.contains_work idx.tree idx.capacity (encode idx.len idx.step (p-idx.base))
    dsimp only
    omega

def erase (idx : Index) (p : Nat) : Built :=
  if p<idx.base ∨ idx.base+idx.len≤p then ⟨idx,3⟩
  else
    let r:=Tree.erase idx.tree idx.capacity (encode idx.len idx.step (p-idx.base))
    ⟨{idx with tree:=r.1},r.2+10⟩

theorem erase_base (idx : Index) (p : Nat) : (erase idx p).index.base=idx.base := by
  unfold erase; split <;> rfl
theorem erase_len (idx : Index) (p : Nat) : (erase idx p).index.len=idx.len := by
  unfold erase; split <;> rfl
theorem erase_step (idx : Index) (p : Nat) : (erase idx p).index.step=idx.step := by
  unfold erase; split <;> rfl
theorem erase_levels (idx : Index) (p : Nat) : (erase idx p).index.levels=idx.levels := by
  unfold erase; split <;> rfl
theorem erase_capacity (idx : Index) (p : Nat) : (erase idx p).index.capacity=idx.capacity := by
  unfold erase; split <;> rfl

theorem erase_valid (idx : Index) (hv : idx.Valid) (p : Nat) : (erase idx p).index.Valid := by
  unfold erase
  split
  · exact hv
  · refine ⟨hv.1,Tree.erase_good idx.tree idx.capacity _ hv.2.1,
      Tree.erase_fits idx.tree idx.capacity _ hv.2.2.1 hv.1,?_⟩
    intro key hk
    have hh:=(Tree.erase_mem idx.tree idx.capacity _ key hv.2.2.1 hv.1).mp hk
    exact hv.2.2.2 key hh.2

theorem erase_live (idx : Index) (hv : idx.Valid) (p x : Nat) :
    (erase idx p).index.Live x ↔ x≠p ∧ idx.Live x := by
  unfold erase
  split
  next ho =>
    change idx.Live x ↔ x≠p ∧ idx.Live x
    constructor
    · intro hx; exact ⟨by obtain ⟨hlo,hhi,_⟩:=hx; omega,hx⟩
    · exact fun hx=>hx.2
  next hin =>
    change (idx.base≤x ∧ x<idx.base+idx.len ∧ encode idx.len idx.step (x-idx.base)∈
      (Tree.erase idx.tree idx.capacity (encode idx.len idx.step (p-idx.base))).1.entries) ↔ _
    rw [Tree.erase_mem idx.tree idx.capacity _ _ hv.2.2.1 hv.1]
    constructor
    · rintro ⟨hlo,hhi,hne,hm⟩
      refine ⟨?_,hlo,hhi,hm⟩
      intro he; subst x; exact hne rfl
    · rintro ⟨hne,hlo,hhi,hm⟩
      refine ⟨hlo,hhi,?_,hm⟩
      intro he
      have hh:=encode_injective idx.len idx.step (x-idx.base) (p-idx.base)
        (by omega) (by omega) he
      omega

theorem erase_work (idx : Index) (p : Nat) : (erase idx p).work≤12*idx.levels+13 := by
  unfold erase
  split
  · dsimp only; omega
  · have hh:=Tree.erase_work idx.tree idx.capacity (encode idx.len idx.step (p-idx.base))
    dsimp only
    omega

/-- A source predicate describes the current version, restricted to this
run window. It may be a globally maintained mask or a deletion history. -/
def Index.Represents (idx : Index) (live : Nat→Prop) : Prop :=
  ∀p,idx.Live p ↔ idx.base≤p ∧ p<idx.base+idx.len ∧ live p

theorem build_represents (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.Represents (fun p=>MaskedProgression.readMask mask p=true) :=
  build_live mask base len step

theorem erase_represents (idx : Index) (hv : idx.Valid) (live : Nat→Prop)
    (hr : idx.Represents live) (p : Nat) :
    (erase idx p).index.Represents (fun x=>x≠p ∧ live x) := by
  intro x
  rw [erase_live idx hv p x,hr x,erase_base,erase_len]
  constructor
  · rintro ⟨hne,hlo,hhi,hm⟩; exact ⟨hlo,hhi,hne,hm⟩
  · rintro ⟨hlo,hhi,hne,hm⟩; exact ⟨hne,hlo,hhi,hm⟩

theorem erase_idempotent_live (idx : Index) (hv : idx.Valid) (p x : Nat) :
    (erase (erase idx p).index p).index.Live x ↔ (erase idx p).index.Live x := by
  rw [erase_live _ (erase_valid idx hv p) p x,erase_live idx hv p x]
  simp only [←and_assoc,and_self]

end REWB.MaskedMutableProgression
