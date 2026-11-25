import REWB.MaskedMutableProgressionErase

/-! Exact dynamic fixed-step progression witnesses. Clipping uses scalar
arithmetic; one inclusive ordered-key query finds a live source. The
returned witness is a global physical position and can be passed directly
to `erase`. No requested positions or residue classes are enumerated. -/
namespace REWB.MaskedMutableProgression
open MaskedOrdered

structure Answer where
  value : Option Nat
  work : Nat
  deriving Repr

def Answer.answer (r : Answer) : Bool := r.value.isSome

def rangeGrid (idx : Index) (start used : Nat) : Answer :=
  let lo:=encode idx.len idx.step start
  let r:=Tree.interval idx.tree idx.capacity lo (lo+(used-1))
  ⟨r.1.map (fun key=>idx.base+decode idx.len idx.step key),r.2+15⟩

theorem rangeGrid_work (idx : Index) (start used : Nat) :
    (rangeGrid idx start used).work≤7*idx.levels+22 := by
  have hh:=Tree.interval_work idx.tree idx.capacity (encode idx.len idx.step start)
    (encode idx.len idx.step start+(used-1))
  simp only [rangeGrid]
  omega

theorem rangeGrid_some (idx : Index) (hv : idx.Valid) (hs : 0<idx.step)
    (start used : Nat) (hu : 0<used) (ha : start<idx.len)
    (hlast : start+(used-1)*idx.step<idx.len) (p : Nat)
    (hp : (rangeGrid idx start used).value=some p) :
    ∃t,t<used ∧ start+t*idx.step<idx.len ∧
      p=idx.base+(start+t*idx.step) ∧ idx.Live p := by
  change (Tree.interval idx.tree idx.capacity (encode idx.len idx.step start)
    (encode idx.len idx.step start+(used-1))).1.map
    (fun key=>idx.base+decode idx.len idx.step key)=some p at hp
  obtain ⟨key,hkey,hphys⟩:=Option.map_eq_some'.mp hp
  have hh:=Tree.interval_some idx.tree idx.capacity _ _ key hv.2.1 hv.2.2.1 hv.1 hkey
  obtain ⟨i,hi,he⟩:=hv.2.2.2 key hh.1
  subst key
  obtain ⟨t,ht,hit⟩:=(grid_interval idx.len idx.step start used i hs hu ha hi hlast).mp
    ⟨hh.2.1,hh.2.2.1⟩
  rw [decode_encode idx.len idx.step i hi] at hphys
  refine ⟨t,ht,by omega,by omega,?_,?_,?_⟩
  · omega
  · omega
  · have he : p-idx.base=i := by omega
    rw [he]
    exact hh.1

theorem rangeGrid_exists (idx : Index) (hv : idx.Valid) (hs : 0<idx.step)
    (start used : Nat) (hu : 0<used) (ha : start<idx.len)
    (hlast : start+(used-1)*idx.step<idx.len) :
    (rangeGrid idx start used).answer=true ↔
      ∃t,t<used ∧ idx.Live (idx.base+(start+t*idx.step)) := by
  rw [Answer.answer,Option.isSome_iff_exists]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨t,ht,_,he,hlive⟩:=rangeGrid_some idx hv hs start used hu ha hlast p hp
    exact ⟨t,ht,by rw [←he]; exact hlive⟩
  · rintro ⟨t,ht,hlive⟩
    have hi : start+t*idx.step<idx.len := by have hh:=hlive.2.1; omega
    have hmem : encode idx.len idx.step (start+t*idx.step)∈idx.tree.entries := by
      simpa only [Nat.add_sub_cancel_left] using hlive.2.2
    have hk:=(grid_interval idx.len idx.step start used (start+t*idx.step) hs hu ha hi hlast).mpr
      ⟨t,ht,rfl⟩
    obtain ⟨key,hkey⟩:=(Tree.interval_exists idx.tree idx.capacity _ _ hv.2.1 hv.2.2.1 hv.1).mpr
      ⟨encode idx.len idx.step (start+t*idx.step),hmem,hk.1,hk.2⟩
    refine ⟨idx.base+decode idx.len idx.step key,?_⟩
    simp only [rangeGrid,hkey]
    rfl

def grid (idx : Index) (start wanted : Nat) : Answer :=
  if idx.step=0 ∨ wanted=0 ∨ idx.len≤start then ⟨none,6⟩
  else
    let count:=(idx.len-1-start)/idx.step+1
    let used:=min wanted count
    let r:=rangeGrid idx start used
    ⟨r.value,r.work+13⟩

theorem grid_work (idx : Index) (start wanted : Nat) :
    (grid idx start wanted).work≤7*idx.levels+35 := by
  unfold grid
  split
  · dsimp only; omega
  · have hh:=rangeGrid_work idx start (min wanted ((idx.len-1-start)/idx.step+1))
    dsimp only
    omega

theorem grid_some (idx : Index) (hv : idx.Valid) (hs : 0<idx.step)
    (start wanted p : Nat) (hp : (grid idx start wanted).value=some p) :
    ∃t,t<wanted ∧ start+t*idx.step<idx.len ∧
      p=idx.base+(start+t*idx.step) ∧ idx.Live p := by
  unfold grid at hp
  split at hp
  next hbad => contradiction
  next hgood =>
    let count:=(idx.len-1-start)/idx.step+1
    let used:=min wanted count
    have ha : start<idx.len := by omega
    have hcount : 0<count := Nat.succ_pos _
    have hu : 0<used := by dsimp [used]; omega
    have hclip (t : Nat) : t<used ↔ t<wanted ∧ start+t*idx.step<idx.len := by
      have hh:=MaskedProgression.capacity_correct idx.len idx.step start t hs ha
      dsimp [used,count]
      omega
    have hlast : start+(used-1)*idx.step<idx.len := (hclip _).mp (by omega) |>.2
    change (rangeGrid idx start used).value=some p at hp
    obtain ⟨t,ht,hbound,he,hlive⟩:=rangeGrid_some idx hv hs start used hu ha hlast p hp
    exact ⟨t,((hclip t).mp ht).1,hbound,he,hlive⟩

theorem grid_correct (idx : Index) (hv : idx.Valid) (hs : 0<idx.step)
    (start wanted : Nat) :
    (grid idx start wanted).answer=true ↔
      ∃t,t<wanted ∧ start+t*idx.step<idx.len ∧ idx.Live (idx.base+(start+t*idx.step)) := by
  by_cases hbad : idx.step=0 ∨ wanted=0 ∨ idx.len≤start
  · simp only [grid,hbad,if_true,Answer.answer,Option.isSome_none,Bool.false_eq_true,false_iff]
    rintro ⟨t,ht,hbound,_⟩
    omega
  · let count:=(idx.len-1-start)/idx.step+1
    let used:=min wanted count
    have ha : start<idx.len := by omega
    have hcount : 0<count := Nat.succ_pos _
    have hu : 0<used := by dsimp [used]; omega
    have hclip (t : Nat) : t<used ↔ t<wanted ∧ start+t*idx.step<idx.len := by
      have hh:=MaskedProgression.capacity_correct idx.len idx.step start t hs ha
      dsimp [used,count]
      omega
    have hlast : start+(used-1)*idx.step<idx.len := (hclip _).mp (by omega) |>.2
    simp only [grid,hbad,if_false]
    change (rangeGrid idx start used).answer=true ↔ _
    rw [rangeGrid_exists idx hv hs start used hu ha hlast]
    constructor
    · rintro ⟨t,ht,hm⟩
      exact ⟨t,((hclip t).mp ht).1,((hclip t).mp ht).2,hm⟩
    · rintro ⟨t,hw,hbound,hm⟩
      exact ⟨t,(hclip t).mpr ⟨hw,hbound⟩,hm⟩

theorem grid_represents (idx : Index) (hv : idx.Valid) (hs : 0<idx.step)
    (live : Nat→Prop) (hr : idx.Represents live) (start wanted : Nat) :
    (grid idx start wanted).answer=true ↔
      ∃t,t<wanted ∧ start+t*idx.step<idx.len ∧ live (idx.base+(start+t*idx.step)) := by
  rw [grid_correct idx hv hs]
  constructor
  · rintro ⟨t,ht,hb,hm⟩; exact ⟨t,ht,hb,(hr _).mp hm |>.2.2⟩
  · rintro ⟨t,ht,hb,hm⟩
    exact ⟨t,ht,hb,(hr _).mpr ⟨by omega,by omega,hm⟩⟩

theorem grid_build_correct (mask : Array Bool) (base len step : Nat) (hs : 0<step)
    (start wanted : Nat) :
    (grid (build mask base len step).index start wanted).answer=true ↔
      ∃t,t<wanted ∧ start+t*step<len ∧
        MaskedProgression.readMask mask (base+(start+t*step))=true :=
  grid_represents _ (build_valid mask base len step) hs _
    (build_represents mask base len step) start wanted

end REWB.MaskedMutableProgression
