import REWB.MaskedAllStartFullCostBank
import REWB.MaskedTraversalAggregateEraseMany

/-! New implementation of measured source deletion after the 2026-11-25
environment interruption. Each deletion performs the actual descriptor
lookup, source-batch erase, selected current-bank construction and
persistent replacement. Original SourceChange values and old counters
are retained. Source fanout stays in the returned source update ledger.
-/
namespace REWB.MaskedAllStart.FullCost.Erase
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h : Nat}

def refreshCurrent (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) : Bank.Result (SourceChange C E h) :=
  match st.slots[first]?.join with
  | none=>(⟨st,tree,false,3,0⟩,3)
  | some entry=>
    let cfg:=withLength entry.config old
    let ⟨⟨bank,oldWork⟩,fullWork⟩:=Bank.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target cfg
    match bank with
    | none=>(⟨st,tree,false,oldWork+6,1⟩,fullWork+6)
    | some value=>
      let ⟨replaced,replaceWork⟩:=Tree.replace tree first value
      let next:={st with
        slots:=st.slots.setIfInBounds first (some ⟨cfg,value⟩)
        repairWork:=st.repairWork+oldWork+8
        rebuilds:=st.rebuilds+1
        writes:=st.writes+1}
      (⟨next,replaced,true,oldWork+replaceWork+12,1⟩,fullWork+replaceWork+12)

theorem refreshCurrent_value (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).1=MaskedTraversalAggregate.refreshCurrent env first old st tree := by
  cases hs : st.slots[first]?.join with
  | none=>simp only [refreshCurrent,MaskedTraversalAggregate.refreshCurrent,hs]
  | some entry=>
    simp only [refreshCurrent,MaskedTraversalAggregate.refreshCurrent,hs,Bank.compile_value,Clip.compiled]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (withLength entry.config old)).1 <;> rfl

theorem refreshCurrent_extra (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).2≤(refreshCurrent env first old st tree).1.work+
      Bank.extra C E env.prepared.K*(refreshCurrent env first old st tree).1.calls := by
  rw [refreshCurrent_value]
  cases hs : st.slots[first]?.join with
  | none=>simp only [refreshCurrent,MaskedTraversalAggregate.refreshCurrent,hs,Nat.mul_zero,Nat.add_zero,Nat.le_refl]
  | some entry=>
    have hh:=Bank.compile_extra C E env.book env.prepared env.cRanges env.eRanges st.sources env.target (withLength entry.config old)
    simp only [refreshCurrent,MaskedTraversalAggregate.refreshCurrent,hs,Bank.compile_value,Clip.compiled]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (withLength entry.config old)).1 <;>
      simp only [Nat.mul_one] <;> omega

theorem refreshCurrent_calls_work (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).1.calls≤(refreshCurrent env first old st tree).1.work := by
  rw [refreshCurrent_value]
  cases hs : st.slots[first]?.join with
  | none=>simp only [MaskedTraversalAggregate.refreshCurrent,hs]; omega
  | some entry=>
    simp only [MaskedTraversalAggregate.refreshCurrent,hs,Clip.compiled]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (withLength entry.config old)).1 <;> simp only <;> omega

def eraseCurrent (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) : Bank.Result (SourceChange C E h) :=
  let ⟨owner,ownerWork⟩:=MaskedClusterDescriptor.locate partition capacity p
  let next:={st with
    sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
    repairWork:=st.repairWork+ownerWork+2}
  match owner with
  | none=>(⟨next,tree,true,ownerWork+2,0⟩,ownerWork+2)
  | some first=>
    let ⟨out,fullWork⟩:=refreshCurrent env first old next tree
    ({out with work:=out.work+ownerWork+3},fullWork+ownerWork+3)

theorem eraseCurrent_value (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).1=
      MaskedTraversalAggregate.eraseCurrent env partition capacity old p st tree := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 <;>
    simp only [eraseCurrent,MaskedTraversalAggregate.eraseCurrent,ho,refreshCurrent_value]

theorem eraseCurrent_extra (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).2≤(eraseCurrent env partition capacity old p st tree).1.work+
      Bank.extra C E env.prepared.K*(eraseCurrent env partition capacity old p st tree).1.calls := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>
    simp only [eraseCurrent,ho,Nat.mul_zero,Nat.add_zero,Nat.le_refl]
  | some first=>
    let next : Mutable.Store.State C E:={st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hh:=refreshCurrent_extra env first old next tree
    simp only [eraseCurrent,ho]
    dsimp only [next] at hh
    omega

theorem eraseCurrent_calls_work (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).1.calls≤
      (eraseCurrent env partition capacity old p st tree).1.work := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>simp only [eraseCurrent,ho]; omega
  | some first=>
    let next : Mutable.Store.State C E:={st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hh:=refreshCurrent_calls_work env first old next tree
    simp only [eraseCurrent,ho]
    dsimp only [next] at hh
    omega

def step (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (acc : Bank.Result (SourceChange C E h)) (p : Nat) : Bank.Result (SourceChange C E h) :=
  let ⟨before,total⟩:=acc
  let ⟨out,work⟩:=eraseCurrent env partition capacity old p before.store before.tree
  ({out with ready:=before.ready && out.ready,work:=before.work+out.work+1,calls:=before.calls+out.calls},
    total+work+1)

theorem fold_value (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (acc : Bank.Result (SourceChange C E h)) :
    (positions.foldl (step env partition capacity old) acc).1=
      positions.foldl (MaskedTraversalAggregate.eraseStep env partition capacity old) acc.1 := by
  induction positions generalizing acc with
  | nil=>rfl
  | cons p ps ih=>
    simp only [List.foldl_cons,ih,step,MaskedTraversalAggregate.eraseStep,eraseCurrent_value]

theorem fold_extra (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (acc : Bank.Result (SourceChange C E h))
    (ha : acc.2≤acc.1.work+Bank.extra C E env.prepared.K*acc.1.calls) :
    (positions.foldl (step env partition capacity old) acc).2≤
      (positions.foldl (step env partition capacity old) acc).1.work+
        Bank.extra C E env.prepared.K*(positions.foldl (step env partition capacity old) acc).1.calls := by
  induction positions generalizing acc with
  | nil=>exact ha
  | cons p ps ih=>
    apply ih
    have hh:=eraseCurrent_extra env partition capacity old p acc.1.store acc.1.tree
    simp only [step,Nat.mul_add]
    omega

theorem fold_calls_work (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (acc : Bank.Result (SourceChange C E h)) (ha : acc.1.calls≤acc.1.work) :
    (positions.foldl (step env partition capacity old) acc).1.calls≤
      (positions.foldl (step env partition capacity old) acc).1.work := by
  induction positions generalizing acc with
  | nil=>exact ha
  | cons p ps ih=>
    apply ih
    have hh:=eraseCurrent_calls_work env partition capacity old p acc.1.store acc.1.tree
    simp only [step]
    omega

def eraseMany (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) : Bank.Result (SourceChange C E h) :=
  positions.foldl (step env partition capacity old) (SourceChange.mk st tree true 0 0,0)

theorem eraseMany_value (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseMany env partition capacity old positions st tree).1=
      MaskedTraversalAggregate.eraseMany env partition capacity old positions st tree :=
  fold_value env partition capacity old positions (SourceChange.mk st tree true 0 0,0)

theorem eraseMany_work (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseMany env partition capacity old positions st tree).2≤
      (Bank.extra C E env.prepared.K+1)*(eraseMany env partition capacity old positions st tree).1.work := by
  have he:=fold_extra env partition capacity old positions (SourceChange.mk st tree true 0 0,0)
    (by simp only [Nat.mul_zero,Nat.add_zero,Nat.le_refl])
  have hc:=fold_calls_work env partition capacity old positions (SourceChange.mk st tree true 0 0,0) (Nat.le_refl 0)
  have hm:=Nat.mul_le_mul_left (Bank.extra C E env.prepared.K) hc
  simp only [eraseMany,Nat.add_mul,Nat.one_mul]
  omega

end REWB.MaskedAllStart.FullCost.Erase
