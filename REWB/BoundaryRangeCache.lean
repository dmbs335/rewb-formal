import REWB.BoundaryRangeCacheGrid
import REWB.BoundaryRangeFarRightCost
import REWB.BoundaryRangeFarIndex
import REWB.BoundaryRangeNearIndexBorderAll

/-! The complete six-case boundary cache, with two explicit stages.
`prepare` constructs every block's three near indexes, far-left index
and finite far-right mask requests, plus one shared border index.
`assemble` consumes finite output rows for those requests and builds
their reverse-E aggregates. The production all-start computation that
must fill the rows and establish `Ready` remains separate. -/
namespace REWB.BoundaryRange.Cache
variable {σ : Nat}

abbrev Inputs (K : DFA (Fin σ)) (n width : Nat) := Vector (FarRight.Input K) (CacheGrid.count n width)

def Ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (width : Nat)
    (bits : Inputs K w.length width) : Prop :=
  ∀slot,FarRight.Ready A B C K D w (CacheGrid.upper w.length width slot.val) (bits.get slot)

structure Block (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  lower : Nat
  upper : Nat
  near : NearIndex.Index A B C K D E w lower upper
  far : FarLeft.Index C K E w
  requests : FarRight.Requests K w
  work : Nat

def buildBlock (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) : Block A B C K D E w :=
  let near:=NearIndex.build A B C K D E w fallback g0 g h0g hg
  let far:=FarLeft.build A B C K D E w fallback g hg
  let requests:=FarRight.prepare K w g
  ⟨g0,g,near,far,requests,near.work+far.work+requests.work+2⟩

@[simp] theorem buildBlock_lower (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (buildBlock A B C K D E w fallback g0 g h0g hg).lower=g0 := rfl

@[simp] theorem buildBlock_upper (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (buildBlock A B C K D E w fallback g0 g h0g hg).upper=g := rfl

@[simp] theorem buildBlock_far (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (buildBlock A B C K D E w fallback g0 g h0g hg).far=FarLeft.build A B C K D E w fallback g hg := rfl

@[simp] theorem buildBlock_near (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (buildBlock A B C K D E w fallback g0 g h0g hg).near=NearIndex.build A B C K D E w fallback g0 g h0g hg := rfl

structure Prepared (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  length : Nat
  length_eq : length=w.length
  width : Nat
  positive : 0<width
  slots : Nat
  slots_eq : slots=CacheGrid.count length width
  blocks : Table.Index (fun _ : Fin slots=>Block A B C K D E w)
  border : NearIndex.Border.Index A B C K D E w
  work : Nat

def prepare (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) : Prepared A B C K D E w :=
  let n:=w.length
  let slots:=CacheGrid.count n width
  let blocks:=Table.build fun slot : Fin slots=>
    let h:=CacheGrid.bounds n width slot.val
    let block:=buildBlock A B C K D E w fallback (CacheGrid.lower n width slot.val)
      (CacheGrid.upper n width slot.val) h.1 h.2
    (block,block.work)
  let border:=NearIndex.Border.build A B C K D E w fallback
  ⟨n,rfl,width,hw,slots,rfl,blocks,border,blocks.work+border.work+n+9⟩

@[simp] theorem prepare_block (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (slot : Fin (CacheGrid.count w.length width)) :
    Table.get (prepare A B C K D E w fallback width hw).blocks slot=
      buildBlock A B C K D E w fallback (CacheGrid.lower w.length width slot.val)
        (CacheGrid.upper w.length width slot.val) (CacheGrid.bounds w.length width slot.val).1
        (CacheGrid.bounds w.length width slot.val).2 := by
  simp only [prepare,Table.get_build]

structure Index (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  prepared : Prepared A B C K D E w
  right : Table.Index (fun _ : Fin prepared.slots=>FarRight.Index K)
  work : Nat

def assemble (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (prepared : Prepared A B C K D E w) (bits : Vector (FarRight.Input K) prepared.slots) : Index A B C K D E w :=
  let right:=Table.build fun slot : Fin prepared.slots=>
    let requests:=(Table.get prepared.blocks slot).requests
    let out:=FarRight.assemble K E w requests (bits.get slot)
    (out,out.work-requests.work+2)
  ⟨prepared,right,prepared.work+right.work+4⟩

def build (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) : Index A B C K D E w :=
  assemble A B C K D E w (prepare A B C K D E w fallback width hw) bits

@[simp] theorem build_prepared (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) :
    (build A B C K D E w fallback width hw bits).prepared=prepare A B C K D E w fallback width hw := rfl

@[simp] theorem build_right (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) (slot : Fin (CacheGrid.count w.length width)) :
    Table.get (build A B C K D E w fallback width hw bits).right slot=
      FarRight.build K E w (CacheGrid.upper w.length width slot.val) (bits.get slot) := by
  simp only [build,assemble,Table.get_build,prepare_block,buildBlock]
  rfl

def queryValid {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right : Nat) (hl : left≤idx.prepared.length) : Bool×Nat :=
  let slot : Fin idx.prepared.slots:=⟨left/idx.prepared.width,by
    rw [idx.prepared.slots_eq]
    exact CacheGrid.slot_bound idx.prepared.length idx.prepared.width left idx.prepared.positive hl⟩
  let block:=Table.get idx.prepared.blocks slot
  let farLeft:=FarLeft.query K E block.far left right
  let farRight:=FarRight.query K (Table.get idx.right slot) left right
  let near:=NearIndex.queryThree block.near left right
  let border:=NearIndex.Border.query idx.prepared.border left right block.lower block.upper
  (farLeft.1 || farRight.1 || near.1 || border.1,farLeft.2+farRight.2+near.2+border.2+17)

def query {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right : Nat) : Bool×Nat :=
  if h : left≤right ∧ right≤idx.prepared.length then queryValid idx left right (by omega) else (false,3)

end REWB.BoundaryRange.Cache
