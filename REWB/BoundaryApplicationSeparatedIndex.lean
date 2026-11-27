import REWB.BoundaryApplicationSeparatedPass

/-! The separated endpoint bitset is constructed from the original
word and two boundaries. Descriptor keys, exact LCE/sorting trie, three
DFA map indexes, the joint-cut index and both finite-row passes are
all built internally. No trie, source row or answer is supplied. -/
namespace REWB.BoundaryApplication.Separated
open REWB.BoundaryTrie
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

def rangeBuildWork (D : DFA (Fin σ)) (idx : Range.Index D) : Nat :=
  D.stateCount*idx.products+idx.letterCells+idx.length+3

def cutBuildWork (A B D : DFA (Fin σ)) (idx : RTable.Shared A B D) : Nat :=
  let z:=(MarkedTransfer.enum (BoundaryIndex.FixedEnd.leftDFA A D) B).elems.length
  idx.buildProducts+2*(idx.length+1)*(z*z)+3*idx.length+4

structure BitIndex (w : Word (Fin σ)) where
  bits : Vector Bool (w.length+1)
  work : Nat

def buildBits (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h1 : g1≤w.length) : BitIndex w :=
  let t:=trie w fallback g0 g1 h1
  let aranges:=Range.build A w
  let cranges:=Range.build C w
  let dranges:=Range.build D w
  let cuts:=RTable.prepare A B D w
  let sources:=Summary.build A C w g0 aranges cranges t.tree
  let out:=Pass.go A B D cuts dranges sources.1 0 (Vector.ofFn (fun _=>false)) (Vector.ofFn (fun _=>false))
  ⟨out.1,t.work+rangeBuildWork A aranges+rangeBuildWork C cranges+rangeBuildWork D dranges+
    cutBuildWork A B D cuts+sources.2+out.2+12*(w.length+2)+D.stateCount+10⟩

/-- The original-slice separated predicate. The C gap ends at g0; the
D gap starts at g1. E is attached by the separate prefix aggregate. -/
def Predicate (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 : Nat)
    (target : Fin (w.length+1)) : Prop :=
  ∃source : Fin (w.length+1),source.val≤g0 ∧ C.accepts (slice w source.val g0) ∧
    ∃L,BoundaryApplication.Coverage.Cut A B D w g1 source target L

theorem full_iff (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) (target : Fin (w.length+1)) :
    Coverage.Full A B C D w g0 g1 (trie w fallback g0 g1 h1).tree target ↔
      Predicate A B C D w g0 g1 target := by
  constructor
  · rintro ⟨a,ha,p,hp,hC,L,hcut⟩
    exact ⟨p,trie_source_bound w fallback g0 g1 h1 a ha p hp,hC,L,hcut⟩
  · rintro ⟨p,hp,hC,L,hcut⟩
    obtain ⟨a,ha,ht⟩:=source_mem w g0 g1 h01 h1 p hp
    exact ⟨a,(BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).1.mem_iff.mpr ha,
      p,ht,hC,L,hcut⟩

theorem buildBits_correct (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) (target : Fin (w.length+1)) :
    (buildBits A B C D w fallback g0 g1 h1).bits.get target=true ↔ Predicate A B C D w g0 g1 target := by
  have hh:=Pass.go_correct A B C D w fallback g0 g1 (by omega)
    (trie w fallback g0 g1 h1).tree (trie w fallback g0 g1 h1).tree
    (trie_valid w fallback g0 g1 h1) (trie_source_bound w fallback g0 g1 h1)
    (trie_good w fallback g0 g1 h1) (trie_nonempty w fallback g0 g1 h1) 0 (Nat.zero_le _)
    (Coverage.covered_root w fallback _ 0) (Vector.ofFn (fun _=>false))
    (Or.inl ⟨rfl,fun _=>Table.get_ofFn _ _⟩) (Vector.ofFn (fun _=>false)) target
  simp only [Table.get_ofFn,Bool.false_eq_true,false_or] at hh
  change (buildBits A B C D w fallback g0 g1 h1).bits.get target=true ↔ _ at hh
  rw [hh,full_iff A B C D w fallback g0 g1 h01 h1 target]
  constructor
  · exact And.right
  · intro hp
    obtain ⟨source,hs,hC,L,hcut⟩:=hp
    have ht : g1≤target.val := by have hh:=hcut.2.1; omega
    obtain ⟨b,hb,hbr⟩:=target_mem w g0 g1 h1 target ht
    exact ⟨⟨b,(BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).1.mem_iff.mpr hb,hbr⟩,
      source,hs,hC,L,hcut⟩

theorem buildBits_iff_cuts (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) (target : Fin (w.length+1)) :
    (buildBits A B C D w fallback g0 g1 h1).bits.get target=true ↔
      ∃a L,a≤g0 ∧ L≤a ∧ g1+L≤target.val ∧
        slice w (a-L) a=slice w (target.val-L) target.val ∧
        A.accepts (slice w 0 (a-L)) ∧ B.accepts (slice w (a-L) a) ∧
        C.accepts (slice w a g0) ∧ D.accepts (slice w g1 (target.val-L)) := by
  rw [buildBits_correct A B C D w fallback g0 g1 h01 h1 target]
  constructor
  · rintro ⟨source,hs,hC,L,hL,hg,he,hA,hB,hD⟩
    exact ⟨source.val,L,hs,hL,hg,he,hA,hB,hC,hD⟩
  · rintro ⟨a,L,ha,hL,hg,he,hA,hB,hC,hD⟩
    exact ⟨⟨a,by omega⟩,ha,hC,L,hL,hg,he,hA,hB,hD⟩

end REWB.BoundaryApplication.Separated
