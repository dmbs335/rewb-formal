import REWB.MaskedTraversalContextCorrect

/-! The retained-bank invariant records actual array IDs and immutable
prefix counts, not an answer function. Together with an anchored-word
certificate it yields literal current-source semantics for H >= L.
Current complete-class geometry and retained H-copy words are distinct:
the retained certificate may mention only this cluster's copies, since
other clusters can have different H-prefixes after a suffix-trie merge.
-/
namespace REWB.MaskedTraversalContext
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady REWB.RunGeometry
variable {α : Type} {h : Nat}

def RunBacked (sources : Mutable.Batch.Sources) (target : Array Bool) (K : Nat)
    (cfg : Mutable.Store.Config) : Prop :=
  cfg.descriptor.repetitions≠0→∃R : Bounds,∃id,
    cfg.runId=some id ∧ sources.runs[id]?=some R ∧ R.period=cfg.descriptor.period ∧
    R.lo≤cfg.descriptor.first ∧ cfg.descriptor.last+cfg.anchor≤R.hi+1 ∧
    cfg.targetCounts=(MaskedProgression.build target R.lo (MaskedPeriodic.Batch.span R) (K*R.period)).counts

theorem runBacked_erase (sources : Mutable.Batch.Sources) (target : Array Bool) (K p : Nat)
    (cfg : Mutable.Store.Config) (hr : RunBacked sources target K cfg) :
    RunBacked (MaskedMutableProgression.Batch.eraseSource p sources) target K cfg := hr

theorem runBacked_context (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Mutable.Store.Config) (sources : Mutable.Batch.Sources)
    (target : Array Bool) (K : Nat) (hr : RunBacked sources target K old)
    (ha : readAnchor anchors first L=old.anchor) :
    RunBacked sources target K (config partition capacity first L anchors old) := by
  simpa only [RunBacked,config,ha] using hr

theorem retained_geometry (f : Nat→α) (n fullBase anchorBase : Nat)
    (fullCopies copies : List Nat) (cfg : Mutable.Store.Config)
    (hg : MaskedClusterDescriptor.Geometry f n fullBase cfg.length fullCopies cfg.descriptor)
    (cert : MaskedLocalAnchor.Certificate f n anchorBase cfg.length copies cfg.descriptor.last
      (cfg.descriptor.nextAt n) cfg.descriptor.previous cfg.descriptor.following cfg.anchor)
    (hin : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
      cfg.incoming≤if cfg.descriptor.repetitions=0 then cfg.descriptor.nextAt n else cfg.descriptor.first+cfg.descriptor.period) :
    Mutable.Store.Geometry cfg n := by
  refine ⟨cert.current,?_,?_,?_,hg.next_bound,?_,hin⟩
  · intro hm
    have hd:=(hg.dense (by omega)).1
    have hh:=cert.current
    omega
  · intro hm
    exact cert.previousSafe _ (hg.dense (by omega)).2.2
  · rw [←hg.endpoint]
    exact hg.next_strict
  · rw [←hg.endpoint]
    exact cert.lastBound

theorem store_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (source target : Array Bool) (removed : List Nat) (sources : Mutable.Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources) (hn : sources.n=w.length)
    (hK : sources.modulus=prepared.K) (cfg : Mutable.Store.Config)
    (fullBase anchorBase : Nat) (fullCopies copies : List Nat)
    (hg : MaskedClusterDescriptor.Geometry (ArrayText.read w.toArray fallback) w.length
      fullBase cfg.length fullCopies cfg.descriptor)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      anchorBase cfg.length copies cfg.descriptor.last (cfg.descriptor.nextAt w.length)
      cfg.descriptor.previous cfg.descriptor.following cfg.anchor)
    (hmem : ∀k,k≤cfg.descriptor.repetitions→cfg.descriptor.first+k*cfg.descriptor.period∈copies)
    (hr : RunBacked sources target prepared.K cfg)
    (hin : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
      cfg.incoming≤if cfg.descriptor.repetitions=0 then cfg.descriptor.nextAt w.length else cfg.descriptor.first+cfg.descriptor.period)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target cfg).1.any
      (fun bank=>bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
        (code _ inMode i) (code _ outMode j))=true ↔
      Mutable.Batch.CursorStep C E w cfg.descriptor.first cfg.descriptor.period cfg.descriptor.repetitions
        cfg.length cfg.anchor (cfg.descriptor.nextAt w.length) cfg.incoming cfg.incomingEnabled
        inMode outMode source removed target (cfg.window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  by_cases hm : cfg.descriptor.repetitions=0
  · have hp:=hg.point hm
    have cert' : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
        anchorBase cfg.length copies cfg.descriptor.first (cfg.descriptor.nextAt w.length)
        cfg.descriptor.previous cfg.descriptor.following cfg.anchor := by
      rw [hp.1]
      exact cert
    have hsep : cfg.descriptor.first<cfg.descriptor.nextAt w.length := by rw [hp.1]; exact hg.next_strict
    have henter : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
        cfg.incoming≤cfg.descriptor.nextAt w.length := by simpa only [hm,if_true] using hin
    have hsource : cfg.descriptor.first≤sources.n := by
      rw [hn]
      have hh:=cert'.lastBound
      omega
    have hc:=Mutable.Batch.compileSingleton_current C E book w fallback source removed sources hv
      anchorBase cfg.length copies cfg.descriptor.first cfg.anchor (cfg.descriptor.nextAt w.length) cfg.incoming
      cfg.descriptor.previous cfg.descriptor.following cfg.incomingEnabled gate inMode outMode target cfg.window i j
      cert' hsep hg.next_bound henter hsource
    simp only [Mutable.Store.compile,hm,if_true,Option.any_some,hn]
    rw [hp.2.1]
    exact hc
  · have hmpos : 0<cfg.descriptor.repetitions := by omega
    obtain ⟨R,id,hrid,hrow,hrq,hrlo,hrhi,hcounts⟩:=hr hm
    have hend : cfg.descriptor.first+cfg.descriptor.repetitions*R.period=cfg.descriptor.last := by
      rw [hrq]
      exact hg.endpoint.symm
    have cert' : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
        anchorBase cfg.length copies (cfg.descriptor.first+cfg.descriptor.repetitions*R.period)
        (cfg.descriptor.nextAt w.length) cfg.descriptor.previous cfg.descriptor.following cfg.anchor := by
      rw [hend]
      exact cert
    have hmem' : ∀k,k≤cfg.descriptor.repetitions→cfg.descriptor.first+k*R.period∈copies := by
      simpa only [hrq] using hmem
    have hprev : cfg.descriptor.previous=some (cfg.descriptor.first+(cfg.descriptor.repetitions-1)*R.period) := by
      rw [hrq]
      exact (hg.dense hmpos).2.2
    have henter : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
        cfg.incoming≤cfg.descriptor.first+R.period := by simpa only [hm,if_false,hrq] using hin
    have hc:=Mutable.Batch.compileRun_current C E book prepared w fallback source removed sources hv id R hrow hK
      anchorBase cfg.length copies cfg.descriptor.first cfg.descriptor.repetitions cfg.anchor
      (cfg.descriptor.nextAt w.length) cfg.incoming cfg.descriptor.previous cfg.descriptor.following
      cfg.incomingEnabled gate inMode outMode target cfg.window i j cert' hmpos
      (by rw [hrq]; exact (hg.dense hmpos).1) hmem' hprev (by rw [hend]; exact hg.next_strict)
      hg.next_bound henter hrlo (by rw [hend]; exact hrhi)
    have hcover : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧
        cfg.descriptor.last+cfg.anchor≤R.hi+1 := ⟨hrq,hrlo,hrhi⟩
    simp only [Mutable.Store.compile,hm,if_false,hrid,hrow,hcover,if_true,true_and,hn]
    rw [hcounts]
    apply hc.trans
    rw [hrq]

end REWB.MaskedTraversalContext
