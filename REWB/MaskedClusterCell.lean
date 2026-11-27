import REWB.MaskedClusterContexts

/-! Executable one-jump matrix cells for the waiting/C/E stage machine.
    The two valid stage pairs select the appropriate immutable mask.
    Every endpoint-state test is an actual finite orbit; invalid stage
    pairs return false. Word-level exactness is transported to real text
    and local anchors in the transfer adapter.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps REWB.Periodic
variable {α : Type}

def always (d : DFA α) : OrbitData d.stateCount := ⟨identity _,d.initial,fun _=>true⟩

theorem always_test (d : DFA α) (n : Nat) : (always d).test n=true := rfl

def entryOrbit (C E : DFA α) (maps : Context C E) (input : Fin C.stateCount) :
    OrbitData C.stateCount := ⟨maps.leftStep,maps.before.get input,C.final⟩

def exitOrbit (d : DFA α) (period replay after : Map d.stateCount) (output : Fin d.stateCount) :
    OrbitData d.stateCount := ⟨period,replay.get d.initial,fun q=>decide (after.get q=output)⟩

theorem map_orbit (d : DFA α) (V : Word α) (input : Fin d.stateCount) (n : Nat) :
    FiniteOrbit.orbit (wordMap d V).get input n=d.run input (repeatWord V n) := by
  rw [run_repeat]
  congr 2
  funext q
  exact wordMap_get d V q

theorem entryOrbit_word (C E : DFA α) (pref V U after : Word α) (input : Fin C.stateCount) (n : Nat) :
    (entryOrbit C E (wordContext C E pref V U after) input).test n=true ↔
      C.final (C.run input (pref++repeatWord V n))=true := by
  simp only [entryOrbit,wordContext,OrbitData.test,wordMap_get,map_orbit,DFA.run_append]

theorem exitOrbit_word (d : DFA α) (V Y after : Word α) (output : Fin d.stateCount) (n : Nat) :
    (exitOrbit d (wordMap d V) (wordMap d Y) (wordMap d after) output).test n=true ↔
      d.run d.initial (Y++repeatWord V n++after)=output := by
  simp only [exitOrbit,OrbitData.test,wordMap_get,map_orbit,DFA.run_append,decide_eq_true_eq]

def cell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) :
    MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→MaskedProgression.Answer
  | .waiting,.gap output =>
    pairQuery (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
      lo hi sourceCounts base q s prepared.K
  | .gap input,.suffix output =>
    pairQuery (entryOrbit C E maps input) (exitOrbit E maps.rightE tail.2 maps.afterE output)
      lo hi targetCounts base q s prepared.K
  | _,_ => ⟨false,0,1⟩

def WordCell (C E : DFA α) (pref V U Y after : Word α) (lo hi k : Nat)
    (source target : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Prop :=
  ((MaskedClusterStage.jump C E source target
    (MaskedClusterStage.read C E (pref++repeatWord V (k-lo)) input)).map
      (MaskedClusterStage.read C E (Y++repeatWord U (hi-k)++after)))=some output

theorem wordCell_rank (C E : DFA α) (pref V U Y after : Word α) (lo hi k : Nat)
    (source target : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (h : WordCell C E pref V U Y after lo hi k source target input output) :
    MaskedClusterStage.rank output=MaskedClusterStage.rank input+1 := by
  unfold WordCell at h
  cases hj : MaskedClusterStage.jump C E source target
      (MaskedClusterStage.read C E (pref++repeatWord V (k-lo)) input) with
  | none =>
    have he : (none : Option (MaskedClusterStage.State C.stateCount E.stateCount))=some output := by
      simpa only [hj,Option.map] using h
    cases he
  | some t =>
    have hh : some (MaskedClusterStage.read C E (Y++repeatWord U (hi-k)++after) t)=some output := by
      simpa only [hj,Option.map] using h
    have he : MaskedClusterStage.read C E (Y++repeatWord U (hi-k)++after) t=output :=
      Option.some.inj hh
    rw [←he,MaskedClusterStage.read_rank]
    have hr:=MaskedClusterStage.jump_rank C E source target _ t hj
    simpa only [MaskedClusterStage.read_rank] using hr

theorem wordCell_waiting (C E : DFA α) (pref V U Y after : Word α) (lo hi k : Nat)
    (source target : Bool) (output : Fin C.stateCount) :
    WordCell C E pref V U Y after lo hi k source target .waiting (.gap output) ↔
      source=true ∧ C.run C.initial (Y++repeatWord U (hi-k)++after)=output := by
  cases source <;> simp [WordCell,MaskedClusterStage.read,MaskedClusterStage.jump]

theorem wordCell_gap (C E : DFA α) (pref V U Y after : Word α) (lo hi k : Nat)
    (source target : Bool) (input : Fin C.stateCount) (output : Fin E.stateCount) :
    WordCell C E pref V U Y after lo hi k source target (.gap input) (.suffix output) ↔
      target=true ∧ C.final (C.run input (pref++repeatWord V (k-lo)))=true ∧
        E.run E.initial (Y++repeatWord U (hi-k)++after)=output := by
  cases target <;> simp [WordCell,MaskedClusterStage.read,MaskedClusterStage.jump]

theorem cell_words (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (pref V U Y after : Word α) (lo hi : Nat) (source target : Array Bool)
    (base len q s : Nat) (input output : MaskedClusterStage.State C.stateCount E.stateCount) (hq : 0<q) :
    (cell C E prepared (wordContext C E pref V U after) (wordMap C Y,wordMap E Y) lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          WordCell C E pref V U Y after lo hi k
            (MaskedProgression.readMask source (s+k*q)) (MaskedProgression.readMask target (s+k*q)) input output := by
  cases input with
  | waiting =>
    cases output with
    | waiting =>
      simp only [cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
    | gap output =>
      simp only [cell,prepared.exact,modulus]
      rw [pairQuery_correct _ _ _ _ _ _ _ _ _ _ hq (Nat.le_max_left _ _) (Nat.le_max_left _ _)]
      simp only [PairAccepts,always_test,exitOrbit_word,wordContext,wordCell_waiting]
      constructor
      · rintro ⟨k,⟨hl,hh,_,he⟩,hb,hn,hm⟩
        exact ⟨k,hl,hh,hb,hn,hm,he⟩
      · rintro ⟨k,hl,hh,hb,hn,hm,he⟩
        exact ⟨k,⟨hl,hh,True.intro,he⟩,hb,hn,hm⟩
    | suffix output =>
      simp only [cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
  | gap input =>
    cases output with
    | waiting =>
      simp only [cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
    | gap output =>
      simp only [cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
    | suffix output =>
      simp only [cell,prepared.exact,modulus]
      rw [pairQuery_correct _ _ _ _ _ _ _ _ _ _ hq (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
      simp only [PairAccepts,exitOrbit_word,wordContext,wordCell_gap]
      constructor
      · rintro ⟨k,⟨hl,hh,hc,he⟩,hb,hn,hm⟩
        exact ⟨k,hl,hh,hb,hn,hm,(entryOrbit_word C E pref V U after input (k-lo)).mp hc,he⟩
      · rintro ⟨k,hl,hh,hb,hn,hm,hc,he⟩
        exact ⟨k,⟨hl,hh,(entryOrbit_word C E pref V U after input (k-lo)).mpr hc,he⟩,hb,hn,hm⟩
  | suffix input =>
    cases output <;>
      simp only [cell,Bool.false_eq_true,false_iff] <;>
      rintro ⟨k,_,_,_,_,hw⟩ <;>
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw <;>
      simp only [MaskedClusterStage.rank] at hr <;> omega

end REWB.MaskedCluster
