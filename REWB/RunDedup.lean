import REWB.RankIndex

/-! Exact binary-trie deduplication for generated run bounds. No scan of
the growing output list occurs. Counters include trie work, emitted and
copied key cells, and a fixed allowance per input/output-list step. -/
namespace REWB.RunDedup
open REWB.RunGeometry REWB.ExactKeys

def key (h : Nat) (R : Bounds) : KeyWord 2 :=
  RankIndex.bits h R.lo++(RankIndex.bits h R.hi++RankIndex.bits h R.period)

theorem key_length (h : Nat) (R : Bounds) : (key h R).length=3*h := by
  simp only [key,List.length_append,RankIndex.bits_length]
  omega

def Bounded (n : Nat) (R : Bounds) : Prop := R.lo≤n ∧ R.hi≤n ∧ R.period≤n

theorem key_exact (h n : Nat) (R S : Bounds) (hn : n<2^h)
    (hR : Bounded n R) (hS : Bounded n S) : key h R=key h S ↔ R=S := by
  constructor
  · intro he
    unfold Bounded at hR hS
    obtain ⟨ha,hbc⟩ := List.append_inj he (by simp only [RankIndex.bits_length])
    obtain ⟨hb,hc⟩ := List.append_inj hbc (by simp only [RankIndex.bits_length])
    have h1:=RankIndex.bits_injective h R.lo S.lo (by omega) (by omega) ha
    have h2:=RankIndex.bits_injective h R.hi S.hi (by omega) (by omega) hb
    have h3:=RankIndex.bits_injective h R.period S.period (by omega) (by omega) hc
    cases R
    cases S
    simp_all only [Bounds.mk.injEq]
  · intro he; rw [he]

theorem fresh_iff (reg : Registry 2) (w : KeyWord 2) :
    (assign reg w).registry.next≠reg.next ↔ lookup reg.tree w=none := by
  rcases intern_rank w reg.tree reg.next with h|h
  · change (intern w reg.tree reg.next).next≠reg.next ↔ _
    rw [h.1,h.2]
    simp
  · change (intern w reg.tree reg.next).next≠reg.next ↔ _
    rw [h.1,h.2.2]
    simp

theorem assigned_none (reg : Registry 2) (w v : KeyWord 2) :
    lookup (assign reg w).registry.tree v=none ↔ v≠w ∧ lookup reg.tree v=none := by
  change lookup (intern w reg.tree reg.next).tree v=none ↔ _
  rw [intern_lookup]
  by_cases he : v=w <;> simp [he]

structure Result where
  registry : Registry 2
  runs : List Bounds
  work : Nat

def go (h : Nat) (reg : Registry 2) : List Bounds→Result
  | [] => ⟨reg,[],0⟩
  | x::xs =>
    let a:=assign reg (key h x)
    let r:=go h a.registry xs
    ⟨r.registry,if a.registry.next≠reg.next then x::r.runs else r.runs,
      a.work+5*h+4+r.work⟩

def goTR (h : Nat) (reg : Registry 2) (acc : List Bounds) (work : Nat) : List Bounds→Result
  | [] => ⟨reg,acc.reverse,work⟩
  | x::xs =>
    let a:=assign reg (key h x)
    goTR h a.registry (if a.registry.next≠reg.next then x::acc else acc)
      (work+a.work+5*h+4) xs

theorem goTR_spec (h : Nat) (reg : Registry 2) (acc : List Bounds)
    (work : Nat) (xs : List Bounds) :
    goTR h reg acc work xs=
      ⟨(go h reg xs).registry,acc.reverse++(go h reg xs).runs,work+(go h reg xs).work⟩ := by
  induction xs generalizing reg acc work with
  | nil => simp [goTR,go]
  | cons x xs ih =>
    rw [goTR,ih]
    simp only [go]
    split <;> simp_all only [List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc]

def tailGo (h : Nat) (reg : Registry 2) (xs : List Bounds) : Result := goTR h reg [] 0 xs

@[csimp] theorem go_eq_tailGo : go=tailGo := by
  funext h reg xs
  simp only [tailGo,goTR_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem go_sublist (h : Nat) (reg : Registry 2) (xs : List Bounds) :
    (go h reg xs).runs.Sublist xs := by
  induction xs generalizing reg with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    simp only [go]
    split
    · exact (ih _).cons₂ x
    · exact (ih _).cons x

theorem go_fresh (h : Nat) (reg : Registry 2) (xs : List Bounds) (R : Bounds)
    (hR : R∈(go h reg xs).runs) : lookup reg.tree (key h R)=none := by
  induction xs generalizing reg with
  | nil => simp [go] at hR
  | cons x xs ih =>
    simp only [go] at hR
    split at hR
    next hn =>
      rcases List.mem_cons.mp hR with he|ht
      · subst R
        exact (fresh_iff reg (key h x)).mp hn
      · exact ((assigned_none reg (key h x) (key h R)).mp (ih _ ht)).2
    next hn =>
      exact ((assigned_none reg (key h x) (key h R)).mp (ih _ hR)).2

theorem go_nodup (h : Nat) (reg : Registry 2) (xs : List Bounds) :
    (go h reg xs).runs.Nodup := by
  induction xs generalizing reg with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [go]
    split
    · apply List.nodup_cons.mpr
      refine ⟨?_,ih _⟩
      intro hx
      have hf:=go_fresh h (assign reg (key h x)).registry xs x hx
      rw [assign_lookup] at hf
      contradiction
    · exact ih _

theorem go_mem (h : Nat) (reg : Registry 2) (xs : List Bounds) (R : Bounds)
    (he : ∀ x,x∈xs→key h x=key h R→x=R) :
    R∈(go h reg xs).runs ↔ R∈xs ∧ lookup reg.tree (key h R)=none := by
  induction xs generalizing reg with
  | nil => simp [go]
  | cons x xs ih =>
    have ht:=ih (reg:=(assign reg (key h x)).registry)
      (fun y hy=>he y (List.mem_cons_of_mem x hy))
    constructor
    · intro hm
      exact ⟨(go_sublist h reg (x::xs)).subset hm,go_fresh h reg (x::xs) R hm⟩
    · rintro ⟨hm,hn⟩
      simp only [go]
      by_cases hx : R=x
      · subst R
        have hf: (assign reg (key h x)).registry.next≠reg.next :=
          (fresh_iff reg (key h x)).mpr hn
        rw [if_pos hf]
        exact List.mem_cons_self
      · have hm' : R∈xs := (List.mem_cons.mp hm).resolve_left hx
        have hk : key h R≠key h x := by
          intro hk
          exact hx (he x (List.mem_cons_self) hk.symm).symm
        have hr:=ht.mpr ⟨hm',(assigned_none reg (key h x) (key h R)).mpr ⟨hk,hn⟩⟩
        split
        · exact List.mem_cons_of_mem x hr
        · exact hr

theorem go_work (h : Nat) (reg : Registry 2) (xs : List Bounds) :
    (go h reg xs).work≤(26*h+5)*xs.length := by
  induction xs generalizing reg with
  | nil => simp [go]
  | cons x xs ih =>
    have hc:=intern_cost (key h x) reg.tree reg.next
    rw [key_length] at hc
    have ht:=ih (assign reg (key h x)).registry
    change (intern (key h x) reg.tree reg.next).work+5*h+4+
      (go h (assign reg (key h x)).registry xs).work≤(26*h+5)*(xs.length+1)
    rw [Nat.mul_succ (26*h+5) xs.length]
    omega

theorem go_valid (h : Nat) (reg : Registry 2) (xs : List Bounds) (hr : reg.Valid) :
    (go h reg xs).registry.Valid := by
  induction xs generalizing reg with
  | nil => exact hr
  | cons x xs ih => exact ih _ (assign_valid reg hr (key h x))

theorem go_next (h : Nat) (reg : Registry 2) (xs : List Bounds) :
    (go h reg xs).registry.next≤reg.next+xs.length := by
  induction xs generalizing reg with
  | nil => simp [go]
  | cons x xs ih =>
    have ht:=ih (assign reg (key h x)).registry
    have hn:=intern_next_le (key h x) reg.tree reg.next
    change (assign reg (key h x)).registry.next≤reg.next+1 at hn
    change (go h (assign reg (key h x)).registry xs).registry.next≤reg.next+(xs.length+1)
    omega

def run (n : Nat) (xs : List Bounds) : Result := go ((n+1).log2+1) initial xs

theorem run_mem (n : Nat) (xs : List Bounds)
    (hb : ∀ R,R∈xs→Bounded n R) (R : Bounds) :
    R∈(run n xs).runs ↔ R∈xs := by
  by_cases hm : R∈xs
  · have hr:=hb R hm
    have hk : ∀ S,S∈xs→key ((n+1).log2+1) S=key ((n+1).log2+1) R→S=R := by
      intro S hs he
      apply (key_exact _ n S R (by have h:=Nat.lt_log2_self (n:=n+1); omega) (hb S hs) hr).mp he
    rw [run,go_mem _ _ _ _ hk]
    simp only [initial,lookup_empty,and_true]
  · constructor
    · intro h; exact False.elim (hm ((go_sublist _ _ xs).subset h))
    · exact False.elim ∘ hm

theorem run_nodup (n : Nat) (xs : List Bounds) : (run n xs).runs.Nodup := go_nodup _ _ _

theorem run_length (n : Nat) (xs : List Bounds) : (run n xs).runs.length≤xs.length :=
  (go_sublist _ _ xs).length_le

theorem run_work (n : Nat) (xs : List Bounds) :
    (run n xs).work≤(26*((n+1).log2+1)+5)*xs.length := go_work _ _ _

theorem run_valid (n : Nat) (xs : List Bounds) : (run n xs).registry.Valid :=
  go_valid _ _ _ initial_valid

theorem run_rank_bound (n : Nat) (xs : List Bounds) :
    (run n xs).registry.next≤xs.length := by
  simpa only [run,initial,Nat.zero_add] using go_next ((n+1).log2+1) initial xs

theorem valid_bounded {α : Type} (f : Nat→α) (n : Nat) (R : Bounds)
    (hR : R.Valid f n) : Bounded n R := by
  have h1:=hR.1
  have h2:=hR.2.1
  have h3:=hR.2.2.1
  exact ⟨by omega,h2,by omega⟩

end REWB.RunDedup
