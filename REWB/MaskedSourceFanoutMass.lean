import REWB.MaskedSourceFanoutBuild

/-! Cached membership totals are exact. These proofs justify charging all
later one-shot source removals to the materialized incidence lists. -/
namespace REWB.MaskedSourceFanout
open REWB.RunGeometry REWB.MaskedPeriodic.Batch

def sumPrefix (f : Nat→Nat) : Nat→Nat
  | 0 => 0
  | n+1 => sumPrefix f n+f n

theorem sumPrefix_change (f g : Nat→Nat) (n p v : Nat)
    (hg : ∀ x,g x=if x=p then v else f x) :
    sumPrefix g n+(if p<n then f p else 0)=
      sumPrefix f n+(if p<n then v else 0) := by
  induction n with
  | zero => simp [sumPrefix]
  | succ n ih =>
    by_cases hp : p<n
    · have hn : n≠p := by omega
      have hp' : p<n+1 := by omega
      simp only [hp,ite_true] at ih
      simp only [sumPrefix,hg n,hn,ite_false,hp',ite_true]
      omega
    · by_cases he : n=p
      · subst p
        simp only [Nat.lt_irrefl,ite_false,Nat.add_zero] at ih
        simp only [sumPrefix,hg n,ite_true,Nat.lt_succ_self]
        omega
      · have hp' : ¬p<n+1 := by omega
        simp only [hp,ite_false,Nat.add_zero] at ih
        simp only [sumPrefix,hg n,he,ite_false,hp',Nat.add_zero]
        omega

def total (rows : Array Cell) : Nat := sumPrefix (fun p=>(read rows p).count) rows.size

def Good (out : Built) : Prop :=
  (∀ p,(read out.rows p).count=(read out.rows p).ids.length) ∧
    total out.rows=out.memberships

theorem push_total (id p : Nat) (out : Built) (hp : p<out.rows.size) :
    total (push id p out).rows=total out.rows+1 := by
  have hs:=sumPrefix_change (fun x=>(read out.rows x).count)
    (fun x=>(read (push id p out).rows x).count) out.rows.size p
    ((read out.rows p).count+1) (by
      intro x
      dsimp only
      rw [push_read]
      by_cases hx : x=p
      · subst x
        simp [hp]
      · simp [hx])
  simp only [hp,ite_true] at hs
  unfold total
  rw [push_size]
  omega

theorem push_good (id p : Nat) (out : Built) (hg : Good out) (hp : p<out.rows.size) :
    Good (push id p out) := by
  refine ⟨?_,?_⟩
  · intro x
    rw [push_read]
    split
    · simp only [List.length_cons,hg.1 x]
    · exact hg.1 x
  · rw [push_total id p out hp,hg.2]
    rfl

theorem fill_good (id len p : Nat) (out : Built) (hg : Good out)
    (hb : p+len≤out.rows.size) : Good (fill id len p out) := by
  induction len generalizing p out with
  | zero => exact hg
  | succ len ih =>
    rw [fill]
    apply ih (p+1) (push id p out) (push_good id p out hg (by omega))
    rw [push_size]
    omega

theorem loop_good (Rs : List Bounds) (id : Nat) (out : Built) (hg : Good out)
    (hb : ∀ R,R∈Rs → R.lo+span R≤out.rows.size) : Good (loop Rs id out) := by
  induction Rs generalizing id out with
  | nil => exact hg
  | cons R Rs ih =>
    rw [loop]
    apply ih (id+1)
      (fill id (span R) R.lo {out with work:=out.work+3})
      (fill_good _ _ _ _ hg (hb R List.mem_cons_self))
    intro S hS
    rw [fill_size]
    exact hb S (List.mem_cons_of_mem R hS)

theorem replicate_total (n : Nat) : total (Array.replicate n ({} : Cell))=0 := by
  have hs : ∀ k,sumPrefix (fun p=>(read (Array.replicate n ({} : Cell)) p).count) k=0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [sumPrefix,ih,read_replicate]; rfl
  exact hs _

theorem build_good (n : Nat) (Rs : List Bounds)
    (hb : ∀ R,R∈Rs → R.lo≤R.hi ∧ R.hi≤n) : Good (build n Rs) := by
  apply loop_good Rs 0 _
  · refine ⟨?_,replicate_total (n+1)⟩
    intro p
    rw [read_replicate]
    rfl
  · intro R hR
    have hr:=hb R hR
    simp only [Array.size_replicate,span]
    omega

end REWB.MaskedSourceFanout
