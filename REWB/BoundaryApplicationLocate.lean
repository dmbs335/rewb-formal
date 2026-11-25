import REWB.BoundaryApplicationHeavyQuery

/-! The actual source slot chooses a source leaf and its exact sequence
of heavy-segment bottoms. These structural specifications are used only
in proofs. The executable query remains direct array lookup plus stored
jumps; it never computes a route list. Duplicate source labels need no
uniqueness assumption: the theorem follows the leaf actually last written
to the source slot by the address construction. -/
namespace REWB.BoundaryApplication.Address
open REWB.BoundaryApplication.Heavy
variable {σ : Nat} {A D E : DFA (Fin σ)} {n : Nat}

inductive SourceRoute (p : Fin (n+1)) : Heavy.Saved A D E n→List (Heavy.Entry A D E n)→Prop
  | leaf (e : Heavy.Entry A D E n) (terminal : Option (Endpoint n)) :
      terminal=some (.source p)→SourceRoute p (.leaf e terminal) [e]
  | left (e : Heavy.Entry A D E n) (chooseRight : Bool) (l r : Heavy.Saved A D E n)
      (es : List (Heavy.Entry A D E n)) :
      SourceRoute p l es→SourceRoute p (.node e chooseRight l r)
        (if chooseRight then es++[e] else es)
  | right (e : Heavy.Entry A D E n) (chooseRight : Bool) (l r : Heavy.Saved A D E n)
      (es : List (Heavy.Entry A D E n)) :
      SourceRoute p r es→SourceRoute p (.node e chooseRight l r)
        (if chooseRight then es else es++[e])

inductive Chain (xs : Array (Cell A D E n)) : Option Nat→List (Heavy.Entry A D E n)→Prop
  | stop : Chain xs none []
  | step {i : Nat} {c : Cell A D E n} {es : List (Heavy.Entry A D E n)} :
      xs[i]?=some c→Chain xs c.jump es→Chain xs (some i) (c.entry::es)

theorem chain_extends {xs ys : Array (Cell A D E n)} (hxy : Extends xs ys)
    (cursor : Option Nat) (es : List (Heavy.Entry A D E n)) (hc : Chain xs cursor es) : Chain ys cursor es := by
  induction hc with
  | stop => exact Chain.stop
  | step hi _ ih => exact Chain.step (hxy _ _ hi) ih

theorem onChain_step (xs : Array (Cell A D E n)) (i : Nat) (c : Cell A D E n)
    (hc : xs[i]?=some c) (P : Heavy.Entry A D E n→Prop) :
    (∃d,HeavyIndex.OnChain xs (some i) d ∧ P d.entry) ↔
      P c.entry ∨ ∃d,HeavyIndex.OnChain xs c.jump d ∧ P d.entry := by
  constructor
  · rintro ⟨d,hd,hp⟩
    cases hd with
    | here he =>
      have hh : c=d := Option.some.inj (hc.symm.trans he)
      exact Or.inl (hh ▸ hp)
    | @next _ j _ e he hj hh =>
      have hce : c=e := Option.some.inj (hc.symm.trans he)
      subst e
      right
      rw [hj]
      exact ⟨d,hh,hp⟩
  · rintro (hp | ht)
    · exact ⟨c,Reaches.here hc,hp⟩
    · cases hj : c.jump with
      | none => rw [hj] at ht; exact False.elim ht.choose_spec.1
      | some j =>
        rw [hj] at ht
        obtain ⟨d,hd,hp⟩:=ht
        exact ⟨d,Reaches.next hc hj hd,hp⟩

theorem chain_predicate (xs : Array (Cell A D E n)) (cursor : Option Nat)
    (es : List (Heavy.Entry A D E n)) (hc : Chain xs cursor es) (P : Heavy.Entry A D E n→Prop) :
    (∃c,HeavyIndex.OnChain xs cursor c ∧ P c.entry) ↔ ∃e,e∈es ∧ P e := by
  induction hc with
  | stop => simp only [HeavyIndex.OnChain,false_and,exists_false,List.not_mem_nil]
  | @step i c es hi hc ih =>
    rw [onChain_step xs i c hi P,ih]
    simp only [List.mem_cons]
    constructor
    · rintro (hp | ⟨e,he,hp⟩)
      · exact ⟨c.entry,Or.inl rfl,hp⟩
      · exact ⟨e,Or.inr he,hp⟩
    · rintro ⟨e,he|he,hp⟩
      · exact Or.inl (he ▸ hp)
      · exact Or.inr ⟨e,he,hp⟩

theorem walk_source_unchanged (t : Heavy.Saved A D E n) (s : Store A D E n)
    (jump : Option Nat) (rank : Nat) (p : Fin (n+1)) (ht : ¬HasSource p t) :
    (walk t s jump rank).sources.get p=s.sources.get p := by
  induction t generalizing s jump rank with
  | leaf e terminal =>
    exact (push_source s e jump rank terminal p).trans (if_neg ht)
  | node e b l r ihl ihr =>
    have hl : ¬HasSource p l := fun h=>ht (Or.inl h)
    have hr : ¬HasSource p r := fun h=>ht (Or.inr h)
    simp only [walk,ihr _ _ _ hr,ihl _ _ _ hl,push_source,reduceCtorEq,if_false]

theorem walk_source_route (t : Heavy.Saved A D E n) (s : Store A D E n)
    (jump : Option Nat) (rank : Nat) (tail : List (Heavy.Entry A D E n))
    (hc : Chain s.nodes jump tail) (p : Fin (n+1)) (ht : HasSource p t) :
    ∃es,SourceRoute p t es ∧
      Chain (walk t s jump rank).nodes ((walk t s jump rank).sources.get p) (es++tail) := by
  induction t generalizing s jump rank tail with
  | leaf e terminal =>
    change terminal=some (.source p) at ht
    refine ⟨[e],SourceRoute.leaf e terminal ht,?_⟩
    change Chain (push s e jump rank terminal).nodes ((push s e jump rank terminal).sources.get p) ([e]++tail)
    rw [push_source,if_pos ht]
    exact Chain.step (push_here s e jump rank terminal)
      (chain_extends (push_extends s e jump rank terminal) jump tail hc)
  | node e b l r ihl ihr =>
    let out:=push s e jump rank none
    let jl:=if b then some s.nodes.size else jump
    let jr:=if b then jump else some s.nodes.size
    let dl:=if b then rank+1 else rank
    let dr:=if b then rank else rank+1
    let tl:=if b then e::tail else tail
    let tr:=if b then tail else e::tail
    let mid:=walk l out jl dl
    have hkeep : Chain out.nodes jump tail := chain_extends (push_extends s e jump rank none) jump tail hc
    have hhead : Chain out.nodes (some s.nodes.size) (e::tail) :=
      Chain.step (push_here s e jump rank none) hkeep
    have hleft : Chain out.nodes jl tl := by cases b <;> assumption
    have hright : Chain mid.nodes jr tr := by
      apply chain_extends (walk_extends l out jl dl)
      cases b <;> assumption
    by_cases hr : HasSource p r
    · obtain ⟨es,hs,hchain⟩:=ihr mid jr dr tr hright hr
      refine ⟨if b then es else es++[e],SourceRoute.right e b l r es hs,?_⟩
      change Chain (walk r mid jr dr).nodes ((walk r mid jr dr).sources.get p) ((if b then es else es++[e])++tail)
      have he : es++tr=(if b then es else es++[e])++tail := by
        cases b <;> simp only [tr,Bool.false_eq_true,if_false,if_true,List.append_assoc,List.singleton_append]
      rw [← he]
      exact hchain
    · have hl : HasSource p l := by
        rcases ht with hl | ht
        · exact hl
        · exact False.elim (hr ht)
      obtain ⟨es,hs,hchain⟩:=ihl out jl dl tl hleft hl
      refine ⟨if b then es++[e] else es,SourceRoute.left e b l r es hs,?_⟩
      have hfinal:=chain_extends (walk_extends r mid jr dr) (mid.sources.get p) (es++tl) hchain
      change Chain (walk r mid jr dr).nodes ((walk r mid jr dr).sources.get p) ((if b then es++[e] else es)++tail)
      rw [walk_source_unchanged r mid jr dr p hr]
      have he : es++tl=(if b then es++[e] else es)++tail := by
        cases b <;> simp only [tl,Bool.false_eq_true,if_false,if_true,List.append_assoc,List.singleton_append]
      rw [← he]
      exact hfinal

/-- The source-address query visits precisely the entries on one actual
source leaf's route, including every light-edge parent and no extra
within-chain ancestors. The executable source table resolves duplicates. -/
theorem build_source_route (t : Heavy.Saved A D E n) (p : Fin (n+1)) (ht : HasSource p t) :
    ∃es,SourceRoute p t es ∧ ∀P : Heavy.Entry A D E n→Prop,
      ((∃c,HeavyIndex.OnChain (build t).nodes ((build t).sources.get p) c ∧ P c.entry) ↔
        ∃e,e∈es ∧ P e) := by
  obtain ⟨es,hs,hchain⟩:=walk_source_route t (empty A D E n) none 0 [] Chain.stop p ht
  rw [List.append_nil] at hchain
  exact ⟨es,hs,fun P=>chain_predicate _ _ _ hchain P⟩

end REWB.BoundaryApplication.Address

namespace REWB.BoundaryApplication.HeavyIndex
variable {σ : Nat}

def LocalEntry (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (source : Fin (w.length+1))
    (right : Nat) (e : Heavy.Entry A D E w.length) : Prop :=
  Local A D E w source right ⟨e,none,0,none⟩

theorem local_entry (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (source : Fin (w.length+1))
    (right : Nat) (c : Address.Cell A D E w.length) :
    Local A D E w source right c ↔ LocalEntry A D E w source right c.entry := Iff.rfl

/-- The complete executable jump query is exactly the disjunction of
its local endpoint predicates along an actual source route. -/
theorem query_route_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (hs : source.val≤g)
    (right : Nat) (hr : right≤w.length) :
    ∃es,Address.SourceRoute source (build A B D E w fallback g hg).paths.saved es ∧
      ((query A B D E w (build A B D E w fallback g hg) source right).value=true ↔
        ∃e,e∈es ∧ LocalEntry A D E w source right e) := by
  let idx:=build A B D E w fallback g hg
  have hsrc : Address.HasSource source idx.paths.saved := by
    apply (Address.go_source A B D E w _ _ _ _ _ _ source).mpr
    exact FixedEnd.trie_source w fallback g hg source hs
  obtain ⟨es,hroute,hpredicate⟩:=Address.build_source_route idx.paths.saved source hsrc
  refine ⟨es,hroute,?_⟩
  rw [query_chain_iff A B D E w fallback g hg source right hr]
  exact hpredicate (LocalEntry A D E w source right)

end REWB.BoundaryApplication.HeavyIndex
