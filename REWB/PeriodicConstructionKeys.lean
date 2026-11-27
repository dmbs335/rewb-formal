import REWB.PeriodicConstructionCache
import REWB.P1ShortKeys

/-! Construct the words and rank arrays consumed by exact trie interning.
The first projection retains the entire legacy record, including its
transition/trie work. The second is accumulated by the actual constructors.
Symbol reads, scalar arithmetic, and trie operations use the existing unit
cost convention; machine integer bits, allocation and GC are not modeled. -/
namespace REWB.PeriodicConstruction.Keys
variable {σ : Nat} {X Y : Type}

theorem map_work_le (f : X→CountedProjection.Result Y) (xs : List X) (c : Nat)
    (h : ∀ x,x∈xs→(f x).2≤c) :
    (CountedProjection.map f xs).2≤xs.length*(c+1)+1 := by
  induction xs with
  | nil=>simp [CountedProjection.map]
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [CountedProjection.map,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def ranks (entries : List (ExactKeys.KeyWord σ×Nat)) : Result (Array Nat) :=
  let ids:=CountedProjection.map (fun e=>(e.2,2)) entries
  let out:=Cache.array ids.1
  (out.1,ids.2+out.2+3)

theorem ranks_value (entries : List (ExactKeys.KeyWord σ×Nat)) :
    (ranks entries).1=(entries.map Prod.snd).toArray := by
  simp only [ranks,Cache.array_value,CountedProjection.map_value]

theorem ranks_work (entries : List (ExactKeys.KeyWord σ×Nat)) :
    (ranks entries).2=5*entries.length+5 := by
  simp only [ranks,Cache.array_work,CountedProjection.map_value,
    List.length_map,CountedProjection.map_plain_steps]
  omega

def takeWord : Nat→List X→Result (List X)
  | 0,_=>([],1)
  | _+1,[]=>([],1)
  | k+1,x::xs=>
    let tail:=takeWord k xs
    (x::tail.1,tail.2+3)

theorem takeWord_value (k : Nat) (xs : List X) : (takeWord k xs).1=xs.take k := by
  induction xs generalizing k with
  | nil=>cases k <;> rfl
  | cons x xs ih=>cases k <;> simp only [takeWord,List.take,ih]

theorem takeWord_work (k : Nat) (xs : List X) : (takeWord k xs).2≤3*xs.length+1 := by
  induction xs generalizing k with
  | nil=>cases k <;> simp [takeWord]
  | cons x xs ih=>
    cases k with
    | zero=>simp [takeWord]
    | succ k=>
      have h:=ih k
      simp only [takeWord,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

def repeatWord (w : Word X) : Nat→Result (Word X)
  | 0=>([],1)
  | m+1=>
    let tail:=repeatWord w m
    let out:=CountedProjection.append tail.1 w
    (out.1,tail.2+out.2+3)

theorem repeatWord_value (w : Word X) (m : Nat) :
    (repeatWord w m).1=Periodic.repeatWord w m := by
  induction m with
  | zero=>rfl
  | succ m ih=>simp only [repeatWord,CountedProjection.append_value,ih,Periodic.repeatWord]

namespace Rotation

def words (s : Nat→Fin σ) (q : Nat) : Result (List (ExactKeys.KeyWord σ)) :=
  let domain:=CountedProjection.range q
  let out:=CountedProjection.map (fun a=>Cache.word s a q) domain.1
  (out.1,domain.2+out.2+3)

theorem words_value (s : Nat→Fin σ) (q : Nat) :
    (words s q).1=ExactKeys.rotations s q := by
  simp only [words,CountedProjection.range_value,CountedProjection.map_value,
    Cache.word_value,ExactKeys.rotations]

theorem words_work (s : Nat→Fin σ) (q : Nat) :
    (words s q).2=4*q^2+4*q+5 := by
  have hm:=CountedProjection.map_steps_constant (fun a=>Cache.word s a q)
    (List.range q) (4*q+1) (fun a _=>Cache.word_work s a q)
  simp only [List.length_range] at hm
  simp only [words,Cache.range_work,CountedProjection.range_value,hm]
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_add,Nat.add_mul,
    Nat.mul_one,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  omega

def intern (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    ExactKeys.PhaseRanks σ×Nat :=
  let ws:=words s q
  let b:=ExactKeys.internMany R ws.1
  let ids:=ranks b.entries
  (⟨b.registry,ids.1,b.work⟩,ws.2+b.work+ids.2+7)

theorem intern_value (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (intern R s q).1=ExactKeys.internRotations R s q := by
  simp only [intern,words_value,ranks_value,ExactKeys.internRotations]

theorem intern_work (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (intern R s q).2=(ExactKeys.internRotations R s q).work+4*q^2+9*q+17 := by
  have hl:=congrArg List.length (ExactKeys.internMany_words R (ExactKeys.rotations s q))
  simp only [List.length_map,ExactKeys.rotations_length] at hl
  simp only [intern,words_work,words_value,ranks_work,hl,ExactKeys.internRotations]
  omega

def tables (R : ExactKeys.Registry σ) (f : Nat→Fin σ) :
    List RunGeometry.Bounds→ExactKeys.RunTables σ×Nat
  | []=>(⟨R,[],0⟩,1)
  | r::rs=>
    let a:=intern R (Periodic.shift f r.lo) r.period
    let b:=tables a.1.registry f rs
    (⟨b.1.registry,(r,a.1.ranks)::b.1.tables,a.1.work+b.1.work⟩,a.2+b.2+5)

theorem tables_value (R : ExactKeys.Registry σ) (f : Nat→Fin σ)
    (rs : List RunGeometry.Bounds) : (tables R f rs).1=ExactKeys.buildRunTables R f rs := by
  induction rs generalizing R with
  | nil=>rfl
  | cons r rs ih=>simp only [tables,intern_value,ih,ExactKeys.buildRunTables]

end Rotation

namespace Short

def word (s : Nat→Fin σ) (q phase rho m : Nat) : Result (ExactKeys.KeyWord σ) :=
  let block:=Cache.word s phase q
  let full:=repeatWord block.1 m
  let tail:=takeWord rho block.1
  let out:=CountedProjection.append full.1 tail.1
  (out.1,block.2+full.2+tail.2+out.2+12)

theorem word_value (s : Nat→Fin σ) (q phase rho m : Nat) :
    (word s q phase rho m).1=P1ShortKeys.word s q phase rho m := by
  simp only [word,CountedProjection.append_value,repeatWord_value,takeWord_value,
    Cache.word_value,P1ShortKeys.word,P1Target.keyWord]

theorem word_work (s : Nat→Fin σ) (q phase rho m : Nat) (hm : m<3) :
    (word s q phase rho m).2≤32*(q+1) := by
  have ht:=takeWord_work rho (Periodic.segment s phase q)
  rw [Periodic.segment_length] at ht
  have casesm : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases casesm with rfl|rfl|rfl <;>
    simp only [word,Cache.word_work,Cache.word_value,repeatWord,
      CountedProjection.append_steps,CountedProjection.append_value,
      List.length_nil,List.nil_append,List.length_append,Periodic.segment_length,
      Nat.mul_add,Nat.mul_one] <;> omega

def words (s : Nat→Fin σ) (q : Nat) : Result (List (ExactKeys.KeyWord σ)) :=
  let domain:=CountedProjection.range (q*q*3)
  let out:=CountedProjection.map (fun i=>
    let w:=word s q (i/3/q) ((i/3)%q) (i%3)
    (w.1,w.2+8)) domain.1
  (out.1,domain.2+out.2+5)

theorem words_value (s : Nat→Fin σ) (q : Nat) :
    (words s q).1=P1ShortKeys.words s q := by
  simp only [words,CountedProjection.map_value,CountedProjection.range_value,
    word_value,P1ShortKeys.words]

theorem words_work (s : Nat→Fin σ) (q : Nat) :
    (words s q).2≤160*q^3+160*q^2+10 := by
  have hm:=map_work_le (fun i=>
    ((word s q (i/3/q) ((i/3)%q) (i%3)).1,
     (word s q (i/3/q) ((i/3)%q) (i%3)).2+8))
    (List.range (q*q*3)) (32*(q+1)+8) (by
      intro i _
      exact Nat.add_le_add_right (word_work s q _ _ _ (Nat.mod_lt _ (by decide))) 8)
  simp only [List.length_range] at hm
  have h96 : (q*q*3)*(32*q)=96*q^3 := by
    rw [show (96:Nat)=3*32 by decide]
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  have h123 : (q*q*3)*41=123*q^2 := by
    rw [show (123:Nat)=3*41 by decide]
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  have hp : (q*q*3)*(32*(q+1)+8+1)+1=96*q^3+123*q^2+1 := by
    rw [show 32*(q+1)+8+1=32*q+41 by omega,Nat.mul_add,h96,h123]
  rw [hp] at hm
  have h6 : 2*(q*q*3)=6*q^2 := by
    rw [show (6:Nat)=2*3 by decide]
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  simp only [words,Cache.range_work,CountedProjection.range_value,h6]
  omega

def intern (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    P1ShortKeys.PhaseRanks σ×Nat :=
  let ws:=words s q
  let b:=ExactKeys.internMany R ws.1
  let ids:=ranks b.entries
  (⟨b.registry,ids.1,b.work⟩,ws.2+b.work+ids.2+7)

theorem intern_value (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (intern R s q).1=P1ShortKeys.internShorts R s q := by
  simp only [intern,words_value,ranks_value,P1ShortKeys.internShorts]

theorem intern_work (R : ExactKeys.Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (intern R s q).2≤(P1ShortKeys.internShorts R s q).work+
      200*(q^3+q^2+1) := by
  have hw:=words_work s q
  have hl:=congrArg List.length (ExactKeys.internMany_words R (P1ShortKeys.words s q))
  simp only [List.length_map,P1ShortKeys.words_length] at hl
  simp only [intern,words_value,ranks_work,hl,P1ShortKeys.internShorts,Nat.mul_add,Nat.mul_one]
  omega

def tables (R : ExactKeys.Registry σ) (f : Nat→Fin σ) :
    List RunGeometry.Bounds→P1ShortKeys.RunTables σ×Nat
  | []=>(⟨R,[],0⟩,1)
  | r::rs=>
    let a:=intern R (Periodic.shift f r.lo) r.period
    let b:=tables a.1.registry f rs
    (⟨b.1.registry,(r,a.1.ranks)::b.1.tables,a.1.work+b.1.work⟩,a.2+b.2+5)

theorem tables_value (R : ExactKeys.Registry σ) (f : Nat→Fin σ)
    (rs : List RunGeometry.Bounds) : (tables R f rs).1=P1ShortKeys.buildRunTables R f rs := by
  induction rs generalizing R with
  | nil=>rfl
  | cons r rs ih=>simp only [tables,intern_value,ih,P1ShortKeys.buildRunTables]

end Short
end REWB.PeriodicConstruction.Keys
