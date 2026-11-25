import REWB.MaskedClusterLeaders
import REWB.MaskedLocalAnchor

/-! Exact arithmetic-progression geometry of a completed dense component.
The first successor is supplied by the measured ordered-set query in the
caller. Finite-list predecessor selection below is used only in proofs;
no descriptor, occurrence list traversal, or period finder is executable
in this module. Neither source nor target masks enter the premises. -/
namespace REWB.MaskedClusterDescriptor
open REWB.Periodic REWB.MaskedRunDiscovery REWB.MaskedLocalAnchor
open REWB.MaskedClusterLeaders (Leader)
variable {α : Type}

/-- A nonleader's true predecessor must be separated by a dense gap. -/
theorem nonleader_dense (xs : List Nat) (L a b : Nat) (ha : Adjacent xs a b)
    (hn : ¬Leader xs L b) : 2*(b-a)≤L := by
  by_cases hd : 2*(b-a)≤L
  · exact hd
  · exfalso
    apply hn
    refine ⟨ha.2.1,?_⟩
    intro x hx hxb
    have hxa : x≤a := by
      by_cases hh : a<x
      · exact False.elim (ha.2.2.2 x hx hh hxb)
      · omega
    omega

/-- The first dense adjacency fixes every later internal adjacent gap. -/
theorem component_gap (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (s t u : Nat)
    (hfirst : Adjacent xs s u) (hu : u≤t)
    (hleaders : ∀x,x∈xs→s<x→x≤t→¬Leader xs L x)
    (a b : Nat) (hab : Adjacent xs a b) (hsa : s≤a) (hbt : b≤t) : b-a=u-s := by
  have hsu:=hfirst.2.2.1
  have hd:=nonleader_dense xs L s u hfirst (hleaders u hfirst.2.1 hsu hu)
  have hm:=complete_least f n base L xs hfull s u a hfirst hd hab.1
  have hab':=hab.2.2.1
  have hdb:=nonleader_dense xs L a b hab (hleaders b hab.2.1 (by omega) hbt)
  exact dense_consecutive_gap (by omega) hdb
    (complete_consecutive f n base L xs a b hfull hab) hm

/-- Finite predecessor existence for specifications, without any ordering
or distinctness assumption on the list representation. -/
theorem max_below (xs : List Nat) (bound : Nat)
    (hex : ∃x,x∈xs ∧ x<bound) :
    ∃p,p∈xs ∧ p<bound ∧ ∀x,x∈xs→x<bound→x≤p := by
  classical
  induction xs with
  | nil => obtain ⟨x,hx,_⟩:=hex; cases hx
  | cons a xs ih =>
    by_cases ht : ∃x,x∈xs ∧ x<bound
    · obtain ⟨p,hp,hpb,hmax⟩:=ih ht
      by_cases ha : a<bound ∧ p<a
      · refine ⟨a,List.mem_cons_self,ha.1,?_⟩
        intro x hx hxb
        rcases List.mem_cons.mp hx with he|hm
        · omega
        · have hh:=hmax x hm hxb; omega
      · refine ⟨p,List.mem_cons_of_mem a hp,hpb,?_⟩
        intro x hx hxb
        rcases List.mem_cons.mp hx with he|hm
        · omega
        · exact hmax x hm hxb
    · have ha : a<bound := by
        obtain ⟨x,hx,hxb⟩:=hex
        rcases List.mem_cons.mp hx with he|hm
        · omega
        · exact False.elim (ht ⟨x,hm,hxb⟩)
      refine ⟨a,List.mem_cons_self,ha,?_⟩
      intro x hx hxb
      rcases List.mem_cons.mp hx with he|hm
      · omega
      · exact False.elim (ht ⟨x,hm,hxb⟩)

theorem predecessor_exists (xs : List Nat) (s x : Nat)
    (hs : s∈xs) (hx : x∈xs) (hsx : s<x) :
    ∃p,Adjacent xs p x ∧ s≤p := by
  obtain ⟨p,hp,hpx,hmax⟩:=max_below xs x ⟨s,hs,hsx⟩
  refine ⟨p,⟨hp,hx,hpx,?_⟩,hmax s hs hsx⟩
  intro y hy hpy hyx
  have hh:=hmax y hy hyx
  omega

/-- Uniform adjacent gaps force every actual member to have an integral
progression coordinate measured from the left endpoint. -/
theorem member_multiple (xs : List Nat) (s t q : Nat) (hs : s∈xs)
    (hgap : ∀a b,Adjacent xs a b→s≤a→b≤t→b-a=q)
    (x : Nat) (hx : x∈xs) (hsx : s≤x) (hxt : x≤t) :
    ∃k,x=s+k*q := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases he : x=s
    · exact ⟨0,by simp [he]⟩
    · obtain ⟨p,ha,hsp⟩:=predecessor_exists xs s x hs hx (by omega)
      have hpx:=ha.2.2.1
      obtain ⟨k,hk⟩:=ih p hpx ha.1 hsp (by omega)
      have hd:=hgap p x ha hsp hxt
      refine ⟨k+1,?_⟩
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- No integral grid position can be missing: walking backwards through
true predecessor adjacencies realizes every coordinate below a member. -/
theorem fill_multiples (xs : List Nat) (s t q : Nat) (hq : 0<q) (hs : s∈xs)
    (hgap : ∀a b,Adjacent xs a b→s≤a→b≤t→b-a=q)
    (k : Nat) (hb : s+k*q≤t) (hk : s+k*q∈xs) :
    ∀j,j≤k→s+j*q∈xs := by
  induction k with
  | zero =>
    intro j hj
    have he : j=0 := by omega
    simpa only [he,Nat.zero_mul,Nat.add_zero] using hs
  | succ k ih =>
    have hxe : s+(k+1)*q=s+k*q+q := by rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
    obtain ⟨p,ha,hsp⟩:=predecessor_exists xs s (s+(k+1)*q) hs hk (by omega)
    have hd:=hgap p (s+(k+1)*q) ha hsp hb
    have hpx:=ha.2.2.1
    have hp : p=s+k*q := by omega
    have hmember : s+k*q∈xs := by rw [←hp]; exact ha.1
    have hbound : s+k*q≤t := by omega
    intro j hj
    by_cases he : j=k+1
    · simpa only [he] using hk
    · exact ih hbound hmember j (by omega)

/-- A finite interval with uniform actual adjacent gaps is exactly a
closed arithmetic progression, with the endpoint quotient as its length. -/
theorem interval_progression (xs : List Nat) (s t q : Nat) (hs : s∈xs) (ht : t∈xs)
    (hst : s<t) (hq : 0<q)
    (hgap : ∀a b,Adjacent xs a b→s≤a→b≤t→b-a=q) :
    0<(t-s)/q ∧ t=s+((t-s)/q)*q ∧
      ∀x,(x∈xs ∧ s≤x ∧ x≤t ↔ ∃k,k≤(t-s)/q ∧ x=s+k*q) := by
  obtain ⟨m,hm⟩:=member_multiple xs s t q hs hgap t ht (by omega) (Nat.le_refl _)
  have hdiff : t-s=m*q := by omega
  have hquot : (t-s)/q=m := by rw [hdiff,Nat.mul_div_cancel m hq]
  have hpos : 0<m := by
    by_cases hz : m=0
    · simp [hz] at hm
      omega
    · omega
  refine ⟨by omega,by rw [hquot]; exact hm,?_⟩
  intro x
  constructor
  · rintro ⟨hx,hsx,hxt⟩
    obtain ⟨k,hk⟩:=member_multiple xs s t q hs hgap x hx hsx hxt
    have hkm : k*q≤m*q := by omega
    exact ⟨k,by have hh:=Nat.le_of_mul_le_mul_right hkm hq; omega,hk⟩
  · rintro ⟨k,hk,rfl⟩
    have hkm : k≤m := by omega
    have hmul:=Nat.mul_le_mul_right q hkm
    have hbound : s+m*q≤t := by omega
    have hlast : s+m*q∈xs := by rw [←hm]; exact ht
    exact ⟨fill_multiples xs s t q hq hs hgap m hbound hlast k hkm,by omega,by omega⟩

/-- Principal descriptor theorem. `u` is the actual first successor and
there is no further leader through `t`. Completeness is essential: this
statement is not valid for temporary partial-merge occurrence classes. -/
theorem component_progression (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (s t u : Nat) (hs : s∈xs) (ht : t∈xs) (hst : s<t)
    (hfirst : Adjacent xs s u) (hu : u≤t)
    (hleaders : ∀x,x∈xs→s<x→x≤t→¬Leader xs L x) :
    0<u-s ∧ 0<(t-s)/(u-s) ∧ 2*(u-s)≤L ∧
    t=s+((t-s)/(u-s))*(u-s) ∧ LeastPeriod (shift f s) L (u-s) ∧
    ∀x,(x∈xs ∧ s≤x ∧ x≤t ↔ ∃k,k≤(t-s)/(u-s) ∧ x=s+k*(u-s)) := by
  have hsu:=hfirst.2.2.1
  have hd:=nonleader_dense xs L s u hfirst (hleaders u hfirst.2.1 hsu hu)
  have hg:=component_gap f n base L xs hfull s t u hfirst hu hleaders
  have hp:=interval_progression xs s t (u-s) hs ht hst (by omega) hg
  exact ⟨by omega,hp.1,hd,hp.2.1,complete_least f n base L xs hfull s u s hfirst hd hs,hp.2.2⟩

end REWB.MaskedClusterDescriptor
