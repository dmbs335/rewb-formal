import REWB.PeriodicConstructionMaskedBranch
import REWB.MaskedClusterOrbit

/-! Actual fixed-pattern modulus preparation. All shape enumeration,
literal erasure, DNF products, projection, GCD/LCM folds and list copies
are executed by the measured definitions. The resulting work is itself
a concrete function of the fixed DFA state counts. No input text or
per-run endpoint is passed to either public preparation function. -/
namespace REWB.PeriodicConstruction.Pattern
open REWB.AffineProjection
open REWB.PeriodicConstruction

def gcd (m n : Nat) : Result Nat :=
  if hm : m=0 then (n,1)
  else let rest:=gcd (n%m) m; (rest.1,rest.2+3)
termination_by m
decreasing_by exact Nat.mod_lt n (Nat.pos_of_ne_zero hm)

theorem gcd_value (m n : Nat) : (gcd m n).1=Nat.gcd m n := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih=>
    rw [gcd,Nat.gcd_def]
    split
    · rfl
    · rename_i hm
      exact ih (n%m) (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)) m

def lcm (m n : Nat) : Result Nat :=
  let g:=gcd m n
  (m*n/g.1,g.2+2)

theorem lcm_value (m n : Nat) : (lcm m n).1=Nat.lcm m n := by
  simp only [lcm,gcd_value,Nat.lcm]

def eraseAff : Aff→Result Aff
  | .lit _=>(.lit 0,1)
  | .var i=>(.var i,1)
  | .add a b=>let x:=eraseAff a; let y:=eraseAff b; (.add x.1 y.1,x.2+y.2+1)
  | .scale c a=>let x:=eraseAff a; (.scale c x.1,x.2+1)

theorem eraseAff_value (a : Aff) : (eraseAff a).1=LiteralShape.aff a := by
  induction a <;> simp_all only [eraseAff,LiteralShape.aff]

def eraseAtom : Atom→Result Atom
  | .le a=>let x:=eraseAff a; (.le x.1,x.2+1)
  | .dvd m a=>let x:=eraseAff a; (.dvd m x.1,x.2+1)

theorem eraseAtom_value (a : Atom) : (eraseAtom a).1=LiteralShape.atom a := by
  cases a <;> simp only [eraseAtom,eraseAff_value,LiteralShape.atom]

def eraseFormula (F : AffineProjection.Formula) : Result AffineProjection.Formula :=
  CountedProjection.map (CountedProjection.map eraseAtom) F

theorem eraseFormula_value (F : AffineProjection.Formula) :
    (eraseFormula F).1=LiteralShape.formula F := by
  simp only [eraseFormula,CountedProjection.map_value,eraseAtom_value,LiteralShape.formula,LiteralShape.conj]
  rfl

def replicate (n : Nat) (x : X) : Result (List X) :=
  match n with
  | 0=>([],1)
  | k+1=>let out:=replicate k x; (x::out.1,out.2+1)

theorem replicate_value (n : Nat) (x : X) : (replicate n x).1=List.replicate n x := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [replicate,ih,List.replicate_succ]

def descriptorCell (t : Aff) (i j m : Nat) : Result AffineProjection.Formula :=
  let exacts:=replicate i (exactCount t 0)
  let tails:=replicate j (progression t 0 m)
  let combined:=CountedProjection.append exacts.1 tails.1
  (combined.1,exacts.2+tails.2+combined.2+25)

theorem descriptorCell_value (t : Aff) (i j m : Nat) :
    (descriptorCell t i j m).1=List.replicate i (exactCount t 0)++List.replicate j (progression t 0 m) := by
  simp only [descriptorCell,CountedProjection.append_value,replicate_value]

def descriptors (S : Nat) (t : Aff) : Result UniformProjection.Family :=
  let positions:=CountedProjection.range (S+1)
  let out:=CountedProjection.flatMap (fun i=>
    CountedProjection.flatMap (fun j=>
      CountedProjection.map (descriptorCell t i j) positions.1) positions.1) positions.1
  (out.1,positions.2+out.2+2)

theorem descriptors_value (S : Nat) (t : Aff) :
    (descriptors S t).1=UniformProjection.descriptors S t := by
  simp only [descriptors,CountedProjection.flatMap_value,CountedProjection.map_value,
    CountedProjection.range_value,descriptorCell_value,UniformProjection.descriptors]

def combine (fs gs : UniformProjection.Family) : Result UniformProjection.Family :=
  CountedProjection.flatMap (fun F=>CountedProjection.map (Formula.both F) gs) fs

theorem combine_value (fs gs : UniformProjection.Family) :
    (combine fs gs).1=UniformProjection.combine fs gs := by
  simp only [combine,CountedProjection.flatMap_value,CountedProjection.map_value,
    Formula.both_value,UniformProjection.combine]

def branchFamily (b c e : Nat) (branch : MaskedPeriodic.Branch) : Result UniformProjection.Family :=
  let bounds:=Masked.bounds branch 0
  let erased:=eraseFormula bounds.1
  let capAff:=eraseAff MaskedPeriodic.aExpr
  let gapAff:=eraseAff (MaskedPeriodic.gapExpr branch)
  let tailAff:=eraseAff (MaskedPeriodic.tailExpr branch 0)
  let cap:=descriptors b capAff.1
  let gap:=descriptors c gapAff.1
  let tail:=descriptors e tailAff.1
  let right:=combine gap.1 tail.1
  let middle:=combine cap.1 right.1
  let out:=combine [erased.1] middle.1
  (out.1,bounds.2+erased.2+capAff.2+gapAff.2+tailAff.2+cap.2+gap.2+tail.2+right.2+middle.2+out.2+20)

theorem branchFamily_value (b c e : Nat) (branch : MaskedPeriodic.Branch) :
    (branchFamily b c e branch).1=MaskedPeriodic.branchFamily b c e branch := by
  simp only [branchFamily,combine_value,eraseFormula_value,Masked.bounds_value,
    descriptors_value,eraseAff_value,MaskedPeriodic.branchFamily]

def family (b c e : Nat) : Result UniformProjection.Family :=
  let a:=branchFamily b c e .zero
  let d:=branchFamily b c e .interior
  let f:=branchFamily b c e .ending
  let df:=CountedProjection.append d.1 f.1
  let out:=CountedProjection.append a.1 df.1
  (out.1,a.2+d.2+f.2+df.2+out.2+4)

theorem family_value (b c e : Nat) : (family b c e).1=MaskedPeriodic.family b c e := by
  simp only [family,CountedProjection.append_value,branchFamily_value,MaskedPeriodic.family]

def conjModulus : Conj→Result Nat
  | []=>(1,1)
  | a::as=>
    let tail:=conjModulus as
    let out:=lcm (UniformProjection.atomModulus a) tail.1
    (out.1,tail.2+out.2+3)

theorem conjModulus_value (C : Conj) : (conjModulus C).1=MaskedPeriodic.Modulus.conj C := by
  induction C with
  | nil=>rfl
  | cons a as ih=>simp only [conjModulus,lcm_value,ih,MaskedPeriodic.Modulus.conj]

def formulaModulus : AffineProjection.Formula→Result Nat
  | []=>(1,1)
  | C::Cs=>
    let first:=conjModulus C
    let tail:=formulaModulus Cs
    let out:=lcm first.1 tail.1
    (out.1,first.2+tail.2+out.2+2)

theorem formulaModulus_value (F : AffineProjection.Formula) :
    (formulaModulus F).1=MaskedPeriodic.Modulus.formula F := by
  induction F with
  | nil=>rfl
  | cons C Cs ih=>simp only [formulaModulus,lcm_value,conjModulus_value,ih,MaskedPeriodic.Modulus.formula]

def familyModulus (k : Nat) : UniformProjection.Family→Result Nat
  | []=>(1,1)
  | F::Fs=>
    let projected:=CountedProjection.project k F
    let first:=formulaModulus projected.1
    let tail:=familyModulus k Fs
    let out:=lcm first.1 tail.1
    (out.1,projected.2+first.2+tail.2+out.2+3)

theorem familyModulus_value (k : Nat) (Fs : UniformProjection.Family) :
    (familyModulus k Fs).1=MaskedPeriodic.Modulus.family k Fs := by
  induction Fs with
  | nil=>rfl
  | cons F Fs ih=>simp only [familyModulus,lcm_value,formulaModulus_value,
      CountedProjection.project_value,ih,MaskedPeriodic.Modulus.family]

def preparePattern (b c e : Nat) : Result (MaskedPeriodic.PreparedPattern b c e) :=
  let shapes:=family b c e
  let modulus:=familyModulus 1 shapes.1
  (⟨modulus.1,by simp only [modulus,shapes,familyModulus_value,family_value,MaskedPeriodic.modulus]⟩,
    shapes.2+modulus.2+2)

theorem preparePattern_value (b c e : Nat) :
    (preparePattern b c e).1=MaskedPeriodic.preparePattern b c e := by
  simp only [preparePattern,familyModulus_value,family_value,MaskedPeriodic.preparePattern,MaskedPeriodic.modulus]

def patternCost (b c e : Nat) : Nat := (preparePattern b c e).2

theorem preparePattern_work (b c e : Nat) : (preparePattern b c e).2=patternCost b c e := rfl

def common : Nat→Result Nat
  | 0=>(1,1)
  | k+1=>
    let tail:=common k
    let out:=lcm (k+1) tail.1
    (out.1,tail.2+out.2+2)

theorem common_value (k : Nat) : (common k).1=MaskedCluster.common k := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [common,lcm_value,ih,MaskedCluster.common]

def prepareCluster (m n : Nat) : Result (MaskedCluster.Prepared m n) :=
  let out:=common (max m n)
  (⟨out.1,by simp only [out,common_value,MaskedCluster.modulus]⟩,out.2+3)

theorem prepareCluster_value (m n : Nat) : (prepareCluster m n).1=MaskedCluster.prepare m n := by
  simp only [prepareCluster,common_value,MaskedCluster.prepare,MaskedCluster.modulus]

def clusterCost (m n : Nat) : Nat := (prepareCluster m n).2

theorem prepareCluster_work (m n : Nat) : (prepareCluster m n).2=clusterCost m n := rfl

end REWB.PeriodicConstruction.Pattern
