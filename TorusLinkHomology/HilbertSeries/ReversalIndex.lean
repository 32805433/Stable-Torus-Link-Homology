import TorusLinkHomology.HilbertSeries.ReversalGrading

/-! Finite indices for the homogeneous reversal decomposition. -/
noncomputable section
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

/-- Interpret a bounded passive monomial as an ordinary chain index. -/
def fiberPassiveIndex {p w : ℕ} (t : BoundedMonomial p w) : ChainIndex p :=
  (Finsupp.equivFunOnFinite.symm (fun i => (t.1 i).val), t.2)

@[ext] structure ReversalFiber (N m p C w h : ℕ) where
  passive : BoundedMonomial p w
  a : Fin (w + 1)
  b : Fin (C * w + 1)
  k : Fin (h + 1)
  weight_eq : passiveWeight N m p (fiberPassiveIndex passive) + (m + p) * a.val = w + b.val
  degree_eq : k.val + passive.2.card = h
  support_bound : b.val ≤ C * a.val

instance (N m p C w h : ℕ) : Finite (ReversalFiber N m p C w h) :=
  Finite.of_injective (fun i : ReversalFiber N m p C w h => (i.passive, i.a, i.b, i.k)) (by
    intro i j he
    apply ReversalFiber.ext
    · exact congrArg Prod.fst he
    · exact congrArg (fun d => d.2.1) he
    · exact congrArg (fun d => d.2.2.1) he
    · exact congrArg (fun d => d.2.2.2) he)

instance (N m p C w h : ℕ) : Fintype (ReversalFiber N m p C w h) := Fintype.ofFinite _

namespace ReversalFiber

def passiveIndex {N m p C w h : ℕ} (i : ReversalFiber N m p C w h) : ChainIndex p :=
  fiberPassiveIndex i.passive

def degree {N m p C w h : ℕ} (i : ReversalFiber N m p C w h) : ℕ × ℕ × ℕ :=
  (i.a.val, i.b.val, i.k.val)

theorem eq_of_passiveIndex_degree_eq {N m p C w h : ℕ}
    {i j : ReversalFiber N m p C w h}
    (hp : i.passiveIndex = j.passiveIndex) (hd : i.degree = j.degree) : i = j := by
  apply ReversalFiber.ext
  · apply Prod.ext
    · funext t
      apply Fin.ext
      exact DFunLike.congr_fun (congrArg Prod.fst hp) t
    · exact congrArg (fun t : ChainIndex p => t.2) hp
  · exact Fin.ext (congrArg Prod.fst hd)
  · exact Fin.ext (congrArg (fun d => d.2.1) hd)
  · exact Fin.ext (congrArg (fun d => d.2.2) hd)

end ReversalFiber
end TorusLinkHomology.HilbertSeries.GeneralReversal
