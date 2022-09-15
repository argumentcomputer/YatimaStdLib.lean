namespace Seq

def between [SeqLeft φ] [SeqRight φ] (f : φ α) (h : φ β) (g : φ γ) : φ γ :=
  f *> g <* h

def liftSeq₂ [Seq φ] [Functor φ] (f2 : α → β → γ) (x : φ α)
  : (Unit → φ β) → φ γ := Seq.seq $ f2 <$> x

end Seq
