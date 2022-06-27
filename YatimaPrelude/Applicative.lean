namespace Applicative

def liftA₂ [Applicative F] (f : A → B → C) 
           (fx : F A) (fy : F B) : F C := 
  f <$> fx <*> fy

end Applicative