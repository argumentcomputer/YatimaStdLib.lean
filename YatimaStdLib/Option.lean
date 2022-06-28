namespace Option

def option (b : B) (f : A → B) (oa : Option A) : B :=
  match oa with
    | Option.none => b
    | Option.some x => f x

end Option