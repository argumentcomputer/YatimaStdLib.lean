def USize.next_power_of_two (n : USize) : USize :=
  if n == 0 then 1 else
  let exp := n.toNat.log2 + 1
  (1 <<< exp.toUSize)