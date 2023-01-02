def USize.nextPowerOfTwo (n : USize) : USize :=
  if n == 0 then 1 else
  (1 <<< (n.toNat.log2 + 1).toUSize)
