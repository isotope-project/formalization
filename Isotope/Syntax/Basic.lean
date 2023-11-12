inductive SSA (I: Type)
-- Terms
| var (x: nat)
| op (f: F) (arg: SSA I)
| pair (l r: SSA I)
| let_tm (e a: SSA I)
| let2_tm (e a: SSA I)
| tt
| ff
| nil
-- Blocks
| br (l: Nat) (t: SSA I)
| ret (t: SSA I)
| let_blk (e a: SSA I)
| let2_blk (e a: SSA I)
| ite (e s t: SSA I)
| cfg (t: SSA I) (m: Nat) (L: Fin m -> SSA I)
-- Meta
| mvar (m: nat)
