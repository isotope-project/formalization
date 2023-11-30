inductive UntypedKind
| term
| block
| cfg

open UntypedKind

inductive Untyped (I: Type u): UntypedKind -> Type u
-- Terms
| var (x: String): Untyped I term
| op (f: F) (a: Untyped I term): Untyped I term
| pair (l r: Untyped I term): Untyped I term
| tt: Untyped I term
| ff: Untyped I term
| nil: Untyped I term
-- Blocks
| br (l: String) (t: Untyped I term): Untyped I block
| ite (e: Untyped I term) (s t: Untyped I block): Untyped I block
| cfg (t: Untyped I block) (C: Untyped I cfg): Untyped I block
-- Let-bindings (shared)
--TODO: add type annotations?
| let1 (k: UntypedKind) (x: String) (e: Untyped I term) (t: Untyped I block)
  : Untyped I k
| let2 (k: UntypedKind) (x: String) (e: Untyped I term) (t: Untyped I block)
  : Untyped I k
-- Control-flow graphs
| cfg_id: Untyped I cfg
| cfg_def (C: Untyped I cfg) (l x: String) (t: Untyped I block): Untyped I cfg
-- Meta
| mvar (k: UntypedKind) (m: String): Untyped I k
