import verification.stream_add
import verification.verify

-- Think: ι = (Expr nn), ι' = ℕ, α = Expr ℝ, α' = ℝ
variables {R : Type} [semiring R] {ι ι' : Type} {α α' : Type} [has_zero α] [has_add α]
  [add_comm_monoid α']


instance {α : Type} [has_zero α] : has_zero (BoundedStreamGen R ι α) := sorry

def BoundedStreamGen.add  (a : BoundedStreamGen R ι α) (b : BoundedStreamGen R ι α) :
  BoundedStreamGen R ι α := sorry

instance : has_add (BoundedStreamGen R ι α) := ⟨BoundedStreamGen.add⟩

open TRAble (tr)

@[simp] def BoundedStreamGen.add_spec [TRAble R ι ι'] [TRAble R α α']
  (a : BoundedStreamGen R ι α) (b : BoundedStreamGen R ι α) 
  (ctx : EContext R) :
  StreamExec.eval (tr ctx (a + b)) = (StreamExec.eval $ tr ctx a) + (StreamExec.eval $ tr ctx b) := sorry

example [TRAble R ι ι'] [TRAble R α α'] (x y : BoundedStreamGen R ι (BoundedStreamGen R ι α)) (ctx : EContext R) : false :=
begin
  let t : BoundedStreamGen R ι (BoundedStreamGen R ι α) := x + y,
  let s : StreamExec _ ι' (StreamExec _ ι' α') := tr ctx (x + y),
end

example [TRAble R ι ι'] [TRAble R α α'] (a b : BoundedStreamGen R ι (BoundedStreamGen R ι α)) (ctx : EContext R) :
  (tr ctx (a + b) : StreamExec (EContext R) ι' (StreamExec (EContext R) ι' α')) = 


-- lemma Stream_add_nested (a : StreamExec σ₁ ι₁ (StreamExec σ₂ ι₂ α))
--   (b : StreamExec σ₃ ι₁ (StreamExec σ₄ ι₂ α)) 
--   (ha : a.bound_valid) (hb : b.bound_valid) :
--   /- (a +ₑ b).eval = -/
--   let x := (StreamExec.eval <$₂> (a +ₑ b)) in _ :=
-- by { rw StreamExec.add_spec; simpa, }
