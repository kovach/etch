import Etch.Stream

namespace Etch.Benchmark.SQL

variable
{ι₁ : Type} [Tagged ι₁] [TaggedC ι₁] [LT ι₁] [@DecidableRel ι₁ LT.lt] [LE ι₁] [@DecidableRel ι₁ LE.le] [Zero ι₁]
{ι₂ : Type} [Tagged ι₂] [TaggedC ι₂] [LT ι₂] [@DecidableRel ι₂ LT.lt] [LE ι₂] [@DecidableRel ι₂ LE.le] [Zero ι₂]
{ι₃ : Type} [Tagged ι₃] [TaggedC ι₃] [LT ι₃] [@DecidableRel ι₃ LT.lt] [LE ι₃] [@DecidableRel ι₃ LE.le] [Zero ι₃]
{ι₄ : Type} [Tagged ι₄] [TaggedC ι₄] [LT ι₄] [@DecidableRel ι₄ LT.lt] [LE ι₄] [@DecidableRel ι₄ LE.le] [Zero ι₄]
{ι₅ : Type} [Tagged ι₅] [TaggedC ι₅] [LT ι₅] [@DecidableRel ι₅ LT.lt] [LE ι₅] [@DecidableRel ι₅ LE.le] [Zero ι₅]
{ι₆ : Type} [Tagged ι₆] [TaggedC ι₆] [LT ι₆] [@DecidableRel ι₆ LT.lt] [LE ι₆] [@DecidableRel ι₆ LE.le] [Zero ι₆]
{α  : Type} [Tagged α]  [One α]
(f : String)
(t₁ t₂ t₃ t₄ := IterMethod.step)

def s   : ι₁ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  Functor.mapConst 1
def s_   : ι₁ →ₛ ι₂ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).inherit <$> ·) ⊚
  Functor.mapConst 1
def d_   : ℕ →ₐ ι₂ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).inherit <$> ·) ⊚
  Functor.mapConst 1
def ss   : ι₁ →ₛ ι₂ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  Functor.mapConst 1
def ds   : ℕ →ₐ ι₂ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level .step <$> ·) ⊚
  Functor.mapConst 1
def dss  : ℕ →ₐ ι₂ →ₛ ι₃ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).level t₃ <$> ·) ⊚
  Functor.mapConst 1
def ds_  : ℕ →ₐ ι₂ →ₛ ι₃ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  Functor.mapConst 1
def ds__ : ℕ →ₐ ι₂ →ₛ ι₃ →ₛ ι₄ →ₛ E α :=
  range |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  ((csr.of f 4 ι₄).inherit <$> ·) ⊚
  Functor.mapConst 1
def ss_ : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  Functor.mapConst 1
def ss__ : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ ι₄ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).inherit <$> ·) ⊚
  ((csr.of f 4 ι₄).inherit <$> ·) ⊚
  Functor.mapConst 1
def sss  : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).level t₃ <$> ·) ⊚
  Functor.mapConst 1
def sss___ : ι₁ →ₛ ι₂ →ₛ ι₃ →ₛ ι₄ →ₛ ι₅ →ₛ ι₆ →ₛ E α :=
  ((csr.of f 1 ι₁).level t₁ 0) |>
  ((csr.of f 2 ι₂).level t₂ <$> ·) ⊚
  ((csr.of f 3 ι₃).level t₃ <$> ·) ⊚
  ((csr.of f 4 ι₄).inherit <$> ·) ⊚
  ((csr.of f 5 ι₅).inherit <$> ·) ⊚
  ((csr.of f 6 ι₆).inherit <$> ·) ⊚
  Functor.mapConst 1

end Etch.Benchmark.SQL
