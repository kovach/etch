import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

/-
def_index_group
  eid~EID       := ℕ       -- Employee ID
  ename~ENAME   := String  -- Emplyee Name
  cid~CID       := ℕ       -- Company ID
  cname~CNAME   := String  -- Company Name
  enum~ENUM     := ℕ       -- Number of employees
  state~CSTATE := String  -- State the company is employed in
  companySize~COMPANYSIZE := ℕ
  -/



abbrev Id := ℕ

open ToStream
open SStream

def_index_enum_group
  eid,
  ename,
  cid,
  cname,
  enum,
  state,
  companySize

-- yields employee Ids who work for companies based in CA with at most 50 employees
def emplyeesOfSmallCompanies
    (employee : (Id →ₛ String →ₛ Id →ₛ Bool))
    (company  : (Id →ₛ String →ₛ String →ₛ Bool)) :=
  -- label columns
  let employee := employee(eid,ename,cid)
  let company  := company(cid,cname,state)
  -- convert `Bool` entries to 0/1
  let company := Bool.toNat $[state] company
  -- count employees per company in CA
  let counts : SparseArray Id ℕ := eval $
    Σ eid, ename, cname, state: employee * (singleton "CA")(state) * company
  -- reshape to CID →ₛ Nat →ₛ Bool
  let counts := ((stream counts).map singleton)(cid, companySize)
  let small := (le 50)(companySize)
  -- get result of shape eid~Id →ₛ Bool
  Σ ename,cid,companySize: small * counts * employee

@[inline]
def emplyeesOfSmallCompanies'
    (employee : (EID →ₛ ENAME →ₛ CID →ₛ Bool))
    (company  : (CID →ₛ CNAME →ₛ CSTATE →ₛ Bool)) :=
  let inCal   := singleton "CA"
  let leFifty := SStream.le 50
  -- convert `Bool` entries to 0/1
  let company := Bool.toNat $[state] company(cid, cname, state)
  -- count employees per company
  let counts : SparseArray CID ℕ := eval $ Σ eid, ename, cname, state: employee(eid,ename,cid) * company
  -- reshape to CID →ₛ Nat →ₛ Bool
  let counts := (stream counts).map singleton
  -- get result of shape EID →ₛ EName →ₛ Bool
  Σ cid,enum,state: inCal(state) * leFifty(enum) * counts(cid, enum) * employee(eid,ename,cid)

end Etch.Verification.SStream
