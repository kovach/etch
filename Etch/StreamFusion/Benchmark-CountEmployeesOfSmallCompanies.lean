import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

def_index_group
  EID   := ℕ       -- Employee ID
  ENAME := String  -- Emplyee Name
  CID   := ℕ       -- Company ID
  CNAME := String  -- Company Name
  ENUM  := ℕ       -- Number of employees
  CSTATE := String -- State the company is employed in

open ToStream

@[inline]
def emplyeesOfSmallCompanies
    (employee : EID →ₛ ENAME →ₛ CID →ₛ Bool)
    (company  : CID →ₛ CNAME →ₛ CSTATE →ₛ Bool) :=
  let inCal   := singleton "CA"
  let leFifty := SStream.le 50
  -- convert `Bool` entries to 0/1
  let company := Bool.toNat $[cstate] company(cid, cname, cstate)
  -- count employeeds per company
  let counts : ArrayMap CID ℕ := eval $ Σ eid, ename, cname, cstate: employee(eid,ename,cid) * company
  -- reshape to CID →ₛ Nat →ₛ Bool
  let counts := (stream counts).map singleton
  -- get result of shape EID →ₛ EName →ₛ Bool
  Σ cid,enum,cstate: inCal(cstate) * leFifty(enum) * counts(cid, enum) * employee(eid,ename,cid)

end Etch.Verification.SStream
