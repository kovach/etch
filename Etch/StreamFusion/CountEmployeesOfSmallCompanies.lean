import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

abbrev EID   := ℕ       -- Employee ID
abbrev ENAME := String  -- Emplyee Name

abbrev eid   : ℕ := 0
abbrev ename : ℕ := 1

abbrev CID   := ℕ       -- Company ID
abbrev CNAME := String  -- Company Name
abbrev ENUM  := ℕ       -- Number of employees
abbrev CSTATE := String -- State the company is employed in

abbrev cid    : ℕ := 2
abbrev cname  : ℕ := 3
abbrev enum   : ℕ := 4
abbrev cstate : ℕ := 5

def companyInCal (company : String) : Bool := if company = "CA" then true else false
def leFiftyEmployees (employeeNum : ℕ) : Bool := if employeeNum < 50 then true else false

@[inline]
def countEmplyeesOfSmallCompanies
    [ToStream E (EID →ₛ ENAME →ₛ CID →ₛ ℕ)]
    [ToStream C (CID →ₛ CNAME →ₛ ENUM →ₛ CSTATE →ₛ ℕ)]
    (employeeStream : E)
    (companyStream : C)
    : EID →ₛ ENAME →ₛ Unit →ₛ CNAME →ₛ ENUM →ₛ CSTATE →ₛ ℕ :=
  let qshape := [(eid,EID),(ename,ENAME),(cid,CID),(cname,CNAME),(enum,ENUM),(cstate,CSTATE)]
  let employees := { qshape | employeeStream(eid,ename,cid) }
  let companies := { qshape | companyStream(cid,cname,enum,cstate) }
  let inCal   := { qshape | companyInCal(cstate) }
  let leFifty := { qshape | leFiftyEmployees(enum) }
  let result : EID →ₛ ENAME →ₛ Unit →ₛ CNAME →ₛ ENUM →ₛ CSTATE →ₛ ℕ :=
    Σ cid, employees * companies * inCal * leFifty
  42

-- def _root_.main (args : List String) : IO Unit := do
end Etch.Verification.SStream
