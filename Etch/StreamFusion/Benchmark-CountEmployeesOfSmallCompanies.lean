import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

abbrev eid   : ℕ := 0
abbrev ename : ℕ := 1
abbrev cid    : ℕ := 2
abbrev cname  : ℕ := 3
abbrev enum   : ℕ := 4
abbrev cstate : ℕ := 5

abbrev EID   := ℕ       -- Employee ID
abbrev ENAME := String  -- Emplyee Name
abbrev CID   := ℕ       -- Company ID
abbrev CNAME := String  -- Company Name
abbrev ENUM  := ℕ       -- Number of employees
abbrev CSTATE := String -- State the company is employed in

@[inline]
def countEmplyeesOfSmallCompanies
    [ToStream E (EID →ₛ ENAME →ₛ CID →ₛ Bool)]
    [ToStream C (CID →ₛ CNAME →ₛ ENUM →ₛ CSTATE →ₛ ℕ)]
    (employeeStream : E)
    (companyStream : C)
    : EID →ₛ ENAME →ₛ Unit →ₛ CNAME →ₛ ENUM →ₛ CSTATE →ₛ ℕ :=

  let S := [(eid,EID),(ename,ENAME),(cid,CID),(cname,CNAME),(enum,ENUM),(cstate,CSTATE)]
  let employees := { S | employeeStream(eid,ename,cid) }
  let companies := { S | companyStream(cid,cname,enum,cstate) }
  let inCal   := S ⇑ (idx (singleton "CA") [cstate])
  let leFifty := S ⇑ (idx (SStream.le 50) [enum])
  let result := Σ cid: inCal * leFifty * employees * companies
  result

end Etch.Verification.SStream
