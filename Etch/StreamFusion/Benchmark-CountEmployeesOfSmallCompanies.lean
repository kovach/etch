import Std.Data.HashMap

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

open Std (HashMap)

abbrev Id := ℕ

open ToStream
open SStream

def_index_enum_group
  eid, ename,
  cid, cname, state,
  companySize

-- yields employee Ids who work for companies based in CA with at most 50 employees
def employeesOfSmallCompanies
    (employee : (Id →ₛ String →ₛ Id →ₛ Bool))
    (company  : (Id →ₛ String →ₛ String →ₛ Bool)) :=
  -- label columns
  let employee := employee(eid,ename,cid)
  let company  := company(cid,cname,state)
  -- convert `Bool` entries to 0/1
  let company := Bool.toNat $$[state] company
  -- count employees per company in CA
  let counts := memo(
    select cid => employee * I(state = "CA") * company with
    HashMap Id ℕ)
  let counts := (fun id => singleton (counts id))(cid, companySize)
  --let counts := (counts.map singleton)(cid, companySize)
  let small := I(companySize ≤ 50)
  -- get result of shape eid~Id →ₛ Bool
  select eid => small * counts * employee

end Etch.Verification.SStream
