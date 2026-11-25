import Lean
import LocalCertification.Certificates.StagedSearchConsumers
open scoped BigOperators
open LocalCertification.Certificates LocalCertification.Certificates.Consumers

#eval stagedRationals 1
#eval (List.range 4).map fun N => (N,(stagedData 0 N).length)
#eval (List.range 4).map fun N => (N,(stagedFind (3/2) 0 N).isSome)
#eval stagedSearchIndex (3/2) (by norm_num) 0
#eval (stagedGamma (3/2) (by norm_num) 0,List.ofFn (stagedPolynomial (3/2) (by norm_num) 0))
#eval let d := stagedSearch (3/2) (by norm_num) 0
  (d.1,List.ofFn d.2.1,d.2.2.1,List.ofFn d.2.2.2.1,List.ofFn d.2.2.2.2,
    canonicalRawCheck (3/2) 0 d,2/(1+∑ i, |d.2.2.2.2 i|))
#eval [stagedDataBound 0 (seedCertificate 3 0),stagedDataBound 1 degreeOneCertificate,
  stagedDataBound 2 Examples.Degree2.data,stagedDataBound 10 Examples.Degree10.data]
#eval canonicalRawCheck 3 10 Examples.Degree10.data


#eval do
  unless stagedRationals 1 == [-1,0,1] do throw (IO.userError "Stage rational enumeration changed")
  unless ((List.range 4).map fun N => (N,(stagedData 0 N).length)) == [(0,0),(1,27),(2,3000),(3,55566)] do
    throw (IO.userError "Stage sizes changed")
  unless ((List.range 4).map fun N => (N,(stagedFind (3/2) 0 N).isSome)) == [(0,false),(1,false),(2,false),(3,true)] do
    throw (IO.userError "First successful stage changed")
  unless stagedSearchIndex (3/2) (by norm_num) 0 == 3 do throw (IO.userError "Stage index changed")
  unless (stagedGamma (3/2) (by norm_num) 0,List.ofFn (stagedPolynomial (3/2) (by norm_num) 0)) == (2/3,[1]) do
    throw (IO.userError "Staged value/polynomial changed")
  let d := stagedSearch (3/2) (by norm_num) 0
  unless (d.1,List.ofFn d.2.1,d.2.2.1,List.ofFn d.2.2.2.1,List.ofFn d.2.2.2.2,
    canonicalRawCheck (3/2) 0 d,2/(1+∑ i, |d.2.2.2.2 i|)) ==
      (-1,[3],1,[some 0,none],[3/2,-1/2],true,2/3) do
    throw (IO.userError "Canonical staged certificate changed")
  unless [stagedDataBound 0 (seedCertificate 3 0),stagedDataBound 1 degreeOneCertificate,
      stagedDataBound 2 Examples.Degree2.data,stagedDataBound 10 Examples.Degree10.data] ==
      [6,18,93,218193293112653] do throw (IO.userError "Finite stage bounds changed")
  unless canonicalRawCheck 3 10 Examples.Degree10.data do throw (IO.userError "Degree-ten runtime certificate failed")
  IO.println "RUNTIME_CHECK\tfinite_stage_search_pass"

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tStagedSearchRuntime\tPASS"
