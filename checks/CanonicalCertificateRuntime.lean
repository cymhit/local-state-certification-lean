import Lean
import LocalCertification.Certificates.CanonicalCertificateConsumers
import LocalCertification.Certificates.TableValues
open scoped BigOperators
open LocalCertification.Certificates LocalCertification.Certificates.Consumers LocalCertification.Certificates.Examples
#eval [(0,canonicalRawCheck 3 0 (seedCertificate 3 0)),
  (1,canonicalRawCheck 3 1 degreeOneCertificate),
  (2,canonicalRawCheck 3 2 Degree2.data),
  (3,canonicalRawCheck 3 3 Degree3.data),
  (4,canonicalRawCheck 3 4 Degree4.data),
  (5,canonicalRawCheck 3 5 Degree5.data),
  (6,canonicalRawCheck 3 6 Degree6.data),
  (7,canonicalRawCheck 3 7 Degree7.data),
  (8,canonicalRawCheck 3 8 Degree8.data),
  (9,canonicalRawCheck 3 9 Degree9.data),
  (10,canonicalRawCheck 3 10 Degree10.data)]
#eval ((seedCertificate 3 0).2.2.2.2 1, arrayEval 1 (canonicalRawQ 0 (seedCertificate 3 0)) 0)
#eval (Degree10.data.2.2.1, List.ofFn Degree10.data.2.2.2.1)
#eval ∑ i : Fin 2, (seedCertificate 3 0).2.2.2.2 i * executableNodeMonomial 3 0 ((seedCertificate 3 0).2.2.2.1 i)


#eval do
  let flags := [canonicalRawCheck 3 0 (seedCertificate 3 0),
    canonicalRawCheck 3 1 degreeOneCertificate, canonicalRawCheck 3 2 Degree2.data,
    canonicalRawCheck 3 3 Degree3.data, canonicalRawCheck 3 4 Degree4.data,
    canonicalRawCheck 3 5 Degree5.data, canonicalRawCheck 3 6 Degree6.data,
    canonicalRawCheck 3 7 Degree7.data, canonicalRawCheck 3 8 Degree8.data,
    canonicalRawCheck 3 9 Degree9.data, canonicalRawCheck 3 10 Degree10.data]
  unless flags == List.replicate 11 true do throw (IO.userError "Canonical degrees 0 through 10 failed")
  unless ((seedCertificate 3 0).2.2.2.2 1, arrayEval 1 (canonicalRawQ 0 (seedCertificate 3 0)) 0) == (-2,1) do
    throw (IO.userError "Degree-zero normalization changed")
  unless (Degree10.data.2.2.1,List.ofFn Degree10.data.2.2.2.1) ==
    (18,[some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 8,some 10,some 13,some 17,none]) do
    throw (IO.userError "Degree-ten certificate nodes changed")
  unless (∑ i : Fin 2, (seedCertificate 3 0).2.2.2.2 i * executableNodeMonomial 3 0 ((seedCertificate 3 0).2.2.2.1 i)) == 1 do
    throw (IO.userError "Degree-zero reproduction changed")
  IO.println "RUNTIME_CHECK\tcanonical_certificates_0_through_10_pass"

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tCanonicalCertificateRuntime\tPASS"
