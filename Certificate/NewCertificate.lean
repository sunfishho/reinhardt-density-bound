import Certificate.NewCertificateVertex0
import Certificate.NewCertificateVertex1
import Certificate.NewCertificateVertex2
import Certificate.NewCertificateBoundary
namespace Certificate.NewCertificate
open Certificate.Sparse Certificate.Potential
set_option maxHeartbeats 0
theorem differential (x : State) (hx : OnRegion x) (k : Fin 3) :
    0 ≤ denominatorAt x (vertex k)*(x.cost-dG x)-dX x k := by
  fin_cases k
  · exact differential_0 x hx
  · exact differential_1 x hx
  · exact differential_2 x hx

#print axioms differential
#print axioms boundary
end Certificate.NewCertificate
