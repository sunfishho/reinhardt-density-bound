import Certificate.Potential.DifferentialSemantics
import Certificate.NumericBound
import Certificate.PrimitiveData
namespace Certificate.NewCertificate
open Certificate.Sparse Certificate.Potential
set_option maxHeartbeats 0
def OnRegion (x : State) : Prop :=
  x.determinantConstraints ∧ PrimitiveData.Region x.coordinates

end Certificate.NewCertificate
