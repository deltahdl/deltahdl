#include <cstdint>
#include <string>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_nets.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The Annex K constant of a drive strength as the parser holds it, from 1 for
// highz up to 5 for supply, and zero where none was written.
int VpiDriveStrengthConstant(uint8_t written) {
  switch (written) {
    case 1:
      return vpiHiZ;
    case 2:
      return vpiWeakDrive;
    case 3:
      return vpiPullDrive;
    case 4:
      return vpiStrongDrive;
    case 5:
      return vpiSupplyDrive;
    default:
      return 0;
  }
}

// §37.16 (figure): what the declaration of `net` writes that `obj` answers:
// whether it wrote the scalared or the vectored keyword, through
// vpiExplicitScalared and vpiExplicitVectored and, a vectored net not being
// expanded into its bits, vpiExpanded; and the drive strengths of its net
// declaration assignment through vpiStrength0 and vpiStrength1.
void RecordNetDeclaration(const RtlirNet& net, VpiObject& obj) {
  obj.is_scalared = net.is_scalared;
  obj.is_vectored = net.is_vectored;
  const DataType* written = net.written_type;
  if (written == nullptr) return;
  obj.strength0 = VpiDriveStrengthConstant(written->drive_strength0);
  obj.strength1 = VpiDriveStrengthConstant(written->drive_strength1);
}

}  // namespace

void RecordNetDeclarationFacts(const RtlirDesign* design,
                               const VpiObjectMap& objects) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
            VpiObject* obj = FindObjectForFlatName(objects, key);
            if (obj != nullptr) RecordNetDeclaration(net, *obj);
          }
        }
      });
}

}  // namespace delta
