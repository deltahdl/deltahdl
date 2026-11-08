#include <cstdint>
#include <string>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_nets.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

void RecordNetDeclaration(const RtlirNet& net, VpiObject& obj) {
  obj.is_scalared = net.is_scalared;
  obj.is_vectored = net.is_vectored;
  obj.implicit_decl = net.implicit_ref_loc.IsValid();
  obj.line_no = VpiNetLineNo(obj.implicit_decl, obj.line_no);
  const DataType* written = net.written_type;
  if (written == nullptr) return;
  obj.strength0 = VpiDriveStrengthConstant(written->drive_strength0);
  obj.strength1 = VpiDriveStrengthConstant(written->drive_strength1);
}

}  // namespace

void ForEachDeclaredNetObject(const RtlirDesign* design,
                              const VpiObjectMap& objects,
                              const VpiDeclaredNetVisit& visit) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
            VpiObject* obj = FindObjectForFlatName(objects, key);
            if (obj != nullptr) visit(net, *obj, prefix);
          }
        }
      });
}

void RecordNetDeclarationFacts(const RtlirDesign* design,
                               const VpiObjectMap& objects) {
  ForEachDeclaredNetObject(
      design, objects,
      [](const RtlirNet& net, VpiObject& obj, const std::string&) {
        RecordNetDeclaration(net, obj);
      });
}

}  // namespace delta
