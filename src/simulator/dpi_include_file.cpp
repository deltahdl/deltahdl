#include "simulator/dpi_include_file.h"

#include <array>
#include <string_view>

namespace delta {

std::string_view DpiAnnexListingSvdpiH() { return "Annex I"; }

std::array<DpiSvdpiContent, 3> DpiSvdpiContents() {
  return {DpiSvdpiContent::kConstantDefinitions,
          DpiSvdpiContent::kStructureDefinitions,
          DpiSvdpiContent::kRoutineDeclarations};
}

bool DpiSvdpiHContains(DpiSvdpiContent /*content*/) { return true; }

}  // namespace delta
