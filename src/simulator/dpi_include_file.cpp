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

bool DpiSvdpiHIsProvidedByEverySimulator() { return true; }

bool DpiSvdpiSectionMustBeProvided(DpiSvdpiSection section) {
  return section == DpiSvdpiSection::kNormative;
}

bool DpiDeprecatedSectionIsDelimitedByComments() { return true; }

std::array<std::string_view, 2> DpiWidthTypesImplementationsDefine() {
  return {"uint8_t", "uint32_t"};
}

bool DpiWidthTypeDefinitionMethodIsPrescribed() { return false; }

}  // namespace delta
