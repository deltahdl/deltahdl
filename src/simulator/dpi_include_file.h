#ifndef DELTA_SIMULATOR_DPI_INCLUDE_FILE_H_
#define DELTA_SIMULATOR_DPI_INCLUDE_FILE_H_

#include <array>
#include <cstdint>
#include <string_view>

namespace delta {

enum class DpiSvdpiContent : uint8_t {
  kConstantDefinitions,
  kStructureDefinitions,
  kRoutineDeclarations,
};

std::string_view DpiAnnexListingSvdpiH();

std::array<DpiSvdpiContent, 3> DpiSvdpiContents();

bool DpiSvdpiHContains(DpiSvdpiContent content);

bool DpiSvdpiHIsProvidedByEverySimulator();

enum class DpiSvdpiSection : uint8_t { kNormative, kDeprecated };

bool DpiSvdpiSectionMustBeProvided(DpiSvdpiSection section);
bool DpiDeprecatedSectionIsDelimitedByComments();
std::array<std::string_view, 2> DpiWidthTypesImplementationsDefine();
bool DpiWidthTypeDefinitionMethodIsPrescribed();

}  // namespace delta

#endif
