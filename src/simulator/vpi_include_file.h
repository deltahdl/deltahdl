#ifndef DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_
#define DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_

#include <array>
#include <cstdint>
#include <string_view>

namespace delta {

std::string_view VpiAnnexShowingVpiUserH();

std::string_view VpiUserHFileName();

bool VpiUserHIsNormative();

bool VpiUserHIsProvidedByEverySimulator();

std::string_view VpiAnnexShowingVpiCompatibilityH();

std::string_view VpiCompatibilityHFileName();

enum class VpiIncludeFileSupport : uint8_t {
  kVpiRoutineLibrary,
  kVpiCompatibilityMode,
};

VpiIncludeFileSupport VpiCompatibilityHSupports();
std::array<std::string_view, 2>
VpiCompatibilityHSubclausesDescribingItsSupport();

enum class VpiCompatibilityHIncluder : uint8_t {
  kVpiUserH,
  kUserApplicationCode,
};

bool VpiCompatibilityHIsIncludedBy(VpiCompatibilityHIncluder includer);
bool VpiCompatibilityHIsIncludedAutomatically();

std::string_view VpiAnnexShowingSvVpiUserH();

std::string_view SvVpiUserHFileName();

bool SvVpiUserHIsNormative();

bool SvVpiUserHIsProvidedByEverySimulator();

}  // namespace delta

#endif
