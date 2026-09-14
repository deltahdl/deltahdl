#include "simulator/vpi_include_file.h"

#include <array>
#include <string_view>

namespace delta {

std::string_view VpiAnnexShowingVpiUserH() { return "Annex K"; }

std::string_view VpiUserHFileName() { return "vpi_user.h"; }

bool VpiUserHIsNormative() { return true; }

bool VpiUserHIsProvidedByEverySimulator() { return true; }

std::string_view VpiAnnexShowingVpiCompatibilityH() { return "Annex L"; }

std::string_view VpiCompatibilityHFileName() { return "vpi_compatibility.h"; }

VpiIncludeFileSupport VpiCompatibilityHSupports() {
  return VpiIncludeFileSupport::kVpiCompatibilityMode;
}

std::array<std::string_view, 2>
VpiCompatibilityHSubclausesDescribingItsSupport() {
  return {"36.12", "36.12.2.1"};
}

bool VpiCompatibilityHIsIncludedBy(VpiCompatibilityHIncluder includer) {
  return includer == VpiCompatibilityHIncluder::kVpiUserH;
}

bool VpiCompatibilityHIsIncludedAutomatically() { return true; }

std::string_view VpiAnnexShowingSvVpiUserH() { return "Annex M"; }

std::string_view SvVpiUserHFileName() { return "sv_vpi_user.h"; }

bool SvVpiUserHIsNormative() { return true; }

bool SvVpiUserHIsProvidedByEverySimulator() { return true; }

}  // namespace delta
