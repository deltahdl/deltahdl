#include "simulator/vpi_include_file.h"

#include <string_view>

namespace delta {

std::string_view VpiAnnexShowingVpiUserH() { return "Annex K"; }

std::string_view VpiUserHFileName() { return "vpi_user.h"; }

bool VpiUserHIsNormative() { return true; }

bool VpiUserHIsProvidedByEverySimulator() { return true; }

}  // namespace delta
