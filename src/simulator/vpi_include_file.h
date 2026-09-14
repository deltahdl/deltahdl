// Annexes K and L: the VPI include files. §K.1 has Annex K show the contents
// of vpi_user.h, and has the file be a normative include file that every
// SystemVerilog simulator shall provide. §L.1 has Annex L show the contents
// of vpi_compatibility.h, the file that holds the special macro definitions
// required to support VPI compatibility mode functionality (§36.12, and
// especially §36.12.2.1); has vpi_user.h include that file automatically; and
// therefore has user application code not include it directly. This header
// states what the annexes say of the two files; the files themselves are
// src/simulator/vpi_user.h and src/simulator/vpi_compatibility.h.
#ifndef DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_
#define DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_

#include <array>
#include <cstdint>
#include <string_view>

namespace delta {

// §K.1: the annex that shows the contents of vpi_user.h.
std::string_view VpiAnnexShowingVpiUserH();

// §K.1: the file whose contents the annex shows.
std::string_view VpiUserHFileName();

// §K.1: vpi_user.h is a normative include file, not an informative one.
bool VpiUserHIsNormative();

// §K.1: every SystemVerilog simulator shall provide vpi_user.h.
bool VpiUserHIsProvidedByEverySimulator();

// §L.1: the annex that shows the contents of vpi_compatibility.h.
std::string_view VpiAnnexShowingVpiCompatibilityH();

// §L.1: the file whose contents the annex shows.
std::string_view VpiCompatibilityHFileName();

// §L.1: what the special macro definitions of vpi_compatibility.h are
// required to support -- VPI compatibility mode functionality -- and the
// clause and the subclause that describe it, the second being the one the
// annex especially points at.
enum class VpiIncludeFileSupport : uint8_t {
  kVpiRoutineLibrary,
  kVpiCompatibilityMode,
};

VpiIncludeFileSupport VpiCompatibilityHSupports();
std::array<std::string_view, 2>
VpiCompatibilityHSubclausesDescribingItsSupport();

// §L.1: who includes vpi_compatibility.h. vpi_user.h includes it
// automatically, as Annex K shows, and user application code therefore does
// not include it directly.
enum class VpiCompatibilityHIncluder : uint8_t {
  kVpiUserH,
  kUserApplicationCode,
};

bool VpiCompatibilityHIsIncludedBy(VpiCompatibilityHIncluder includer);
bool VpiCompatibilityHIsIncludedAutomatically();

}  // namespace delta

#endif  // DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_
