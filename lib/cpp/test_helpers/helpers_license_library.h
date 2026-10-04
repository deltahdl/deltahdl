#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_scratch_dir.h"
#include "preprocessor/protect_license.h"
#include "simulator/foreign_code.h"
#include "simulator/shared_library.h"

using namespace delta;

// The licensing library a protected model's licence names, as an IP author
// ships one beside the model (§34.5.28.2, §34.5.29.2). Its entry function
// answers 42 for a feature beginning with 'o' and 5 for any other, so a test
// chooses the answer by the feature it asks about; its exit function counts
// the releases, and a third function reads the count back.
inline constexpr std::string_view kLicenseLibrarySource =
    "static int released = 0;\n"
    "int deltahdl_license_check(const char* feature) {\n"
    "  return feature[0] == 'o' ? 42 : 5;\n"
    "}\n"
    "void deltahdl_license_release(void) { ++released; }\n"
    "int deltahdl_license_released(void) { return released; }\n";

// That library built with the C compiler into a scratch directory of its own,
// which lives as long as the test does.
struct LicenseLibrary {
  ScratchDir scratch;
  std::string file;

  LicenseLibrary() {
    std::string base = (scratch.dir / "license").string();
    std::string error = BuildCSharedLibrary(kLicenseLibrarySource, base, "cc");
    EXPECT_TRUE(error.empty()) << error;
    file = ForeignCodeSharedLibraryFileName(base);
  }

  // A licence naming this library, its entry and exit functions, `feature`,
  // and the match value `match`.
  ProtectLicense Asking(std::string_view feature, uint64_t match) const {
    ProtectLicense license;
    license.library = file;
    license.entry = "deltahdl_license_check";
    license.feature = std::string(feature);
    license.exit = "deltahdl_license_release";
    license.has_exit = true;
    license.match = match;
    license.has_match = true;
    license.stated = true;
    return license;
  }

  // How many times the exit function has been called, or -1 where the count
  // cannot be read.
  int Released() const {
    SharedLibraryLoad load = LoadSharedLibrary(file);
    if (load.handle == nullptr) return -1;
    void* count = SharedLibrarySymbol(load.handle, "deltahdl_license_released");
    if (count == nullptr) return -1;
    return reinterpret_cast<int (*)()>(count)();
  }
};
