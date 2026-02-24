// Annex L.2: Source code

#include <gtest/gtest.h>
#include "vpi/vpi_compatibility.h"

namespace {

TEST(VpiCompatL2, VersionMacroAvailable) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

}  // namespace
