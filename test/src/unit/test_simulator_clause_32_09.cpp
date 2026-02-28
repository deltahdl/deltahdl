// §32.9: Loading timing data from an SDF file

#include <gtest/gtest.h>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// SDF file parsing
// =============================================================================
TEST(SdfParser, ParseEmptyFile) {
  SdfFile file;
  bool ok = ParseSdf("(DELAYFILE)", file);
  EXPECT_TRUE(ok);
  EXPECT_TRUE(file.cells.empty());
}

TEST(SdfParser, ParseVersion) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (SDFVERSION "4.0")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.version, "4.0");
}

TEST(SdfParser, ParseDesign) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (DESIGN "top")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.design, "top");
}

}  // namespace
