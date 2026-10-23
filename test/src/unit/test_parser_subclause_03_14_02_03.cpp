#include <gtest/gtest.h>

#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, CUTimeunitOnlyByKeyword) {
  auto r = PreprocessAndParse(
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_FALSE(r.cu->has_cu_timeunit);
  EXPECT_FALSE(r.cu->has_cu_timeprecision);
}

}  // namespace
