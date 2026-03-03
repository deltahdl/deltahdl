// §6.12.1: Conversion

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Real conversions (LRM 6.12.1) ---
TEST(ParserSection6, RealToIntAssignment) {
  // Implicit conversion from real to integer (rounds, not truncates)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    r = 35.7;\n"
              "    i = r;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, IntToRealAssignment) {
  // Implicit conversion from integer to real
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  int i;\n"
              "  initial begin\n"
              "    i = 42;\n"
              "    r = i;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
