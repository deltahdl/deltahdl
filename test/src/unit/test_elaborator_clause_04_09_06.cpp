#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PortConnectionElab, PrimitiveOutputMustBeOneBitNet) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] out;\n"
      "  logic in_sig;\n"
      "  buf b(out, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionElab, PrimitiveOneBitOutputElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  logic in_sig;\n"
      "  buf b(out, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortConnectionElab, BidirectionalSwitchInoutMustBeOneBitNets) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [3:0] a, b;\n"
      "  tran t(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
