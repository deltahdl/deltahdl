#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §4.9.6: The "shall" requirement that primitive output and inout terminals
// be 1-bit nets is enforced by `ValidatePrimitiveOutputTerminalWidths` in
// the gate-instance elaborator path. A `buf` whose output is declared as a
// multi-bit wire violates the rule, so the elaborator must surface a
// diagnostic. Without the validator the cont-assign would silently elaborate
// at the LHS's wider width.
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

// §4.9.6 (companion): a single-bit `wire` output is the expected shape, so
// the validator must not raise a false positive on the conformant case. This
// pins the inverse direction of the rule so a future overzealous check gets
// caught.
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

// §4.9.6: Bidirectional switches are listed alongside output terminals as
// targets of the 1-bit-net rule. A `tran` whose two inout terminals are
// declared as multi-bit wires must be diagnosed by the same validator.
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

}  // namespace
