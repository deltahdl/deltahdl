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

// Positive boundary of the same rule for the inout half: a bidirectional
// switch whose terminals are 1-bit nets satisfies the direct-1-bit-net
// requirement and elaborates without error.
TEST(PortConnectionElab, BidirectionalSwitchOneBitInoutElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire a, b;\n"
      "  tran t(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §4.9.6 admits a 1-bit *structural net expression* (see 23.3.3), not only a
// scalar net, as a primitive output/inout terminal. A single-bit select of a
// vector net is one bit wide and satisfies the rule.
TEST(PortConnectionElab, PrimitiveOutputOneBitSelectElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[0], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form of the same rule for a structural net expression: a ranged
// part-select wider than one bit driving a primitive output terminal violates
// the 1-bit requirement.
TEST(PortConnectionElab, PrimitiveOutputMultiBitPartSelectRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[3:1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The part-select bounds are a constant expression (§11.2.1); a localparam is
// one of its constant forms. The 1-bit rule must measure the select width after
// resolving the localparam bounds, so a 3-bit localparam-bounded part-select is
// rejected just like a literal-bounded one.
TEST(PortConnectionElab, PrimitiveOutputPartSelectWidthFromLocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam int HI = 3;\n"
      "  localparam int LO = 1;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[HI:LO], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// An indexed part-select `[base +: width]` is another structural net expression
// form (§23.3.3). With a width of one it names a single bit and satisfies the
// primitive-terminal 1-bit rule.
TEST(PortConnectionElab,
     PrimitiveOutputIndexedPartSelectOneBitElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[2 +: 1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form: an indexed part-select spanning more than one bit driving a
// primitive output terminal violates the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputIndexedPartSelectMultiBitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[2 +: 3], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A concatenation of net selects is a structural net expression (§23.3.3). A
// concatenation whose parts total one bit satisfies the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputConcatOneBitElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b({bus[0]}, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form: a concatenation whose parts total more than one bit driving a
// primitive output terminal violates the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputConcatMultiBitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b({bus[1:0]}, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The 1-bit rule covers the *inout* terminal position as well as output. A
// bidirectional switch terminal driven by a multi-bit structural net expression
// (a ranged part-select) is rejected just like a multi-bit output terminal.
TEST(PortConnectionElab, PrimitiveInoutMultiBitPartSelectRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  wire other;\n"
      "  tran t(bus[3:1], other);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A module parameter is another constant form (§11.2.1) admissible as a
// part-select bound, taking the overridable-parameter code path rather than the
// localparam one. A 3-bit parameter-bounded part-select is still rejected.
TEST(PortConnectionElab, PrimitiveOutputPartSelectWidthFromParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int HI = 3) ();\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[HI:1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
