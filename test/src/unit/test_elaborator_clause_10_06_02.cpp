#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "fixture_elaborator.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;
namespace {

TEST(ForceReleaseElaboration, VarLvalueForceReleaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  initial begin force w = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceBitSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForcePartSelectVariableLhsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  initial begin force data[3:0] = 4'hA; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceBitSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForcePartSelectUserNettypeNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [7:0] my_t;\n"
      "  my_t bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceOnMixedAssignmentVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    force x = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatWithBitSelectVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  wire w;\n"
      "  initial begin force {w, data[0]} = 2'b11; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §10.6.2 admits a constant bit-select of a vector net as a force target, and a
// constant expression per §11.2.1 is not only a literal but also a parameter.
// A parameter-indexed net bit-select is therefore a legal force LHS.
TEST(ForceReleaseElaboration, ForceParamBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 3;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[P] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A localparam is another §11.2.1 constant form, so a localparam-bounded
// part-select of a vector net is likewise a legal force LHS.
TEST(ForceReleaseElaboration, ForceLocalparamPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam HI = 7;\n"
      "  localparam LO = 4;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[HI:LO] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The concatenation form admits any of the individual legal LHS elements. A
// concatenation mixing a whole net with a constant bit-select of a vector net
// is accepted, exercising the accept path through the concatenation recursion.
TEST(ForceReleaseElaboration, ForceConcatWithNetBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force {w, bus[3]} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The prohibition covers force AND release: a release applied to a variable
// driven by both a continuous and a procedural assignment is rejected the same
// way the force position is.
TEST(ForceReleaseElaboration, ReleaseOnMixedAssignmentVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    x = 1'b1;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
