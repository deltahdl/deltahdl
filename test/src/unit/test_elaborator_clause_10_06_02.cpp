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

// §10.6.2: force LHS shall not be a bit-select of a variable.
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

// §10.6.2: force LHS shall not be a part-select of a variable.
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

// §10.6.2: force LHS shall not be a bit-select of a net with a user-defined
// nettype.
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

// §10.6.2: force LHS shall not be a part-select of a net with a user-defined
// nettype.
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

// §10.6.2: a force statement shall not be applied to a variable that is
// being assigned by a mixture of continuous and procedural assignments.
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

// §10.6.2: force in a concatenation, where one operand is a bit-select of
// a variable, is illegal.
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

}  // namespace
