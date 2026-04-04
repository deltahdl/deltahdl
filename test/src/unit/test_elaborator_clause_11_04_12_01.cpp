#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ReplicationElaboration, ReplicationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  assign a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] x;\n"
      "  initial a = {4{x}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ConstantReplicationInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [31:0] P = {4{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnLhsOfBlockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnLhsOfNonblockingAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  initial {4{a}} <= 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnLhsOfContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  assign {4{a}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationInsideLhsConcat) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial {b, {2{a}}} = 8'hFF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnOutputPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(output [7:0] o);\n"
      "  assign o = 8'hAA;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.o({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnInoutPort) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout [7:0] io);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.io({4{a}}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ReplicationOnInputPortOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i);\n"
      "endmodule\n"
      "module m;\n"
      "  logic [1:0] a;\n"
      "  child u(.i({4{a}}));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, XMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bx{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ZMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {1'bz{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ZeroReplicationStandaloneRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] result;\n"
      "  initial result = {0{a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ReplicationElaboration, ZeroReplicationInsideConcatOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial result = {a, {0{b}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ReplicationElaboration, NegativeMultiplierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {-1{1'b0}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
