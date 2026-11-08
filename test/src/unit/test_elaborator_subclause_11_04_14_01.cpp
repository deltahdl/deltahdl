#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StreamExpressionConcatElaboration, NestedStreamingConcatAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}, a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, MultipleElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {a, b, c}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, ClassHandleWithLocalMemberRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = {>> {h}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a streaming "
                            "concatenation operand: its class has local or "
                            "protected members",
                            7, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration,
     ClassHandleWithProtectedMemberRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  protected int guarded;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = {>> {h}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a streaming "
                            "concatenation operand: its class has local or "
                            "protected members",
                            7, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration, RealOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  logic [63:0] dst;\n"
      "  initial dst = {>> {r}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'r' is not a bit-stream type and cannot be a "
                            "streaming concatenation operand",
                            4, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration, ChandleOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  chandle c;\n"
      "  logic [63:0] dst;\n"
      "  initial dst = {>> {c}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'c' is not a bit-stream type and cannot be a "
                            "streaming concatenation operand",
                            4, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration, EventOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] dst;\n"
      "  initial dst = {>> {e}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'e' is not a bit-stream type and cannot be a "
                            "streaming concatenation operand",
                            4, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration, ClassHandleWithPublicMembersAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Plain;\n"
      "  int a;\n"
      "  int b;\n"
      "endclass\n"
      "module m;\n"
      "  Plain p;\n"
      "  int v;\n"
      "  initial v = {>> {p}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, UnpackedTaggedUnionOperandReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int a; byte b; } u_t;\n"
      "  u_t u;\n"
      "  bit [31:0] r;\n"
      "  initial r = {>> {u}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'u' is not a bit-stream type and cannot be a "
                            "streaming concatenation operand",
                            5, "11.4.14.1"));
}

TEST(StreamExpressionConcatElaboration, UntaggedAndPackedTaggedUnionsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  class C; int a; endclass\n"
             "  typedef union { int a; byte b; } u_t;\n"
             "  typedef union tagged packed { int a; int b; } p_t;\n"
             "  u_t u;\n"
             "  p_t p;\n"
             "  C h;\n"
             "  bit [95:0] r;\n"
             "  initial r = {>> {u, p, h}};\n"
             "endmodule\n"));
}

}  // namespace
