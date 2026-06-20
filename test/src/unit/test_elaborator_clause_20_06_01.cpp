#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, TypenameRejectsHierarchicalRef) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  logic x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  parameter integer T = $typename(s.x);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsLocalReference) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  parameter integer T = $typename(x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameWithoutArgsInParamInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer T = $typename();\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
}

TEST(SubroutineCallExprElaboration, TypenameRejectsDynamicArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  parameter integer T = $typename(d[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameRejectsAssocArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[string];\n"
      "  parameter integer T = $typename(a[\"k\"]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsStaticArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int s[2];\n"
      "  parameter integer T = $typename(s[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TypenameAcceptsScalarBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  parameter integer T = $typename(v[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
