#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "elaboration-time-constant context shall not contain hierarchical "
      "references",
      6, "20.6.1"));
}

// The elaboration-time-constant restriction applies in a localparam
// initializer just as in a parameter one: a hierarchical reference argument is
// rejected. Covers the localparam declaration form of the constant context.
TEST(SubroutineCallExprElaboration,
     TypenameRejectsHierarchicalRefInLocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  logic x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  localparam integer T = $typename(s.x);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "elaboration-time-constant context shall not contain hierarchical "
      "references",
      6, "20.6.1"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "elaboration-time-constant context shall not reference elements of "
      "dynamic objects",
      3, "20.6.1"));
}

TEST(SubroutineCallExprElaboration, TypenameRejectsAssocArrayElement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[string];\n"
      "  parameter integer T = $typename(a[\"k\"]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "elaboration-time-constant context shall not reference elements of "
      "dynamic objects",
      3, "20.6.1"));
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

// §20.6.1: $typename of a built-in data type folds in a constant expression to
// the type's keyword, whatever the type.
TEST(TypenameConstEval, ABuiltinTypeFoldsToItsKeyword) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(int)", f)), "int");
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(real)", f)), "real");
  EXPECT_EQ(ConstEvalString(ParseExprFrom("$typename(string)", f)), "string");
}

// §20.6.1: a name that is not a built-in type, an expression and a call of
// another function are not folded as a type name.
TEST(TypenameConstEval, OtherArgumentsAreNotFolded) {
  EvalFixture f;
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename(w)", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(1 + 2)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$clog2(int)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename()", f)).has_value());
}

}  // namespace
