#include <gtest/gtest.h>

#include <initializer_list>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument is a hierarchical reference",
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument is a hierarchical reference",
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument selects an element of a dynamic object",
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$typename cannot serve as an elaboration-time constant "
                    "when its argument selects an element of a dynamic object",
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

// §20.6.1: a name that declares nothing, an operation on literals alone and a
// call of another function are not folded as a type name; nor, with no module
// being elaborated, an anonymous aggregate, which is named after the module
// (step c), a range bounded by a name, nor an operand naming no variable.
TEST(TypenameConstEval, OtherArgumentsAreNotFolded) {
  EvalFixture f;
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename(w)", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(1 + 2)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$clog2(int)", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename()", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(struct packed { bit a; })", f))
          .has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(bit [W:0])", f)).has_value());
  EXPECT_FALSE(ConstEvalString(ParseExprFrom("$typename(~w)", f)).has_value());
  EXPECT_FALSE(
      ConstEvalString(ParseExprFrom("$typename(w[0])", f)).has_value());
}

// The characters the string parameter `name` of module `top` folded to.
std::string_view FoldedChars(RtlirDesign* design, std::string_view name) {
  const RtlirParamDecl* pd = FindParam(design, "top", name);
  return pd == nullptr ? "<no parameter>" : pd->resolved_string;
}

// §20.6.1, step b: a data_type no expression spells reaches the fold as a type
// node, and a signing other than its type's default stays in the name; an
// anonymous aggregate is named by the system after the module (step c), an
// enumeration with each constant's value (step e) (#8067).
TEST(TypenameConstEval, ATypeNodeFoldsToItsName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam string A = $typename(int unsigned);\n"
      "  localparam string B = $typename(bit signed [3:0]);\n"
      "  localparam string C = $typename(struct packed { bit a; byte b; });\n"
      "  localparam string D = $typename(enum bit [1:0] { X, Y = 3 });\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "int unsigned");
  EXPECT_EQ(FoldedChars(design, "B"), "bit signed[3:0]");
  EXPECT_EQ(FoldedChars(design, "C"), "struct packed{bit a;byte b;}top.s$type");
  EXPECT_EQ(FoldedChars(design, "D"), "enum{X=2'd0,Y=2'd3}top.e$type");
}

// §20.6.1, step g: a keyword type with a packed range, which the parser reads
// as a select over the keyword, folds to the keyword and its bounds as
// unsized decimals, a parameter in a bound standing for its value (#8068).
TEST(TypenameConstEval, ARangedKeywordFoldsWithItsBounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam int W = 8;\n"
      "  localparam string A = $typename(bit [3:0]);\n"
      "  localparam string B = $typename(logic [W-1:0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "bit[3:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "logic[7:0]");
}

// §20.6.1, step a: a typedef name folds to the type it names, and one naming
// a structure keeps the name, behind the module declaring it (step f)
// (#8069).
TEST(TypenameConstEval, ATypedefNameFoldsToTheTypeItNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit node;\n"
      "  typedef struct { bit A; bit B; } AB_t;\n"
      "  localparam string A = $typename(node);\n"
      "  localparam string B = $typename(AB_t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "bit");
  EXPECT_EQ(FoldedChars(design, "B"), "struct{bit A;bit B;}top.AB_t");
}

// §20.6.1: an expression folds to its self-determined type: a variable to the
// type it was declared with, an unpacked array's dimensions after the "$"
// standing for its name (step d), an element to the element type with the
// dimensions after the first, a bit-select, an indexed part-select and a sum
// to the vectors §11.6.1 and §11.8.1 make them, and an operation with a real
// operand to `real` (#8070).
TEST(TypenameConstEval, AnExpressionFoldsToItsSelfDeterminedType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct { bit A; bit B; } AB_t;\n"
      "  logic [7:0] v;\n"
      "  bit [3:0] w;\n"
      "  AB_t AB [10];\n"
      "  int m [2][3];\n"
      "  typedef enum { X, Y } e_t;\n"
      "  localparam string A = $typename(v);\n"
      "  localparam string B = $typename(AB);\n"
      "  localparam string C = $typename(AB[0]);\n"
      "  localparam string D = $typename(v[0]);\n"
      "  localparam string E = $typename(v + w);\n"
      "  localparam string F = $typename(w + 1.5);\n"
      "  localparam string G = $typename(m[0]);\n"
      "  localparam string H = $typename(v[5-:2]);\n"
      "  localparam string I = $typename(X[0]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "struct{bit A;bit B;}top.AB_t$[0:9]");
  EXPECT_EQ(FoldedChars(design, "C"), "struct{bit A;bit B;}top.AB_t");
  EXPECT_EQ(FoldedChars(design, "D"), "logic");
  EXPECT_EQ(FoldedChars(design, "E"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "F"), "real");
  EXPECT_EQ(FoldedChars(design, "G"), "int$[0:2]");
  EXPECT_EQ(FoldedChars(design, "H"), "logic[1:0]");
  EXPECT_EQ(FoldedChars(design, "I"), "bit");
}

// §20.6.1 with §7.4.1 and §11.5.1: the fold sizes a select of a packed array
// by the elements of its outermost dimension, `p[1]` one 8-bit element and
// `p[2:1]` two, as the run does.
TEST(TypenameConstEval, ASelectOfAPackedArrayFoldsToItsElementsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0][7:0] p;\n"
      "  bit [3:0] n;\n"
      "  localparam string A = $typename(p[1]);\n"
      "  localparam string B = $typename(p[2:1]);\n"
      "  localparam string C = $typename(p[1] + n);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FoldedChars(design, "A"), "logic[7:0]");
  EXPECT_EQ(FoldedChars(design, "B"), "logic[15:0]");
  EXPECT_EQ(FoldedChars(design, "C"), "logic[7:0]");
}

// What the fold cannot resolve from the module's declarations it leaves to
// the run rather than fold to a wrong name: a class type and a package's
// type, which the module's typedef table does not hold, an enumeration
// constant, whose storage records no declared type, an operand that is real,
// a string or an unpacked array, here a slice of one, a select of an element
// of a multidimensional array, and a type reference to an expression.
TEST(TypenameConstEval, WhatTheModuleCannotResolveIsLeftUnfolded) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit w_t;\n"
      "endpackage\n"
      "module top;\n"
      "  class K;\n"
      "  endclass\n"
      "  typedef enum { X, Y } e_t;\n"
      "  K h;\n"
      "  p::w_t pw;\n"
      "  real r;\n"
      "  string s;\n"
      "  int q [2];\n"
      "  int m [2][3];\n"
      "  localparam string A = $typename(h);\n"
      "  localparam string B = $typename(pw);\n"
      "  localparam string C = $typename(X);\n"
      "  localparam string D = $typename(-r);\n"
      "  localparam string E = $typename({s});\n"
      "  localparam string F = $typename(q[1:0]);\n"
      "  localparam string G = $typename(m[1][2]);\n"
      "  localparam string H = $typename(type(r));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  for (std::string_view name : {"A", "B", "C", "D", "E", "F", "G", "H"}) {
    EXPECT_EQ(FoldedChars(design, name), "") << name;
  }
}

}  // namespace
