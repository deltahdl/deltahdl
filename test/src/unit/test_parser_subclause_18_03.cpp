#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintFourState, TripleEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x === 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 3,
      "18.3"));
}

TEST(ConstraintFourState, TripleNotEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x !== 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 3,
      "18.3"));
}

TEST(ConstraintFourState, FourStateLiteralRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 4'b01xz; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state value is not allowed in a constraint", 3, "18.3"));
}

TEST(ConstraintFourState, QuestionMarkDigitRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  constraint c { x == 4'b10??; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state value is not allowed in a constraint", 3, "18.3"));
}

TEST(ConstraintFourState, TwoStateConstraintAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 5; x inside {1, 2, 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

constexpr char kValueMessage[] = "4-state value is not allowed in a constraint";
constexpr char kOperatorMessage[] =
    "4-state equality operator is not allowed in a constraint";

TEST(ConstraintFourState, UnbasedUnsizedXAndZAreReported) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  constraint c { x == 'x;\n"
      "                 y != 'z; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 3, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 4, "18.3"));
}

TEST(ConstraintFourState, UnbasedUnsizedOneAndZeroAreAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  constraint c { x == '1; y != '0; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState, AFourStateDistItemOrInsideMemberIsReported) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  constraint c { x dist { 4'b1x00 := 1, 4'd2 := 1 };\n"
      "                 y inside { 4'd1, 4'bz000 }; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 3, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 4, "18.3"));
}

TEST(ConstraintFourState, TwoStateDistItemsAndInsideMembersAreAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  constraint c { x dist { 4'b1000 := 1, 4'd2 := 1 };\n"
      "                 y inside { 4'd1, 4'b1000 }; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState, NestedConstraintFormsAreReported) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  rand bit [3:0] a [2];\n"
      "  constraint c {\n"
      "    if (y > 1) x === 4'd1;\n"
      "    (y == 2) -> x == 4'b000x;\n"
      "    foreach (a[i]) a[i] !== 4'd3;\n"
      "    soft x == 4'bz;\n"
      "  }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kOperatorMessage, 5, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 6, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kOperatorMessage, 7, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 8, "18.3"));
}

TEST(ConstraintFourState, NestedTwoStateConstraintFormsAreAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "  rand bit [3:0] a [2];\n"
      "  constraint c {\n"
      "    if (y > 1) x == 4'd1;\n"
      "    (y == 2) -> x == 4'b0001;\n"
      "    foreach (a[i]) a[i] != 4'd3;\n"
      "    soft x == 4'b1;\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState, AnOutOfBlockConstraintIsChecked) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  extern constraint ce;\n"
      "endclass\n"
      "constraint C::ce {\n"
      "  x !== 4'd2;\n"
      "}\n");
  EXPECT_TRUE(ReportedError(r.diags, kOperatorMessage, 6, "18.3"));
}

TEST(ConstraintFourState, AnOutOfBlockTwoStateConstraintIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  extern constraint ce;\n"
      "endclass\n"
      "constraint C::ce {\n"
      "  x != 4'd2;\n"
      "}\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState, AFourStateLiteralInRandomizeWithIsReported) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial void'(obj.randomize() with { x == 4'bx; });\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 6, "18.3"));
}

TEST(ConstraintFourState, ATwoStateLiteralInRandomizeWithIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial void'(obj.randomize() with { x == 4'b1; });\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState, ScopeRandomizeWithIsChecked) {
  auto r = Parse(
      "module m;\n"
      "  bit [3:0] a;\n"
      "  initial begin\n"
      "    void'(std::randomize(a) with { a === 4'd1; });\n"
      "    void'(std::randomize(a) with { a == 4'b10z1; });\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kOperatorMessage, 4, "18.3"));
  EXPECT_TRUE(ReportedError(r.diags, kValueMessage, 5, "18.3"));
}

TEST(ConstraintFourState, ScopeRandomizeWithTwoStateFormsIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  bit [3:0] a;\n"
      "  initial begin\n"
      "    void'(std::randomize(a) with { a == 4'd1; });\n"
      "    void'(std::randomize(a) with { a == 4'b1001; });\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintFourState,
     XAndZLettersInAStringOrOutsideAConstraintAreAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  string s;\n"
      "  constraint c { s == \"xz\" -> x == 4'd1; }\n"
      "  function bit f(logic [3:0] v);\n"
      "    return v === 4'bx;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
