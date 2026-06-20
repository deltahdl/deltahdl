#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// §21.2.1.6 Assignment pattern format. The %p (and the shorter %0p) format
// specifier prints aggregate operands -- unpacked structures, arrays, and
// unions -- as an assignment pattern, and prints a singular operand as a single
// element of one. These tests drive the whole simulator: $display passes the
// run-time context into the formatter, which reads the struct/union/array/enum
// type information the lowerer recorded, and the displayed text is captured end
// to end.

namespace {

std::string RunSim(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  return testing::internal::GetCapturedStdout();
}

// §21.2.1.6 (C1/C2/C7a/C6): a struct prints as an assignment pattern with one
// "name:value" entry per member, in declaration order. The leading '{ and the
// member/comma punctuation form a legal interpretation of the assignment
// pattern syntax.
TEST(AssignmentPatternFormat, StructPrintsNamedMembers) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = 8'd1;\n"
      "    s.b = 8'd2;\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

// §21.2.1.6 (C7e edge): a signed integer member prints with its sign, since an
// element prints as it would unformatted. A byte member holding -5 shows "-5",
// not the unsigned bit pattern.
TEST(AssignmentPatternFormat, StructMemberWithNegativeValuePrintsSigned) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = -5;\n"
      "    s.b = 8'd2;\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:-5, b:2}\n");
}

// §21.2.1.6 (C7e edge): a member that holds unknown bits prints as it would
// unformatted -- the decimal status character x. An unassigned 4-state struct
// keeps every member at x, exercising the field extraction's preservation of
// unknown bits.
TEST(AssignmentPatternFormat, StructMemberWithUnknownValuePrintsX) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial $display(\"%p\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:x, b:x}\n");
}

// §21.2.1.6 (C5/C7e edge): array elements also print as they would unformatted,
// so a signed element with a negative value shows its sign within the pattern.
TEST(AssignmentPatternFormat, ArrayOfSignedElementsPrintsNegative) {
  auto out = RunSim(
      "module t;\n"
      "  int a [3];\n"
      "  initial begin\n"
      "    a[0] = -5;\n"
      "    a[1] = 20;\n"
      "    a[2] = 30;\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{-5, 20, 30}\n");
}

// §21.2.1.6 (C3): a (non-tagged) union prints only its first declared member.
TEST(AssignmentPatternFormat, UnionPrintsOnlyFirstMember) {
  auto out = RunSim(
      "module t;\n"
      "  typedef union packed { byte a; byte b; } u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    u.a = 8'd5;\n"
      "    $display(\"%p\", u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:5}\n");
}

// §21.2.1.6 (C4): a tagged union prints "tag:value" for the currently valid
// member.
TEST(AssignmentPatternFormat, TaggedUnionPrintsTagAndValue) {
  auto out = RunSim(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  initial begin\n"
      "    u = tagged Valid 42;\n"
      "    $display(\"%p\", u);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{Valid:42}\n");
}

// §21.2.1.6 (C7b): an enumerated value prints as the matching member name when
// the value is one named by the type.
TEST(AssignmentPatternFormat, EnumPrintsMemberName) {
  auto out = RunSim(
      "module t;\n"
      "  typedef enum logic [1:0] { RED, GREEN, BLUE } color_e;\n"
      "  color_e c;\n"
      "  initial begin\n"
      "    c = BLUE;\n"
      "    $display(\"%p\", c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "BLUE\n");
}

// §21.2.1.6 (C7b): when the value is not one named by the enumeration, it
// prints according to the base type instead of an enumeration name. An
// uninitialized 4-state enum holds x, which names no member, so the base-type
// (decimal) form is used.
TEST(AssignmentPatternFormat, EnumWithUnnamedValueFallsBackToBaseType) {
  auto out = RunSim(
      "module t;\n"
      "  typedef enum logic [1:0] { RED, GREEN, BLUE } color_e;\n"
      "  color_e c;\n"
      "  initial $display(\"%p\", c);\n"
      "endmodule\n");
  EXPECT_EQ(out, "x\n");
}

// §21.2.1.6 (C7b): the base-type fallback also applies to a *known* value that
// simply names no member of the enumeration -- the distinct path where the
// member-match search runs to completion without a hit (as opposed to an
// unknown value, which skips the search). Casting day_e's SUN (6) into the
// three-member color_e leaves a known 6 that matches no color name, so the
// value prints in the base type's decimal form rather than as an enumeration
// name.
TEST(AssignmentPatternFormat, EnumKnownValueNotNamedFallsBackToBaseType) {
  auto out = RunSim(
      "module t;\n"
      "  typedef enum { RED, GREEN, BLUE } color_e;\n"
      "  typedef enum { MON, TUE, WED, THU, FRI, SAT, SUN } day_e;\n"
      "  color_e c;\n"
      "  initial begin\n"
      "    c = color_e'(SUN);\n"
      "    $display(\"%p\", c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "6\n");
}

// §21.2.1.6 (C7d): a null class handle prints the word "null". An uninitialized
// handle is null.
TEST(AssignmentPatternFormat, NullClassHandlePrintsNull) {
  auto out = RunSim(
      "class C; endclass\n"
      "module t;\n"
      "  C h;\n"
      "  initial $display(\"%p\", h);\n"
      "endmodule\n");
  EXPECT_EQ(out, "null\n");
}

// §21.2.1.6 (C7c/C10): %p on a singular string operand prints the string value
// enclosed in quotes, formatted as it would be as an element of an aggregate.
TEST(AssignmentPatternFormat, StringOperandIsQuoted) {
  auto out = RunSim(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hi\";\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "\"hi\"\n");
}

// §21.2.1.6 (C10/C7e): %p on a singular non-string operand formats it as a
// single aggregate element -- i.e. as it would print unformatted (decimal).
TEST(AssignmentPatternFormat, SingularValuePrintsUnformatted) {
  auto out = RunSim(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    $display(\"%p\", x);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "7\n");
}

// §21.2.1.6 (C9): %0p is the shorter form of the assignment-pattern specifier;
// it likewise yields a legal assignment-pattern rendering of the aggregate.
TEST(AssignmentPatternFormat, ShortFormSpecifierRendersPattern) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = 8'd1;\n"
      "    s.b = 8'd2;\n"
      "    $display(\"%0p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

}  // namespace
