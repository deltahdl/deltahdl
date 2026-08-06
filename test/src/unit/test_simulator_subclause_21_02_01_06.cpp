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

// §21.2.1.6 (C2): the rule's primary form is the *unpacked* structure data
// type, which shall print as an assignment pattern with named elements just as
// the packed form does.
TEST(AssignmentPatternFormat, UnpackedStructPrintsNamedMembers) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct { byte a; byte b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = 8'd1;\n"
      "    s.b = 8'd2;\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

// §21.2.1.6 (C7a): a member that is itself a packed structure shall print as a
// nested assignment pattern with named elements -- "each element shall be
// printed under one of these rules" -- not as a flat number.
TEST(AssignmentPatternFormat, NestedStructMemberPrintsNestedPattern) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte x; byte y; } inner_t;\n"
      "  typedef struct packed { inner_t i; byte c; } outer_t;\n"
      "  outer_t o;\n"
      "  initial begin\n"
      "    o.i.x = 8'd3;\n"
      "    o.i.y = 8'd4;\n"
      "    o.c = 8'd5;\n"
      "    $display(\"%p\", o);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{i:'{x:3, y:4}, c:5}\n");
}

// §21.2.1.6 (C5 x C7a): an unpacked array of structs is traversed until the
// singular members are reached, so each element prints as its own nested
// named pattern inside the array's pattern.
TEST(AssignmentPatternFormat, ArrayOfStructsPrintsNestedElementPatterns) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte x; byte y; } p_t;\n"
      "  p_t a [2];\n"
      "  initial begin\n"
      "    a[0] = 16'h0102;\n"
      "    a[1] = 16'h0304;\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{'{x:1, y:2}, '{x:3, y:4}}\n");
}

// §21.2.1.6 (C5 x C7b): an enum element of an unpacked array prints as its
// enumeration member name when the value is one named by the type.
TEST(AssignmentPatternFormat, ArrayOfEnumsPrintsMemberNames) {
  auto out = RunSim(
      "module t;\n"
      "  typedef enum logic [1:0] { RED, GREEN, BLUE } color_e;\n"
      "  color_e a [2];\n"
      "  initial begin\n"
      "    a[0] = GREEN;\n"
      "    a[1] = RED;\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{GREEN, RED}\n");
}

// §21.2.1.6 (C5 x C7c): string elements of an unpacked array print as quoted
// strings within the array's pattern.
TEST(AssignmentPatternFormat, ArrayOfStringsQuotesEachElement) {
  auto out = RunSim(
      "module t;\n"
      "  string a [2];\n"
      "  initial begin\n"
      "    a[0] = \"ab\";\n"
      "    a[1] = \"cd\";\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{\"ab\", \"cd\"}\n");
}

// §21.2.1.6 (C5): a queue is an unpacked array data type, so its current
// elements print as an assignment pattern in index order.
TEST(AssignmentPatternFormat, QueuePrintsElementsAsPattern) {
  auto out = RunSim(
      "module t;\n"
      "  int q [$];\n"
      "  initial begin\n"
      "    q.push_back(5);\n"
      "    q.push_back(6);\n"
      "    $display(\"%p\", q);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{5, 6}\n");
}

// §21.2.1.6 (C5/C6 edge): a queue holding no elements still yields a legal
// assignment-pattern interpretation -- the empty pattern.
TEST(AssignmentPatternFormat, EmptyQueuePrintsEmptyPattern) {
  auto out = RunSim(
      "module t;\n"
      "  int q [$];\n"
      "  initial $display(\"%p\", q);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{}\n");
}

// §21.2.1.6 (C5): a dynamic array likewise prints its current elements as an
// assignment pattern.
TEST(AssignmentPatternFormat, DynamicArrayPrintsElementsAsPattern) {
  auto out = RunSim(
      "module t;\n"
      "  int d [];\n"
      "  initial begin\n"
      "    d = new[2];\n"
      "    d[0] = 8;\n"
      "    d[1] = 9;\n"
      "    $display(\"%p\", d);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{8, 9}\n");
}

// §21.2.1.6 (C5): an associative array prints as an assignment pattern that
// includes index labels, one "key:value" item per populated element -- the
// form the clause's own example shows for an int-indexed array.
TEST(AssignmentPatternFormat, AssociativeArrayPrintsIndexLabels) {
  auto out = RunSim(
      "module t;\n"
      "  int aa [int];\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    $display(\"%p\", aa);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{10:100, 20:200}\n");
}

// §21.2.1.6 (C5): a string-indexed associative array's index labels are the
// quoted string keys.
TEST(AssignmentPatternFormat, StringKeyedAssocArrayQuotesIndexLabels) {
  auto out = RunSim(
      "module t;\n"
      "  int aa [string];\n"
      "  initial begin\n"
      "    aa[\"k1\"] = 1;\n"
      "    aa[\"k2\"] = 2;\n"
      "    $display(\"%p\", aa);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{\"k1\":1, \"k2\":2}\n");
}

// §21.2.1.6 (C7d): a null chandle value shall print the word "null"; an
// uninitialized chandle is null.
TEST(AssignmentPatternFormat, NullChandlePrintsNull) {
  auto out = RunSim(
      "module t;\n"
      "  chandle ch;\n"
      "  initial $display(\"%p\", ch);\n"
      "endmodule\n");
  EXPECT_EQ(out, "null\n");
}

// §21.2.1.6 (C7d): a null virtual interface shall print the word "null"; once
// bound to an interface instance it prints an implementation-dependent form
// instead (here the instance name), showing the "null" spelling comes from the
// handle being null rather than from the operand's type.
TEST(AssignmentPatternFormat, NullVirtualInterfacePrintsNull) {
  auto out = RunSim(
      "interface ifc; logic a; endinterface\n"
      "module t;\n"
      "  ifc i0();\n"
      "  virtual ifc v;\n"
      "  initial begin\n"
      "    $display(\"%p\", v);\n"
      "    v = i0;\n"
      "    $display(\"%p\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "null\ni0\n");
}

// §21.2.1.6 (C10 x C7e): %p on a singular real operand prints the value as it
// would unformatted -- the shortest real form, keeping the fraction rather
// than truncating to an integer.
TEST(AssignmentPatternFormat, RealOperandPrintsRealForm) {
  auto out = RunSim(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    $display(\"%p\", r);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "1.5\n");
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

// §21.2.1.6 (C2/C6) x §10.9 dependency: a struct whose value comes from an
// assignment-pattern *initializer* -- the very syntax the printed output must
// remain a legal interpretation of -- round-trips through %p as a named
// pattern. The input is built from the declaration initializer, not from
// procedural member assignments.
TEST(AssignmentPatternFormat, StructFromPatternInitializerRoundTrips) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $display(\"%p\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

// §21.2.1.6 (C5/C6) x §10.9 dependency: an unpacked array populated by an
// assignment-pattern initializer prints back as an assignment pattern of the
// same element values.
TEST(AssignmentPatternFormat, ArrayFromPatternInitializerRoundTrips) {
  auto out = RunSim(
      "module t;\n"
      "  int a [3] = '{5, 6, 7};\n"
      "  initial $display(\"%p\", a);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{5, 6, 7}\n");
}

// §21.2.1.6 (C7e edge): a member holding all high-impedance bits prints as it
// would unformatted -- the decimal status character z -- alongside a known
// member, exercising the z half of the unknown/high-impedance element forms.
TEST(AssignmentPatternFormat, StructMemberWithHighImpedanceValuePrintsZ) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = 8'bz;\n"
      "    s.b = 8'd0;\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:z, b:0}\n");
}

// §21.2.1.6 (C1/C2) in the $write position: the rule applies to the whole
// display-and-write task family, and $write renders the same pattern without
// appending a newline.
TEST(AssignmentPatternFormat, WriteTaskRendersPatternWithoutNewline) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $write(\"%p|\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}|");
}

// §21.2.1.6 (C1): Table 21-1 spells the specifier as %p or %P; the uppercase
// spelling selects the same assignment-pattern rendering.
TEST(AssignmentPatternFormat, UppercaseSpecifierRendersPattern) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $display(\"%P\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

// §21.2.1.6 (C10): a singular *expression* operand -- not just a variable
// reference -- is formatted as one element of an aggregate would be.
TEST(AssignmentPatternFormat, ExpressionOperandPrintsElementForm) {
  auto out = RunSim(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    $display(\"%p\", x + 1);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "8\n");
}

// §21.2.1.6 (C10 x C9): the shorter %0p form may likewise be applied to a
// singular expression, which is then formatted as a single element of an
// aggregate would be.
TEST(AssignmentPatternFormat, ShortFormOnSingularPrintsElementForm) {
  auto out = RunSim(
      "module t;\n"
      "  int x;\n"
      "  string s;\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    s = \"hi\";\n"
      "    $display(\"%0p %0p\", x, s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "7 \"hi\"\n");
}

}  // namespace
