#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

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

// §21.2.1.6 (C5 x C7c): the string elements of a queue, of a queue a locator
// filled, of a dynamic array and of an associative array print quoted, as those
// of a fixed-size array do. The elements themselves carry no string mark, so
// read as numbers they printed the codes of their characters.
TEST(AssignmentPatternFormat, VariableSizeArraysOfStringsQuoteEachElement) {
  auto out = RunSim(
      "module t;\n"
      "  string a[$] = '{\"b\", \"c\"};\n"
      "  string o[$];\n"
      "  string s[2] = '{\"b\", \"c\"};\n"
      "  string d[] = '{\"x\", \"yz\"};\n"
      "  string aa[int];\n"
      "  initial begin\n"
      "    o = s.find with (1);\n"
      "    aa[1] = \"p\";\n"
      "    $display(\"%p %p %p %p\", a, o, d, aa);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out,
            "'{\"b\", \"c\"} '{\"b\", \"c\"} '{\"x\", \"yz\"} '{1:\"p\"}\n");
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

// §21.2.1.6 (C1/C2) in an instantiated module: the struct is declared in M,
// which top instantiates as `m`, so its layout stands under "m.s" (§23.9) and
// the operand's bare name is resolved through the instance. Looked up bare,
// no layout was found and the operand fell to the singular form, printing
// the whole 16-bit value as 258; the named pattern prints each member.
TEST(AssignmentPatternFormat, ChildInstanceStructPrintsNamedMembers) {
  auto out = RunSim(
      "module M;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.a = 8'd1;\n"
      "    s.b = 8'd2;\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

// §21.2.1.6 (C4) in an instantiated module: the valid member of a tagged
// union prints as its own type, an int here, so -7 keeps its sign. With the
// layout looked up by the bare name inside instance `m`, the member's type
// and width were not found and the value was sliced at the union's width as
// an unsigned quantity, printing '{Valid:4294967289}.
TEST(AssignmentPatternFormat,
     ChildInstanceTaggedUnionPrintsValidMemberAsItsType) {
  auto out = RunSim(
      "module M;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  initial begin\n"
      "    u = tagged Valid (-7);\n"
      "    $display(\"%p\", u);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{Valid:-7}\n");
}

// §21.2.1.6 (C5 x C7a) in an instantiated module: a queue of structs is
// traversed to its singular members, so each element prints as a nested
// named pattern. The queue is found through the instance, but its element
// layout was looked up by the bare name and missed, so each element printed
// as a number: '{258, 772}.
TEST(AssignmentPatternFormat, ChildInstanceQueueOfStructsPrintsNestedPatterns) {
  auto out = RunSim(
      "module M;\n"
      "  typedef struct packed { byte x; byte y; } p_t;\n"
      "  p_t q [$];\n"
      "  initial begin\n"
      "    q.push_back(16'h0102);\n"
      "    q.push_back(16'h0304);\n"
      "    $display(\"%p\", q);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{'{x:1, y:2}, '{x:3, y:4}}\n");
}

// §21.2.1.6 (C5 x C7a) in an instantiated module: a fixed-size unpacked
// array of structs prints each element as a nested named pattern. The array
// is declared in M and stored under "m.a" (§23.9), and the formatter asked
// for its shape by the bare name and found none, so the operand fell to the
// struct form and printed the never-written carrier as one pattern,
// '{x:0, y:0}; the two elements print in index order.
TEST(AssignmentPatternFormat, ChildInstanceArrayOfStructsPrintsNestedPatterns) {
  auto out = RunSim(
      "module M;\n"
      "  typedef struct packed { byte x; byte y; } p_t;\n"
      "  p_t a [2];\n"
      "  initial begin\n"
      "    a[0] = 16'h0102;\n"
      "    a[1] = 16'h0304;\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{'{x:1, y:2}, '{x:3, y:4}}\n");
}

// §21.2.1.6 (C7a) with §7.4 and §7.8: an element selected from an array of
// structs is a struct and prints as a named pattern, as the whole array prints
// it -- an associative array's `va[10]` written from a struct variable, a
// fixed-size array's `arr[1]`, a queue's `q[0]`, in the top module and in an
// instance -- and an element of an array of enums prints as its member name.
// Each printed the element's bits as one number, 21474836486 for '{a:5, b:6}.
TEST(AssignmentPatternFormat, ElementOfAnArrayOfStructsPrintsAsAPattern) {
  auto out = RunSim(
      "module M;\n"
      "  typedef struct { int a; int b; } u_t;\n"
      "  u_t va[int];\n"
      "  initial begin\n"
      "    va[5] = '{7, 8};\n"
      "    $display(\"%p\", va[5]);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  typedef enum { ON, OFF } sw_e;\n"
      "  typedef struct { int a; int b; } ab_t;\n"
      "  ab_t vb[int];\n"
      "  ab_t arr[2] = '{'{1, 2}, '{3, 4}};\n"
      "  ab_t q[$] = '{'{9, 10}};\n"
      "  sw_e ea[2];\n"
      "  ab_t p;\n"
      "  M m();\n"
      "  initial begin\n"
      "    p = '{5, 6};\n"
      "    vb[10] = p;\n"
      "    ea[1] = OFF;\n"
      "    #1 $display(\"%p %p %p %p\", vb[10], arr[1], q[0], ea[1]);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:7, b:8}\n'{a:5, b:6} '{a:3, b:4} '{a:9, b:10} OFF\n");
}

// §21.2.1.6 (C2 with C7b): a struct member of an enum type prints as the name
// of its value, as the enum prints on its own -- in a struct variable, in each
// element of an array of such structs, and for an enum declared in a package.
// Each printed the value's number, '{sw:1, n:7} for OFF.
TEST(AssignmentPatternFormat, EnumMemberOfAStructPrintsItsName) {
  auto out = RunSim(
      "package pk; typedef enum { RED, GREEN } col_e; endpackage\n"
      "module top;\n"
      "  typedef enum { ON, OFF } switch_e;\n"
      "  typedef struct { switch_e sw; pk::col_e c; int n; } s_t;\n"
      "  s_t s = '{OFF, pk::GREEN, 7};\n"
      "  s_t arr[2];\n"
      "  initial begin\n"
      "    arr[1] = s;\n"
      "    $display(\"%p\", s);\n"
      "    $display(\"%p\", arr);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out,
            "'{sw:OFF, c:GREEN, n:7}\n"
            "'{'{sw:ON, c:RED, n:0}, '{sw:OFF, c:GREEN, n:7}}\n");
}

// §21.2.1.6 (C5 with §10.9.1): a multidimensional unpacked array prints as a
// pattern of the patterns of its subarrays, one level of braces per dimension,
// down to its elements -- integers, structs and enum names alike.
TEST(AssignmentPatternFormat,
     MultidimensionalArrayNestsOnePatternPerDimension) {
  auto out = RunSim(
      "module top;\n"
      "  typedef enum { ON, OFF } switch_e;\n"
      "  typedef struct { int a; int b; } ab_t;\n"
      "  int id[2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  logic [3:0] m3[2][2][2];\n"
      "  ab_t sa[2][2];\n"
      "  switch_e ed[2][2] = '{'{ON, OFF}, '{OFF, ON}};\n"
      "  initial begin\n"
      "    foreach (m3[i, j, k]) m3[i][j][k] = i * 4 + j * 2 + k;\n"
      "    sa[1][0] = '{5, 6};\n"
      "    $display(\"%p\", id);\n"
      "    $display(\"%p\", m3);\n"
      "    $display(\"%p\", sa);\n"
      "    $display(\"%p\", ed);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out,
            "'{'{1, 2}, '{3, 4}}\n"
            "'{'{'{0, 1}, '{2, 3}}, '{'{4, 5}, '{6, 7}}}\n"
            "'{'{'{a:0, b:0}, '{a:0, b:0}}, '{'{a:5, b:6}, '{a:0, b:0}}}\n"
            "'{'{ON, OFF}, '{OFF, ON}}\n");
}

// §21.2.1.6 with §7.6 (printed page 160): elements correspond "by the
// left-to-right order of elements in each array", so the pattern %p prints
// lists each dimension from its left bound -- a[3] first for int a[3:0], and in
// dr[1:0][2:3] the subarray dr[1] first, itself from dr[1][2]. Printing from
// the lowest address gave a pattern that, assigned back, reverses the array.
TEST(AssignmentPatternFormat, DescendingDimensionPrintsFromItsLeftBound) {
  auto out = RunSim(
      "module top;\n"
      "  int a[3:0] = '{1, 2, 3, 4};\n"
      "  int dr[1:0][2:3] = '{'{1, 2}, '{3, 4}};\n"
      "  initial $display(\"%p %0d %p %0d\", a, a[3], dr, dr[1][2]);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{1, 2, 3, 4} 1 '{'{1, 2}, '{3, 4}} 1\n");
}

// §21.2.1.6 with §6.19: an enumerated value prints as its member's name when
// every bit matches a member, x and z included, so `XX='x` prints XX and
// `Z='z` prints Z; a value holding x in an enumeration with no x member
// prints as its base type does.
TEST(AssignmentPatternFormat, EnumXAndZMembersPrintByName) {
  auto out = RunSim(
      "module top;\n"
      "  enum integer {IDLE, XX='x, S1='b01, S2='b10} s;\n"
      "  enum logic [1:0] {A, Z='z, B=2} lz;\n"
      "  enum logic [1:0] {P, Q} nx;\n"
      "  initial begin\n"
      "    s = XX; lz = Z;\n"
      "    $display(\"%p %p %p\", s, lz, nx);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "XX Z x\n");
}

// §21.2.1.6 with §7.12 and §7.10.1: the result of a locator or map method is a
// queue, and a slice of a queue or of a fixed-size array is an unpacked array,
// so each passed straight to %p prints as a pattern of its elements, of the
// type the method or slice gives them: a found string quoted, an index a
// number, a string key quoted. Read as the value the expression evaluates to,
// each printed as one packed number.
TEST(AssignmentPatternFormat, ArrayMethodResultsAndSlicesPrintAsPatterns) {
  auto out = RunSim(
      "module t;\n"
      "  int iq[$] = '{3, 1, 2};\n"
      "  string sq[$] = '{\"b\", \"a\"};\n"
      "  int fa[3] = '{7, 5, 6};\n"
      "  int ia[int];\n"
      "  int sa[string];\n"
      "  initial begin\n"
      "    ia[4] = 40; ia[9] = 90; sa[\"k\"] = 1;\n"
      "    $display(\"%p %p %p\", iq.find(x) with (x > 1), iq.min(),\n"
      "             iq.map(x) with (x + 1));\n"
      "    $display(\"%p %p %p\", iq[0:1], iq[1:$], fa[1:2]);\n"
      "    $display(\"%p %p\", sq.find(x) with (x != \"\"),\n"
      "             sq.find_index(x) with (x == \"a\"));\n"
      "    $display(\"%p %p\", ia.max(), sa.find_index(x) with (x > 0));\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out,
            "'{3, 2} '{1} '{4, 2, 3}\n"
            "'{3, 1} '{1, 2} '{5, 6}\n"
            "'{\"b\", \"a\"} '{1}\n"
            "'{90} '{\"k\"}\n");
}

// §21.2.1.6 with §7.4 and §7.10: an array whose elements are queues or
// fixed-size arrays prints each element as a nested pattern of its values --
// a queue of queues, a queue and a dynamic array of fixed-size arrays, an
// associative array of queues -- and an element never written as its type's
// default, 0 for int and x for logic. Read from the element's placeholder,
// each element printed as 0.
TEST(AssignmentPatternFormat, ArraysOfArraysPrintNestedPatterns) {
  auto out = RunSim(
      "module t;\n"
      "  int qq[$][$];\n"
      "  int r[$][3];\n"
      "  int d[][2];\n"
      "  logic [3:0] ld[][2];\n"
      "  int aq[string][$];\n"
      "  initial begin\n"
      "    qq.push_back('{1, 2}); qq.push_back('{3});\n"
      "    r.push_back('{4, 5, 6});\n"
      "    d = new[2]; d[0] = '{7, 8};\n"
      "    ld = new[1];\n"
      "    aq[\"k\"] = '{9};\n"
      "    $display(\"%p %p %p %p %p\", qq, r, d, ld, aq);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out,
            "'{'{1, 2}, '{3}} '{'{4, 5, 6}} '{'{7, 8}, '{0, 0}} '{'{x, x}} "
            "'{\"k\":'{9}}\n");
}

// §21.2.1.6 with §7.12.1 and §7.4.4: a locator over an array whose elements
// are arrays returns a queue of those elements, the subarrays of a
// multidimensional array or the element queues of a queue, so %p prints a
// pattern of their patterns. Declined as no locator result, each printed 0.
TEST(AssignmentPatternFormat, LocatorRowsPrintNestedPatterns) {
  auto out = RunSim(
      "module t;\n"
      "  int m[3][2] = '{'{1, 2}, '{3, 4}, '{5, 0}};\n"
      "  int qq[$][$];\n"
      "  initial begin\n"
      "    qq.push_back('{5}); qq.push_back('{6, 7});\n"
      "    $display(\"%p %p\", m.find with (item[0] > 2),\n"
      "             qq.find with (item.size() > 1));\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{'{3, 4}, '{5, 0}} '{'{6, 7}}\n");
}

// §21.2.1.6 with §26.3 and §3.12.1: an array named through a scope prefix is
// the array the prefix's scope declares -- a package's through `pk::`, printed
// as through an import, and the compilation unit's through `$unit::`, past a
// module's own of the same name. Looked up by no name or by the text alone,
// the package's printed 0 and the unit's printed the module's.
TEST(AssignmentPatternFormat, ArraysNamedThroughAScopePrefixPrintTheirOwn) {
  auto out = RunSim(
      "int uq[$] = '{8, 9};\n"
      "package pk;\n"
      "  int pq[$] = '{1, 2};\n"
      "  int pa[2] = '{3, 4};\n"
      "endpackage\n"
      "module t;\n"
      "  int uq[$] = '{0};\n"
      "  initial $display(\"%p %p %p %p\", pk::pq, pk::pa, $unit::uq, uq);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{1, 2} '{3, 4} '{8, 9} '{0}\n");
}

}  // namespace
