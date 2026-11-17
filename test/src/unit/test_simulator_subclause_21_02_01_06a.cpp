#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSim(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  return testing::internal::GetCapturedStdout();
}

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

TEST(AssignmentPatternFormat, StructMemberWithUnknownValuePrintsX) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t s;\n"
      "  initial $display(\"%p\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:x, b:x}\n");
}

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

TEST(AssignmentPatternFormat, EnumWithUnnamedValueFallsBackToBaseType) {
  auto out = RunSim(
      "module t;\n"
      "  typedef enum logic [1:0] { RED, GREEN, BLUE } color_e;\n"
      "  color_e c;\n"
      "  initial $display(\"%p\", c);\n"
      "endmodule\n");
  EXPECT_EQ(out, "x\n");
}

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

TEST(AssignmentPatternFormat, NullClassHandlePrintsNull) {
  auto out = RunSim(
      "class C; endclass\n"
      "module t;\n"
      "  C h;\n"
      "  initial $display(\"%p\", h);\n"
      "endmodule\n");
  EXPECT_EQ(out, "null\n");
}

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

TEST(AssignmentPatternFormat, EmptyQueuePrintsEmptyPattern) {
  auto out = RunSim(
      "module t;\n"
      "  int q [$];\n"
      "  initial $display(\"%p\", q);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{}\n");
}

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

TEST(AssignmentPatternFormat, NullChandlePrintsNull) {
  auto out = RunSim(
      "module t;\n"
      "  chandle ch;\n"
      "  initial $display(\"%p\", ch);\n"
      "endmodule\n");
  EXPECT_EQ(out, "null\n");
}

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

TEST(AssignmentPatternFormat, StructFromPatternInitializerRoundTrips) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $display(\"%p\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat, ArrayFromPatternInitializerRoundTrips) {
  auto out = RunSim(
      "module t;\n"
      "  int a [3] = '{5, 6, 7};\n"
      "  initial $display(\"%p\", a);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{5, 6, 7}\n");
}

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

TEST(AssignmentPatternFormat, WriteTaskRendersPatternWithoutNewline) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $write(\"%p|\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}|");
}

TEST(AssignmentPatternFormat, UppercaseSpecifierRendersPattern) {
  auto out = RunSim(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t s = '{8'd1, 8'd2};\n"
      "  initial $display(\"%P\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{a:1, b:2}\n");
}

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

TEST(AssignmentPatternFormat, DescendingDimensionPrintsFromItsLeftBound) {
  auto out = RunSim(
      "module top;\n"
      "  int a[3:0] = '{1, 2, 3, 4};\n"
      "  int dr[1:0][2:3] = '{'{1, 2}, '{3, 4}};\n"
      "  initial $display(\"%p %0d %p %0d\", a, a[3], dr, dr[1][2]);\n"
      "endmodule\n");
  EXPECT_EQ(out, "'{1, 2, 3, 4} 1 '{'{1, 2}, '{3, 4}} 1\n");
}

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

TEST(FormatPSim, ArrayPropertyThroughAHandlePrintsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class H;\n"
                       "  int q[$];\n"
                       "  int a[3];\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    automatic H h = new;\n"
                       "    h.q = '{5, 2, 9};\n"
                       "    h.a = '{1, 2, 3};\n"
                       "    $display(\"%p %p %0d\", h.q, h.a, h.q.size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{5, 2, 9} '{1, 2, 3} 3\n");
}

TEST(FormatPSim, ArrayPropertyTwoHandlesDownPrintsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class In;\n"
                       "  int q[$];\n"
                       "endclass\n"
                       "class Out;\n"
                       "  In inner = new;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    automatic Out o = new;\n"
                       "    o.inner.q = '{5, 2, 9};\n"
                       "    $display(\"%p\", o.inner.q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{5, 2, 9}\n");
}

}  // namespace
