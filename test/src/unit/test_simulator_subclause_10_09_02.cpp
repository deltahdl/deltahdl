#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

std::string WideStructSource(std::string_view body) {
  return std::string(
             "module t;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [63:0] b;\n"
             "  } wide_t;\n"
             "  wide_t w1, w2;\n"
             "  initial begin\n") +
         std::string(body) +
         "  end\n"
         "endmodule\n";
}

TEST(StructPatternSimulation,
     WideStructNamedPatternPlacesAMemberAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      WideStructSource("    w1 = '{a: 8'hA5, b: 64'h42};\n"), f, "w1");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 0xA5u);
  EXPECT_EQ(var->value.words[0].aval, 0x42u);
  EXPECT_EQ(var->value.words[1].bval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(StructPatternSimulation, NamedStructPatternCarriesAnUnknownMemberValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{a: 8'bxxxxxxxx, b: 8'h42};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx01000010");
}

TEST(StructPatternSimulation,
     WideStructNamedPatternAgreesWithThePositionalSpelling) {
  SimFixture f;
  auto* design =
      ElaborateSrc(WideStructSource("    w1 = '{a: 8'bxxxxxxxx, b: 64'h42};\n"
                                    "    w2 = '{8'bxxxxxxxx, 64'h42};\n"),
                   f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* keyed = f.ctx.FindVariable("w1");
  auto* positional = f.ctx.FindVariable("w2");
  ASSERT_NE(keyed, nullptr);
  ASSERT_NE(positional, nullptr);
  ASSERT_EQ(keyed->value.nwords, positional->value.nwords);
  for (uint32_t i = 0; i < keyed->value.nwords; ++i) {
    SCOPED_TRACE(testing::Message() << "word " << i);
    EXPECT_EQ(keyed->value.words[i].aval, positional->value.words[i].aval);
    EXPECT_EQ(keyed->value.words[i].bval, positional->value.words[i].bval);
  }
}

TEST(StructPatternSimulation,
     WideStructDefaultKeyPlacesEveryMemberAboveTheFirstWord) {
  SimFixture f;
  auto* var =
      RunAndFindVar(WideStructSource("    w1 = '{default: 8'hA5};\n"), f, "w1");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 0xA5u);
  EXPECT_EQ(var->value.words[0].aval, 0xA5u);
}

TEST(StructPatternSimulation, NamedStructPatternWithDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, default: 8'd99};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2659u);
}

TEST(StructPatternSimulation, NamedStructPatternOnlyDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{default: 8'd55};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 14135u);
}

TEST(StructPatternSimulation, NestedAssignmentPatternEvaluates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  typedef struct { pair_t p1; pair_t p2; } nested_t;\n"
      "  nested_t n;\n"
      "  initial begin\n"
      "    n = '{'{8'd1, 8'd2}, '{8'd3, 8'd4}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.has_errors);
}

TEST(StructPatternSimulation, PositionalWithExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { int x; int y; } pair_t;\n"
      "  pair_t s;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 1;\n"
      "    s = pair_t'{1, 2 + k};\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), (uint64_t{1} << 32) | 3);
}

TEST(StructPatternSimulation, MemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 16'hABCD, b: 8'h5A};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD5Au);
}

TEST(StructPatternSimulation, PositionalMemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{16'h1234, 4'h5};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3405u);
}

TEST(StructPatternSimulation, NamedMemberValueEvaluatesExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 5;\n"
      "    p = pair_t'{a: k + 1, b: 8'h02};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0602u);
}

TEST(StructPatternSimulation, ThreeTierPrecedence) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    byte a;\n"
      "    byte b;\n"
      "    logic [7:0] c;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    s = s_t'{a: 8'd1, byte: 8'd2, default: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);

  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(var->value.ToUint64(), expected);
}

TEST(StructPatternSimulation, TypeKeyMultipleFieldsPipeline) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    int a;\n"
      "    int b;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{int: 32'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), (uint64_t{42} << 32) | 42);
}

TEST(StructPatternSimulation, ALogicKeyLeavesVectorMembersToTheDefault) {
  const char* src =
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p, q;\n"
      "  initial begin\n"
      "    p = pair_t'{logic: 8'hCD, default: 0};\n"
      "    q = pair_t'{byte_t: 8'hCD};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 0u);
  EXPECT_EQ(RunAndGet(src, "q"), 0xCDCDu);
}

TEST(StructPatternSimulation, DefaultKeyRecursesIntoNestedStruct) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] c; } bc_t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    bc_t bc;\n"
      "  } d_t;\n"
      "  d_t d;\n"
      "  initial begin\n"
      "    d = '{default: 8'hAB};\n"
      "  end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABABu);
}

TEST(StructPatternSimulation, TypeKeyLastValueWinsPipeline) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{byte: 8'h11, byte: 8'h22};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2222u);
}

TEST(StructPatternSimulation, ReplicationInStructContext) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{2{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABu);
}

TEST(StructPatternSimulation,
     NestedPositionalPatternIsPlacedByTheMembersLayout) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { int a; int b; } pair_t;\n"
      "  typedef struct packed { pair_t p; int c; } outer_t;\n"
      "  outer_t s;\n"
      "  int y;\n"
      "  initial begin\n"
      "    s = '{'{b: 2, a: 1}, 3};\n"
      "    y = s.p.a * 100 + s.p.b * 10 + s.c;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(StructPatternSimulation, NestedKeyedPatternIsPlacedByTheMembersLayout) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { int a; int b; } pair_t;\n"
      "  typedef struct packed { pair_t p; int c; } outer_t;\n"
      "  outer_t s;\n"
      "  int y;\n"
      "  initial begin\n"
      "    s = '{p: '{8'd1, 8'd2}, c: 3};\n"
      "    y = s.p.a * 100 + s.p.b * 10 + s.c;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(StructPatternSimulation,
     KeyedPatternInitializesAssociativeArrayOfStructs) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {ON, OFF} switch_e;\n"
      "  typedef struct {switch_e sw; string s;} pair_t;\n"
      "  typedef struct {int a; int b;} ab_t;\n"
      "  pair_t va[int] = '{10:'{OFF, \"switch10\"}, 20:'{ON, \"switch20\"}};\n"
      "  ab_t vb[int] = '{1:'{5, 6}, 2:'{7, 8}};\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", va.num(), vb.num(),\n"
      "                   vb[1].a, vb[2].b, va.exists(20));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "2 2 5 8 1\n");
}

TEST(StructAssignmentPatternRun, AnItemFillsADynamicArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a; byte data[]; } h_t;\n"
      "module t;\n"
      "  h_t z, y;\n"
      "  initial begin\n"
      "    z = '{a: 3, data: '{7, 8, 9}};\n"
      "    y = '{4, '{5, 6}};\n"
      "    $display(\"%0d %0d %0d | %0d %0d %0d\", z.a, z.data.size(),\n"
      "             z.data[2], y.a, y.data.size(), y.data[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3 9 | 4 2 6\n");
}

TEST(StructPatternSimulation, DefaultKeyGivesAStringMemberTheString) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  typedef struct {string t;} in_t;\n"
      "  typedef struct {int n; in_t in;} out_t;\n"
      "  pair_t first, p;\n"
      "  out_t o;\n"
      "  initial begin\n"
      "    first.s = \"first\";\n"
      "    p = '{default: \"hi\"};\n"
      "    o = '{n: 4, default: \"ok\"};\n"
      "    $display(\"%0d [%s] %0d [%s]\", p.n, p.s, o.n, o.in.t);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "26729 [hi] 4 [ok]\n");
}

TEST(StructPatternSimulation, MemberKeyPatternGivesEachStringElementItsText) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {string v [2];} names_t;\n"
      "  names_t m;\n"
      "  initial begin\n"
      "    m = '{v: '{\"abcdefghij\", \"xy\"}};\n"
      "    $display(\"[%s] [%s]\", m.v[0], m.v[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "[abcdefghij] [xy]\n");
}

TEST(StructPatternSimulation,
     TypeAndDefaultKeysFillEachElementOfAnArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a [2]; string v [2];} rec_t;\n"
      "  rec_t r;\n"
      "  initial begin\n"
      "    r = '{default: 5, string: \"z\"};\n"
      "    $display(\"%0d %0d [%s] [%s]\", r.a[0], r.a[1], r.v[0], r.v[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "5 5 [z] [z]\n");
}

TEST(StructPatternSim, ATypeKeyReachesTheMembersOfANestedStructure) {
  const char* src =
      "module t;\n"
      "  struct packed { int A; struct packed { int B, C; } BC; } s;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    s = '{int: 5, default: 0};\n"
      "    a = s.A; b = s.BC.B; c = s.BC.C;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 5u);
  EXPECT_EQ(RunAndGet(src, "b"), 5u);
  EXPECT_EQ(RunAndGet(src, "c"), 5u);
}

TEST(StructPatternSim, ADefaultOfAMembersOwnTypeIsAssignedWhole) {
  const char* src =
      "typedef struct packed { logic [7:0] a, b; } pair_t;\n"
      "typedef struct packed { logic [7:0] c, d; } other_t;\n"
      "module t;\n"
      "  pair_t pv = '{8'h12, 8'h34};\n"
      "  int k = 7;\n"
      "  struct packed { pair_t p; other_t o; int x; } s;\n"
      "  struct packed { pair_t p; int x; } s2;\n"
      "  logic [15:0] sp, so, s2p;\n"
      "  initial begin\n"
      "    s = '{default: pv};\n"
      "    s2 = '{default: k};\n"
      "    sp = s.p; so = s.o; s2p = s2.p;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "sp"), 0x1234u);
  EXPECT_EQ(RunAndGet(src, "so"), 0x3434u);
  EXPECT_EQ(RunAndGet(src, "s2p"), 0x0707u);
}

TEST(StructPatternSim, ATypedefKeySetsTheMembersOfItsType) {
  const char* src =
      "typedef logic [7:0] byte_t;\n"
      "module t;\n"
      "  struct packed { byte_t a, b; } s;\n"
      "  struct packed { logic [7:0] c; int d; } u;\n"
      "  initial begin\n"
      "    s = '{byte_t: 8'h1};\n"
      "    u = '{byte_t: 8'h7, default: 0};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "s"), 0x0101u);
  EXPECT_EQ(RunAndGet(src, "u"), uint64_t{0x07} << 32);
}

TEST(StructPatternSim, AnIntKeyMatchesASignedBitVectorOfItsRange) {
  const char* src =
      "module t;\n"
      "  struct packed { bit signed [31:0] a; bit [31:0] b; } s;\n"
      "  initial s = '{int: 5, default: 0};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "s"), uint64_t{5} << 32);
}

TEST(StructPatternSim, ATypeKeyMatchesOnlyAMemberOfItsPackedBounds) {
  const char* src =
      "typedef logic [7:0] byte_t;\n"
      "module t;\n"
      "  struct packed { logic [8:1] a; logic [1:0][3:0] b; logic [7:0] c; } "
      "s;\n"
      "  initial s = '{byte_t: 8'h5A, default: 0};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "s"), 0x5Au);
}

TEST(StructPatternSim, AnElementTypeKeyDoesNotSetADynamicArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { longint a; longint d[]; } h_t;\n"
      "module t;\n"
      "  h_t z;\n"
      "  initial begin\n"
      "    z = '{longint: 5, default: 0};\n"
      "    $display(\"%0d %0d\", z.a, z.d.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 0\n");
}

TEST(StructPatternSim, AStructureTypeKeySetsOnlyAMemberOfThatType) {
  const char* src =
      "typedef struct packed { logic [7:0] a, b; } pair_t;\n"
      "module t;\n"
      "  pair_t pv = '{8'h12, 8'h34};\n"
      "  struct packed { pair_t p; shortint x; } s;\n"
      "  initial s = '{pair_t: pv, default: 0};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "s"), 0x12340000u);
}

TEST(StructPatternSim, AKeyedPatternSetsAProceduralVariableByItsKeys) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module t;\n"
      "  function automatic int fa();\n"
      "    s_t v = '{b: 8'h6, a: 7};\n"
      "    return v.a * 100 + v.b;\n"
      "  endfunction\n"
      "  function int fs();\n"
      "    static s_t v = '{b: 8'h2, default: 3};\n"
      "    return v.a * 100 + v.b;\n"
      "  endfunction\n"
      "  task automatic tk(output int r);\n"
      "    s_t v = '{b: 8'h4, int: 9};\n"
      "    r = v.a * 100 + v.b;\n"
      "  endtask\n"
      "  initial begin : blk\n"
      "    automatic s_t v = '{b: 8'h1, a: 5};\n"
      "    static struct { int a; logic [7:0] b; } u = '{b: 8'h3, a: 4};\n"
      "    int r;\n"
      "    tk(r);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", fa(), fs(), r, v.a * 100 + v.b,\n"
      "             u.a * 100 + u.b);\n"
      "    fork\n"
      "      begin\n"
      "        automatic s_t w = '{b: 8'h8, a: 2};\n"
      "        $display(\"%0d\", w.a * 100 + w.b);\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "706 302 904 501 403\n208\n");
}

TEST(StructPatternSim, ATopLevelMemberKeyLeavesANestedNamesakeToTheDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct { int x; struct { int x; int y; } s; } "
                 "st;\n"
                 "  st v;\n"
                 "  initial begin\n"
                 "    v = '{x: 5, default: 9};\n"
                 "    $display(\"%0d %0d %0d\", v.x, v.s.x, v.s.y);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5 9 9\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
