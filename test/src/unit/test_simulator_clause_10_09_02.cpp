#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StructPatternSimulation, NamedStructPatternWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, default: 8'd99};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2659u);
}

TEST(StructPatternSimulation, NamedStructPatternOnlyDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{default: 8'd55};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { int x; int y; } pair_t;\n"
      "  pair_t s;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 1;\n"
      "    s = pair_t'{1, 2 + k};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), (uint64_t{1} << 32) | 3);
}

// §10.9.2: each member expression is evaluated in the context of an assignment
// to the corresponding member's type, so a value wider than the member is
// narrowed to the member's width -- observed here by truncating a 16-bit value
// down to an 8-bit member.
TEST(StructPatternSimulation, MemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 16'hABCD, b: 8'h5A};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD5Au);
}

// §10.9.2: a by-name member value is an arbitrary expression evaluated in the
// context of an assignment to that member -- here a runtime `k + 1` is computed
// through the named-key path and placed into member a.
// §10.9.2: in a positional structure pattern each element is evaluated in the
// context of an assignment to its corresponding member's type, so an element
// wider than its member is narrowed to the member width -- it is not
// concatenated at its self-determined width, which would spill into and corrupt
// the following members.
TEST(StructPatternSimulation, PositionalMemberValueCoercedToMemberWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{16'h1234, 4'h5};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3405u);
}

TEST(StructPatternSimulation, NamedMemberValueEvaluatesExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  int k;\n"
      "  initial begin\n"
      "    k = 5;\n"
      "    p = pair_t'{a: k + 1, b: 8'h02};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0602u);
}

TEST(StructPatternSimulation, ThreeTierPrecedence) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(var->value.ToUint64(), expected);
}

TEST(StructPatternSimulation, TypeKeyMultipleFieldsPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), (uint64_t{42} << 32) | 42);
}

// §10.9.2: a type key names a data type and sets every field whose type matches
// it -- here the `logic` vector key covers both logic members (distinct from
// the integer-atom key forms exercised elsewhere).
TEST(StructPatternSimulation, LogicTypeKeyAppliesToVectorFields) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{logic: 8'hCD};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDCDu);
}

// §10.9.2: the default: key is applied recursively to each member of an
// unmatched substructure, so every leaf of the nested struct receives the
// default value -- not just the low bits of the substructure field.
TEST(StructPatternSimulation, DefaultKeyRecursesIntoNestedStruct) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABABu);
}

// §10.9.2: when the same type key appears more than once, the last value is
// used -- and it is applied to every field of that type.
TEST(StructPatternSimulation, TypeKeyLastValueWinsPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{byte: 8'h11, byte: 8'h22};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2222u);
}

TEST(StructPatternSimulation, ReplicationInStructContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{2{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABu);
}

}  // namespace
