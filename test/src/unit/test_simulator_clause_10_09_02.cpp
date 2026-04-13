#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StructPattern, NamedMemberTwoFields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"x", "y"};
  pat->elements = {MakeInt(f.arena, 5), MakeInt(f.arena, 10)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberReversedOrder) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"y", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"y", "x"};
  pat->elements = {MakeInt(f.arena, 10), MakeInt(f.arena, 5)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(StructPattern, NamedMemberThreeFields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "rgb_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8, DataTypeKind::kLogic});
  info.fields.push_back({"g", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"r", "g", "b"};
  pat->elements = {MakeInt(f.arena, 0xFF), MakeInt(f.arena, 0x80),
                   MakeInt(f.arena, 0x00)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFF8000u);
}

TEST(StructPattern, DefaultAllFields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"default"};
  pat->elements = {MakeInt(f.arena, 0xFF)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFFFu);
}

TEST(StructPattern, DefaultWithNamedOverride) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "default"};
  pat->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 0)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0100u);
}

TEST(StructPattern, TypeKeyedInt) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "mixed_t";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"int"};
  pat->elements = {MakeInt(f.arena, 42)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), uint64_t{42} << 8);
}

TEST(StructPattern, MixedPrecedence) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "multi_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"a", 16, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "byte", "default"};
  pat->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                   MakeInt(f.arena, 3)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(result.ToUint64(), expected);
}

TEST(StructPattern, TypeKeyMatchesMultipleFields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"byte"};
  pat->elements = {MakeInt(f.arena, 0xAB)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABABu);
}

TEST(StructPattern, TypeKeyLastWins) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"byte", "byte"};
  pat->elements = {MakeInt(f.arena, 0x11), MakeInt(f.arena, 0x22)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x2222u);
}

TEST(StructPattern, TypeKeyOverridesDefault) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "mixed_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"a", 16, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"byte", "default"};
  pat->elements = {MakeInt(f.arena, 0xAA), MakeInt(f.arena, 0xFF)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  // byte key matches a and b (0xAA each), default fills c (0xFF).
  uint64_t expected = (uint64_t{0xAA} << 16) | (uint64_t{0xAA} << 8) | 0xFF;
  EXPECT_EQ(result.ToUint64(), expected);
}

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
  // a=1 (member key), b=2 (byte type key), c=3 (default).
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
  // Both int fields get 42.
  EXPECT_EQ(var->value.ToUint64(), (uint64_t{42} << 32) | 42);
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
