// §11.4.5: Equality operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// ==========================================================================
// Equality X/Z propagation — §11.4.5, §11.4.6
// ==========================================================================
TEST(EvalOpXZ, LogicalEqX) {
  SimFixture f;
  // 4'b1x00 == 4'b1100 → x
  MakeVar4(f, "el", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("er", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "el"),
                          MakeId(f.arena, "er"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalNeqX) {
  SimFixture f;
  // 4'b1x00 != 4'b1100 → x
  MakeVar4(f, "nl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("nr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "nl"),
                          MakeId(f.arena, "nr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, CaseEqStillExact) {
  SimFixture f;
  // === still compares aval+bval exactly, no X propagation
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// § expression — equality comparison
TEST(SimA83, EqualityTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § expression — inequality comparison
TEST(SimA83, InequalityTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (equality) — Simulation
// =============================================================================
// § binary_operator — == (true)
TEST(SimA86, BinaryEqTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 == 8'd10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — != (true)
TEST(SimA86, BinaryNeqTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 != 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — === (case equality)
TEST(SimA86, BinaryCaseEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 === 8'd7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — !== (case inequality)
TEST(SimA86, BinaryCaseNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalAdv, PackedStructEqualitySameValue) {
  SimFixture f;
  // Two 16-bit packed struct vars with same value → == is 1.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s1", 16, 0xABCD);
  MakeVar(f, "s2", 16, 0xABCD);
  f.ctx.SetVariableStructType("s1", "my_struct");
  f.ctx.SetVariableStructType("s2", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s1"),
                          MakeId(f.arena, "s2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PackedStructEqualityDiffValue) {
  SimFixture f;
  // Two 16-bit packed struct vars with different values → == is 0.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s3", 16, 0xABCD);
  MakeVar(f, "s4", 16, 0x1234);
  f.ctx.SetVariableStructType("s3", "my_struct");
  f.ctx.SetVariableStructType("s4", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s3"),
                          MakeId(f.arena, "s4"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
