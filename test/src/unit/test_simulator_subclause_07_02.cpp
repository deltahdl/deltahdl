#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context_types.h"

using namespace delta;

static void VerifyStructField(const StructFieldInfo& field,
                              const char* expected_name,
                              uint32_t expected_offset, uint32_t expected_width,
                              size_t index) {
  EXPECT_EQ(field.name, expected_name) << "field " << index;
  EXPECT_EQ(field.bit_offset, expected_offset) << "field " << index;
  EXPECT_EQ(field.width, expected_width) << "field " << index;
}

namespace {

TEST(StructType, RegisterAndFind_Metadata) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});
  info.fields.push_back({"y", 0, 8});

  f.ctx.RegisterStructType("point_t", info);
  auto* found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->type_name, "point_t");
  EXPECT_TRUE(found->is_packed);
  EXPECT_EQ(found->total_width, 16u);
  ASSERT_EQ(found->fields.size(), 2u);
}

TEST(StructType, RegisterAndFind_Fields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});
  info.fields.push_back({"y", 0, 8});

  f.ctx.RegisterStructType("point_t", info);
  auto* found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  ASSERT_EQ(found->fields.size(), 2u);

  VerifyStructField(found->fields[0], "x", 8, 8, 0);
  VerifyStructField(found->fields[1], "y", 0, 8, 1);
}

TEST(StructType, FindNonexistent) {
  SimFixture f;
  EXPECT_EQ(f.ctx.FindStructType("no_such_type"), nullptr);
}

TEST(StructType, SetVariableStructType) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "color_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8});
  info.fields.push_back({"g", 8, 8});
  info.fields.push_back({"b", 0, 8});
  f.ctx.RegisterStructType("color_t", info);

  f.ctx.CreateVariable("pixel", 24);
  f.ctx.SetVariableStructType("pixel", "color_t");

  auto* type = f.ctx.GetVariableStructType("pixel");
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->type_name, "color_t");
  EXPECT_EQ(type->fields.size(), 3u);
}

TEST(StructType, GetVariableStructTypeUnknown) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetVariableStructType("nonexistent"), nullptr);
}

TEST(StructType, FieldTypeKindPreserved) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "typed_s";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});
  f.ctx.RegisterStructType("typed_s", info);
  auto* found = f.ctx.FindStructType("typed_s");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->fields[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(found->fields[1].type_kind, DataTypeKind::kByte);
}

TEST(StructMemberAccess, MemberAccessBasic) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("s.x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* acc = f.arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = MakeId(f.arena, "s");
  acc->rhs = MakeId(f.arena, "x");

  auto result = EvalExpr(acc, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

// §7.2 with §6.18: a member declared through a typedef holds the typedef's
// type -- `ab_e e` of `typedef enum logic [1:0] {A=1, B=2} ab_e` two bits,
// `six_t w` of `typedef logic [5:0] six_t` six -- in an unpacked struct and a
// packed one alike, as $bits of the struct already counted them. The run-time
// layout gave each one bit, so B and 6'h2a read back as 0.
TEST(StructType, MembersDeclaredThroughTypedefsHoldTheirWidth) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum logic [1:0] {A=1, B=2} ab_e;\n"
      "  typedef logic [5:0] six_t;\n"
      "  typedef struct {ab_e e; six_t w; int n;} s_t;\n"
      "  typedef struct packed {ab_e e; six_t w;} ps_t;\n"
      "  s_t s = '{B, 6'h2a, 3};\n"
      "  ps_t ps = '{B, 6'h2a};\n"
      "  initial $display(\"%0d %h %0d %0d %h %h %p\", s.e, s.w, s.n, ps.e, "
      "ps.w,\n"
      "                   ps, s);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2a 3 2 2a aa '{e:B, w:42, n:3}\n");
}

}  // namespace
