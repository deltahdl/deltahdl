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

// §7.2.1 with §6.11: a member reads as the type it is declared with, so a
// shortint and a byte member of an unpacked struct hold -2 and -3, a
// `logic signed [3:0]` member -1, and a `bit [3:0]` member 15; each compares
// below zero exactly when its type is signed.
TEST(StructType, SignedMembersOfAnUnpackedStructReadSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {\n"
      "    shortint address; byte c; logic signed [3:0] s; bit [3:0] u;\n"
      "  } Plain;\n"
      "  Plain pl;\n"
      "  initial begin\n"
      "    pl.address = -2;\n"
      "    pl.c = -3;\n"
      "    pl.s = -1;\n"
      "    pl.u = -1;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", pl.address, pl.c, pl.s, "
      "pl.u, pl.c < 0, pl.u < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-2 -3 -1 15 1 0\n");
}

// §7.2 and §7.3 with §6.21: a structure or union declared in an initial block
// or a static task has storage like any variable, so a whole assignment, a
// member write and a member read all reach it -- st holds 9 and 1, the union
// reads 16'h1234 through either member, the inline packed struct's x holds 5,
// and the task's local 7. Bound to no layout, each member read 0 or x.
TEST(StructType, AggregateLocalsOfAStaticBlockAndTaskHoldTheirValues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int x; byte y;} s_t;\n"
      "  typedef union packed {bit [15:0] w; bit [1:0][7:0] b;} u_t;\n"
      "  int bx, by, uw, ub, px, tx;\n"
      "  task tk; s_t ts; ts.x = 7; tx = ts.x; endtask\n"
      "  initial begin\n"
      "    s_t st;\n"
      "    u_t u;\n"
      "    struct packed {int x; byte y;} ps;\n"
      "    st = '{8, 1};\n"
      "    st.x = st.x + 1;\n"
      "    bx = st.x; by = st.y;\n"
      "    u.w = 16'h1234;\n"
      "    uw = u.w; ub = u.b;\n"
      "    ps.x = 5;\n"
      "    px = ps.x;\n"
      "    tk();\n"
      "    $display(\"%0d %0d %h %h %0d %0d\", bx, by, uw, ub, px, tx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 1 00001234 00001234 5 7\n");
}

// §7.2 with §7.4.2: an unpacked array member of an unpacked struct holds each
// of its elements, so m.v[1] and m.v[3] keep 20 and 40 beside n's 5, the
// struct is 32 + 4*32 = 160 bits, and a member after an array member keeps
// its own value. Laid out as one element, the writes landed in n or nowhere.
TEST(StructType, UnpackedArrayMemberHoldsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int n; int v[4]; } rec_t;\n"
      "  typedef struct { int v[2]; byte tail; } t_t;\n"
      "  rec_t m;\n"
      "  t_t t2;\n"
      "  initial begin\n"
      "    m.v[1] = 20; m.v[3] = 40; m.n = 5;\n"
      "    t2.v[0] = 7; t2.v[1] = 9; t2.tail = 3;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", m.v[1], m.v[3], m.n,\n"
      "             $bits(m), t2.v[0], t2.v[1], t2.tail);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20 40 5 160 7 9 3\n");
}

}  // namespace
