#include "builders_ast.h"
#include "fixture_program.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ElabA60701, StructPositionalPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd10, 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(ElabA60701, TypedPatternExpressionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } coord_t;\n"
      "  coord_t c;\n"
      "  initial begin\n"
      "    c = coord_t'{x: 8'd5, y: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(SimA60701, NamedStructPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, b: 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(SimA60701, NamedStructPatternReversedOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{b: 8'd20, a: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(SimA60701, PositionalStructPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd3, 8'd7};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 775u);
}

TEST(SimA60701, ThreeFieldStructNamedPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] x;\n"
      "    logic [7:0] y;\n"
      "    logic [7:0] z;\n"
      "  } triple_t;\n"
      "  triple_t v;\n"
      "  initial begin\n"
      "    v = triple_t'{x: 8'd1, y: 8'd2, z: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x010203u);
}

TEST(SimA60701, ConstPatternInVarDeclInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p = '{8'd100, 8'd200};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 25800u);
}

TEST(Elaboration, StructPattern_InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, StructPattern_DuplicateKey) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §10.9.2: Struct pattern that does not cover all members is an error.
TEST(Elaboration, StructPattern_UncoveredMember) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabA60701, StructNamedPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
