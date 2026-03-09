#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimClause05, Cl5_12_AttrOnVarDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state *) logic [7:0] x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0xAB);
}

TEST(SimClause05, Cl5_12_AttrWithValueOnDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state = 1 *) logic [7:0] y = 8'hCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 0xCD);
}

TEST(SimClause05, Cl5_12_MultipleAttrSpecs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* full_case, parallel_case *) logic [7:0] z = 8'hEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("z")->value.ToUint64(), 0xEF);
}

TEST(SimClause05, Cl5_12_MultipleSeparateInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* full_case = 1 *)\n"
      "  (* parallel_case = 1 *)\n"
      "  logic [7:0] w = 8'h77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 0x77);
}

TEST(SimClause05, Cl5_12_AttrOnInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  (* synthesis_off *) initial begin\n"
      "    a = 8'h55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x55);
}

TEST(SimClause05, Cl5_12_AttrOnAssignStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    (* mark *) b = 8'hDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xDD);
}

TEST(SimClause05, Cl5_12_AttrOnIfStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    (* high_pri *) if (1) c = 8'hAA;\n"
      "    else c = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xAA);
}

TEST(SimClause05, Cl5_12_AttrOnCaseStmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (8'd2)\n"
      "      8'd1: d = 8'h11;\n"
      "      8'd2: d = 8'h22;\n"
      "      default: d = 8'h00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 0x22);
}

TEST(SimClause05, Cl5_12_AttrOnForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] e;\n"
      "  initial begin\n"
      "    e = 0;\n"
      "    (* unroll *) for (int i = 0; i < 3; i = i + 1)\n"
      "      e = e + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("e")->value.ToUint64(), 3);
}

TEST(SimClause05, Cl5_12_AttrWithStringValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* mode = \"fast\" *) logic [7:0] g = 8'h99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("g")->value.ToUint64(), 0x99);
}

}  // namespace
