#include "fixture_elaborator.h"

namespace {

// §3.1: Design elements are containers for declarations and procedural code.
// The elaborator must accept each design element kind as a valid container.

TEST(ElabClause03, Cl3_1_ModuleAsContainer) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithProceduralBlock) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, d, q;\n"
             "  always_ff @(posedge clk) q <= d;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithSubroutine) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithPorts) {
  EXPECT_TRUE(
      ElabOk("module m(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_EmptyModuleElaborates) {
  EXPECT_TRUE(ElabOk("module m; endmodule\n"));
}

// §3.1: Programs are design element containers (§3.4).

TEST(ElabClause03, Cl3_1_EmptyProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_1_ProgramAsContainer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  logic a;\n"
      "  initial a = 1;\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_1_ProgramWithPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p(input logic clk);\n"
      "  initial begin end\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §3.1: Interfaces are design element containers (§3.5).

TEST(ElabClause03, Cl3_1_EmptyInterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("interface ifc; endinterface\n", f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_1_InterfaceAsContainer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] data;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_1_InterfaceWithPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc(input logic clk);\n"
      "  logic ready;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §3.1: Checkers are design element containers (§3.6).

TEST(ElabClause03, Cl3_1_EmptyCheckerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker\n", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_1_CheckerAsContainer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §3.1: The elaborator rejects an unknown top-level name.

TEST(ElabClause03, Cl3_1_UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
