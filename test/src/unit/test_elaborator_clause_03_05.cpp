#include "fixture_elaborator.h"

namespace {

TEST(ElabClause03, InterfaceWithVariablesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, InterfaceWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->ports.size(), 1u);
}

TEST(ElabClause03, InterfaceWithContAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, SimpleBusExampleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface\n",
      f, "simple_bus");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, InterfaceWithSubroutinesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  function automatic int xform(int v); return v; endfunction\n"
      "  task send; endtask\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
