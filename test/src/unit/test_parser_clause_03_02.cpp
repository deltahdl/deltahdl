// §3.2

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignElements, ModuleDeclKindDistinctValues) {
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kInterface);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kProgram, ModuleDeclKind::kChecker);
}

TEST(DesignElements, TopLevelClassIsNotDesignElement) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(DesignElements, AllSevenDesignElementsCoexist) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive udp_id (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_id");
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// §3.2 states that design elements are containers for declarations and
// procedural code. Verify the parser populates a non-empty body for each of
// the seven kinds when given a representative declaration inside.
TEST(DesignElements, DesignElementsContainDeclarations) {
  auto r = Parse(
      "module m; wire w; endmodule\n"
      "program p; int x; endprogram\n"
      "interface ifc; logic s; endinterface\n"
      "checker chk; logic flag; endchecker\n"
      "package pkg; parameter int K = 1; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

// Primitives carry a UDP table rather than a generic items list (§28); the
// non-empty table is the §3.2 "container for procedural code" observation.
TEST(DesignElements, PrimitiveContainsTableRows) {
  auto r = Parse(
      "primitive udp_id (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_FALSE(r.cu->udps[0]->table.empty());
}

// Configurations carry design_cells and rules rather than a generic items
// list (§33); a non-empty design_cells observes the container property.
TEST(DesignElements, ConfigurationContainsDesignCell) {
  auto r = Parse(
      "module top; endmodule\n"
      "config cfg; design top; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_FALSE(r.cu->configs[0]->design_cells.empty());
}

// §3.2 names declarations and procedural code together as the contents a
// design element holds. Observe the combined claim within a single body by
// putting both content kinds inside one module and confirming the items
// vector picks up at least one of each.
TEST(DesignElements, DesignElementContainsBothDeclarationAndProceduralBlock) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  initial begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

}  // namespace
