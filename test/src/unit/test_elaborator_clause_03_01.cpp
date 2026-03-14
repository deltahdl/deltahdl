#include "fixture_elaborator.h"

namespace {

// §3.1 General — overview-level elaboration tests.

TEST(BuildingBlockElaboration, MinimalModuleElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BuildingBlockElaboration, MinimalInterfaceElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("interface ifc; endinterface", f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BuildingBlockElaboration, MinimalProgramElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("program p; endprogram", f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BuildingBlockElaboration, TopModuleNotFoundReturnsNull) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(BuildingBlockElaboration, EmptySourceTopNotFoundReturnsNull) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(BuildingBlockElaboration, ElaboratedDesignContainsTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(BuildingBlockElaboration, ModuleWithPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef int myint;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(BuildingBlockElaboration, MinimalCheckerElaboratesSuccessfully) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BuildingBlockElaboration, SelectSpecificTopFromMultipleModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "b");
}

TEST(BuildingBlockElaboration, ModuleWithChildInstanceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_FALSE(design->top_modules[0]->children.empty());
}

TEST(BuildingBlockElaboration, NestedHierarchyTwoLevelsDeep) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(BuildingBlockElaboration, AllModulesMapPopulated) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(design->all_modules.find("top"), design->all_modules.end());
  EXPECT_NE(design->all_modules.find("child"), design->all_modules.end());
}

TEST(BuildingBlockElaboration, ModuleWithPackageImportAndUsage) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_t x;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BuildingBlockElaboration, CuScopeFunctionVisibleInDesign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "function int add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m; endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->cu_function_decls.empty());
}

TEST(BuildingBlockElaboration, ModuleWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->ports.empty());
}

TEST(BuildingBlockElaboration, ModuleWithContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
}

TEST(BuildingBlockElaboration, ModuleWithAlwaysCombElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->processes.empty());
}

TEST(BuildingBlockElaboration, InterfaceWithModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(BuildingBlockElaboration, MultiplePackagesElaborate) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t1;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

TEST(BuildingBlockElaboration, ModuleWithParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
