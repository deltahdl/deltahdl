// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.1 — Error: missing end-keyword.
TEST(CompilationUnitStructure, MissingEndmoduleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

TEST(CompilationUnitStructure, MissingEndpackageIsError) {
  EXPECT_FALSE(ParseOk("package p;"));
}

TEST(CompilationUnitStructure, MissingEndinterfaceIsError) {
  EXPECT_FALSE(ParseOk("interface i;"));
}

TEST(CompilationUnitStructure, MissingEndprogramIsError) {
  EXPECT_FALSE(ParseOk("program p;"));
}

TEST(CompilationUnitStructure, MissingEndcheckerIsError) {
  EXPECT_FALSE(ParseOk("checker c;"));
}

// §3.1 — Error: mismatched end label.
TEST(CompilationUnitStructure, MismatchedEndLabelIsError) {
  EXPECT_FALSE(ParseOk("module foo; endmodule : bar\n"));
}

// §3.1 — Module with design element name containing underscores and digits.
TEST(CompilationUnitStructure, DesignElementNameWithUnderscoresAndDigits) {
  auto r = Parse("module my_module_123; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_module_123");
}

// §3.1 — Design elements with comments interspersed.
TEST(CompilationUnitStructure, CommentsInterspersedBetweenDesignElements) {
  auto r = Parse(
      "// header comment\n"
      "module m; endmodule\n"
      "/* between */\n"
      "package p; endpackage\n"
      "// trailer\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

// §3.1 — Design elements and CU-scope items interleaved.
TEST(CompilationUnitStructure, DesignElementsAndCuItemsInterleaved) {
  auto r = Parse(
      "function void f1; endfunction\n"
      "module m1; endmodule\n"
      "task t1; endtask\n"
      "package p1; endpackage\n"
      "function void f2; endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->cu_items.size(), 3u);
}

// §3.1 — Large number of modules accumulate correctly.
TEST(CompilationUnitStructure, ManyModulesAccumulate) {
  std::string src;
  for (int i = 0; i < 50; ++i) {
    src += "module m" + std::to_string(i) + "; endmodule\n";
  }
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 50u);
}

TEST(CompilationUnitStructure, TimeunitDeclarationSetsFlag) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
}

TEST(CompilationUnitStructure, TimeprecisionDeclarationSetsFlag) {
  auto r = Parse(
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(CompilationUnitStructure, TimeunitAndTimeprecisionBothSet) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(CompilationUnitStructure, CuScopeLocalparamGoesToCuItems) {
  auto r = Parse(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

TEST(CompilationUnitStructure, ModuleWithEmptyPortListParens) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(CompilationUnitStructure, BindDirectiveGoesToBindDirectives) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "bind target binder b1();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->bind_directives.empty());
}

TEST(CompilationUnitStructure, ConfigWithEndLabel) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(CompilationUnitStructure, PrimitiveWithEndLabel) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(CompilationUnitStructure, MissingEndconfigIsError) {
  EXPECT_FALSE(ParseOk(
      "module m; endmodule\n"
      "config c;\n"
      "  design m;"));
}

TEST(CompilationUnitStructure, MissingEndprimitiveIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"));
}

}  // namespace
