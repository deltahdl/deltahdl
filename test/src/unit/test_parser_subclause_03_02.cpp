#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_design.h"

using namespace delta;

namespace {

TEST(AppendCellDeclarations, EveryDesignElementKindReachesTheTarget) {
  auto src = Parse(
      "module m;\n"
      "endmodule\n"
      "program p;\n"
      "endprogram\n"
      "interface i;\n"
      "endinterface\n"
      "checker chk;\n"
      "  logic flag = 0;\n"
      "endchecker\n"
      "package pk;\n"
      "endpackage\n"
      "primitive u(output o, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  EXPECT_EQ(target.modules.size(), 1u);
  EXPECT_EQ(target.programs.size(), 1u);
  EXPECT_EQ(target.interfaces.size(), 1u);
  EXPECT_EQ(target.checkers.size(), 1u);
  EXPECT_EQ(target.packages.size(), 1u);
  EXPECT_EQ(target.udps.size(), 1u);
  EXPECT_EQ(target.configs.size(), 1u);
}

TEST(AppendCellDeclarations, CheckerReachesTheTargetUnderItsOwnName) {
  auto src = Parse(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "endchecker\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  ASSERT_EQ(target.checkers.size(), 1u);
  ASSERT_NE(target.checkers[0], nullptr);
  EXPECT_EQ(target.checkers[0]->name, "chk");
}

TEST(AppendCellDeclarations, CompilationUnitScopeDeclarationsStayBehind) {
  auto src = Parse(
      "typedef int cu_t;\n"
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);
  ASSERT_FALSE(src.cu->classes.empty());
  ASSERT_FALSE(src.cu->cu_items.empty());

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  EXPECT_EQ(target.modules.size(), 1u);
  EXPECT_TRUE(target.classes.empty());
  EXPECT_TRUE(target.cu_items.empty());
}

TEST(AppendCellDeclarations, TargetKeepsWhatItAlreadyHeld) {
  auto first = Parse(
      "module one;\n"
      "endmodule\n");
  auto second = Parse(
      "module two;\n"
      "endmodule\n");
  ASSERT_NE(first.cu, nullptr);
  ASSERT_NE(second.cu, nullptr);

  CompilationUnit target;
  AppendCellDeclarations(target, *first.cu);
  AppendCellDeclarations(target, *second.cu);

  ASSERT_EQ(target.modules.size(), 2u);
  EXPECT_EQ(target.modules[0]->name, "one");
  EXPECT_EQ(target.modules[1]->name, "two");
}

}  // namespace
