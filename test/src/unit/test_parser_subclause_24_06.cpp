#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(AnonymousProgramNameSpaceSharing, PackageItemsIncludeAnonymousMembers) {
  auto r = Parse(
      "package p;\n"
      "  task outer_t(); endtask\n"
      "  program;\n"
      "    task inner_t(); endtask\n"
      "    function void inner_f(); endfunction\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  const auto& items = r.cu->packages[0]->items;
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kTaskDecl), 2u);
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kFunctionDecl), 1u);
}

TEST(AnonymousProgramNameSpaceSharing,
     CompilationUnitItemsIncludeAnonymousMembers) {
  auto r = Parse(
      "task outer_t(); endtask\n"
      "program;\n"
      "  task inner_t(); endtask\n"
      "  function void inner_f(); endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountItemsByKind(r.cu->cu_items, ModuleItemKind::kTaskDecl), 2u);
  EXPECT_EQ(CountItemsByKind(r.cu->cu_items, ModuleItemKind::kFunctionDecl),
            1u);
}

TEST(AnonymousProgramNameSpaceSharing,
     CompilationUnitAnonymousProgramDeclaresNoProgramScope) {
  auto r = Parse(
      "program;\n"
      "  task inner_t(); endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_EQ(CountItemsByKind(r.cu->cu_items, ModuleItemKind::kTaskDecl), 1u);
}

TEST(AnonymousProgramPlacement, AnAnonymousProgramInsideAModuleIsRejected) {
  auto r = Parse(
      "module top;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "24.3"));
}

TEST(AnonymousProgramPlacement, AnAnonymousProgramInsideAnInterfaceIsRejected) {
  auto r = Parse(
      "interface I;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "24.3"));
}

TEST(AnonymousProgramPlacement, ANamedProgramInsideAModuleIsAccepted) {
  auto r = Parse(
      "module top;\n"
      "  program p;\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
