#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AnonymousProgramParsing, InPackage) {
  auto r = Parse(
      "package p;\n"
      "  program;\n"
      "    task run();\n"
      "    endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AnonymousProgramParsing, InCompilationUnit) {
  auto r = Parse(
      "program;\n"
      "  function void f(); endfunction\n"
      "  class C; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(AnonymousProgramNameSpaceSharing, CompilationUnitItemsIncludeAnonymousMembers) {
  auto r = Parse(
      "task outer_t(); endtask\n"
      "program;\n"
      "  task inner_t(); endtask\n"
      "  function void inner_f(); endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountItemsByKind(r.cu->cu_items, ModuleItemKind::kTaskDecl), 2u);
  EXPECT_EQ(CountItemsByKind(r.cu->cu_items, ModuleItemKind::kFunctionDecl), 1u);
}

}  // namespace
