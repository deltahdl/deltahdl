#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// §24.6 states that an anonymous program declares its items without
// introducing a new scope. Beyond the members flattening into the surrounding
// compilation-unit list, the parser must not record a program declaration for
// the anonymous program itself: r.cu->programs holds only named programs and
// stays empty here.
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

}  // namespace
