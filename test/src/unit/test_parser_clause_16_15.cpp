// §16.15: Disable iff resolution

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// checker_or_generate_item_declaration ::= default disable iff expr ;
TEST(SourceText, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
}

}  // namespace
