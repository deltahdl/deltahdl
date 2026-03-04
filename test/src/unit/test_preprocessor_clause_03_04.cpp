// §3.4: Programs

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.4:
TEST(ParserClause03, Cl3_4_DataAndClassDeclarations) {
  auto r = ParseWithPreprocessor(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  class my_trans; int data; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->programs[0]->items.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kClassDecl));
  // §3.4: Multiple programs each create separate scopes
  EXPECT_TRUE(
      ParseOk("program p1; logic a; endprogram\n"
              "program p2; logic b; endprogram\n"));
}

}  // namespace
