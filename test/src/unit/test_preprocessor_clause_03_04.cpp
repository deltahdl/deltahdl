#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause03, DataAndClassDeclarations) {
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

  EXPECT_TRUE(
      ParseOk("program p1; logic a; endprogram\n"
              "program p2; logic b; endprogram\n"));
}

}  // namespace
