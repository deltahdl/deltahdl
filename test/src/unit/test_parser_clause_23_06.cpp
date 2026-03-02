// §23.6: Hierarchical names

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 19. Hierarchical reference syntax (a.b.c)
TEST(ParserClause03, Cl3_13_HierarchicalReferenceSyntax) {
  // Hierarchical names like top.sub.sig are member-access expressions.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
