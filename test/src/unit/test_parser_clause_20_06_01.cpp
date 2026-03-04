// §20.6.1: Type name function

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §20.6 — Bare type keyword in expression context ($typename(logic))
TEST(ParserSection6, BareTypeKeywordInExpr) {
  auto r = Parse("module t;\n"
                 "  initial $display($typename(logic));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

} // namespace
