// §19.6.1.4: Cross bin set expression

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, CrossBodyItem_FunctionDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      function CrossQueueType myFunc(int val);\n"
              "        return '{val};\n"
              "      endfunction\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #32: cross_set_expression
// =============================================================================
TEST(ParserA211, CrossSetExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
