// §18.17.7: Value passing between productions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.12 Randsequence — rs_production
// =============================================================================
// Production with return type: int P : ...;
TEST(ParserA612, RsProductionWithReturnType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      int main : gen;\n"
      "      gen : { return 42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Production with port list: P(int x) : ...;
TEST(ParserA612, RsProductionWithPorts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(5);\n"
      "      void gen(int x) : { $display(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_production_item
// =============================================================================
// Production item with arguments
TEST(ParserA612, RsProductionItemWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : gen(1, 2);\n"
      "      void gen(int a, int b) : { $display(a + b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
