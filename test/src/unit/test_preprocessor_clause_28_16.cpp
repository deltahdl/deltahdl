// §28.16: Gate and net delays

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, GateWithParenDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or #(10) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->gate_delay, nullptr);
}

}  // namespace
