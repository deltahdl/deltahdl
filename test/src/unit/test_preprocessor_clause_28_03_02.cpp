// §28.3.2: The drive strength specification

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, StrengthWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4);  // strong0
  EXPECT_EQ(item->drive_strength1, 4);  // strong1
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

}  // namespace
