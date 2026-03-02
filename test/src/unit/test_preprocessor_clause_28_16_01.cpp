// §28.16.1: min:typ:max delays

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, GateMinTypMaxDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1(io1, io2, dir);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

}  // namespace
