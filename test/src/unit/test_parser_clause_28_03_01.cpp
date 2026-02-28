// §28.3.1: The gate type specification

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_EnableWithStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (weak0, weak1) #7 b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
  EXPECT_NE(g->gate_delay, nullptr);
}

}  // namespace
