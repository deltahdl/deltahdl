// Annex A.4.1.4: Checker instantiation

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- ordered_checker_port_connection ---
TEST(ParserAnnexA0414, CheckerInstOrderedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

}  // namespace
