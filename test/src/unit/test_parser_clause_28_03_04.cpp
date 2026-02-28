// §28.3.4: The primitive instance identifier

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(ParserA301, GateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

}  // namespace
