// §23.10.2.1: Parameter value assignment by ordered list

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A4ModuleInstWithParams) {
  auto r = Parse("module m; sub #(8, 4) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
}

TEST(ParserAnnexA0411, OrderedParamsNamedPorts) {
  auto r = Parse("module m; sub #(8) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_ports.size(), 1u);
}

}  // namespace
