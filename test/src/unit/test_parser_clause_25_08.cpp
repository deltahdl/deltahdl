#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceInstantiationGrammar, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

TEST(ParameterizedInterface, WithParameters) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

TEST(ParameterizedInterface, WithConstants) {
  auto r = Parse(
      "interface ifc;\n"
      "  localparam int DEPTH = 16;\n"
      "  parameter int WIDTH = 8;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(
      CountItemsByKind(r.cu->interfaces[0]->items, ModuleItemKind::kParamDecl),
      1u);
}

}  // namespace
