#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ParameterizedInterface, WithParameters) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

TEST(ParameterizedInterface, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

}  // namespace
