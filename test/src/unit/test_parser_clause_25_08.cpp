#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Section 25.8 defines no grammar of its own; the parameter-port-list and
// parameter-value-assignment grammar belong to 25.3 / 6.20 / 23.10.2. These
// two tests are minimal observers of the surface the 25.8 worked example
// exercises: an interface *declaration* carries a parameter port list (the AST
// places it under cu->interfaces, distinct from a module), and an interface
// *instance* carries a named override (matching simple_bus #(.DWIDTH(16))).
// Override mechanics, type parameters, multiplicity and the duplicate/mixed
// error cases live with 6.20 / 23.10.2 / 23.10.2.2.

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

}
