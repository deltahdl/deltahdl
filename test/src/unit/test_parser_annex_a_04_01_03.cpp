// Annex A.4.1.3: Program instantiation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- program_instantiation: with parameter_value_assignment (ordered) ---
TEST(ParserAnnexA0413, ProgramInstWithOrderedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(16) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

}  // namespace
