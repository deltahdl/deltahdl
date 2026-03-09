#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ProgramTestParse, ProgramInstantiatedInModule) {
  auto* unit = Parse(
      "program test_prog(input logic clk);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  test_prog tp(.clk(clk));\n"
      "endmodule\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  const auto* inst =
      FindItemByKind(unit->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "test_prog");
  EXPECT_EQ(inst->inst_name, "tp");
}

}
