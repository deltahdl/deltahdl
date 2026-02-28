// §24.3: The program construct

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4.1.3 -- Program instantiation
//
// program_instantiation ::=
//   program_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- program_instantiation: basic ---
TEST(ParserAnnexA0413, BasicProgramInst) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- program_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0413, MultipleProgramInstances) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(a)), u1(.clk(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

// Program parameter port list and ports
TEST(SourceText, ProgramParamsAndPorts) {
  auto r = Parse(
      "program prg #(parameter int N = 10)(input logic clk);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

}  // namespace
