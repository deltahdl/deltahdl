// Non-LRM tests

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

namespace {

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// Clocking block with assertion_item_declaration elaborates
TEST(ElabA611, AssertionItemDeclElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
