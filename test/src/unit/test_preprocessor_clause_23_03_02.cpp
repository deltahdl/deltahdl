// §23.3.2: Module instantiation syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.3 Design element instantiations
TEST(ParserClause03, Cl3_3_DesignElementInstantiations) {
  auto r = ParseWithPreprocessor(
      "module child; endmodule\n"
      "module top;\n"
      "  logic sig;\n"
      "  child c0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // "top" is modules[1]; check it has the instantiation.
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

}  // namespace
