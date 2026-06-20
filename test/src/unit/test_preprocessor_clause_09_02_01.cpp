#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InitialProcedurePreprocessing, MacroExpandsInsideInitialBlock) {
  auto r = ParseWithPreprocessor(
      "`define VAL 42\n"
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = `VAL;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(InitialProcedurePreprocessing, MacroExpandsToInitialBody) {
  auto r = ParseWithPreprocessor(
      "`define INIT_BODY x = 1\n"
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial `INIT_BODY;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
