#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssignmentParsing, NetDeclAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->name, "a");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(AssignmentParsing, NetDeclAssignmentVector) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire [7:0] w = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
