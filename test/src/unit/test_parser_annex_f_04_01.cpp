#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §F.4.1: nested property instances in a body must be captured so the
// rewriter knows what to flatten in.
TEST(PropertyInstanceParsing, NestedPropertyInstanceCaptured) {
  auto r = Parse(
      "module m;\n"
      "  property leaf(x);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf(a);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* root = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl && item->name == "root") {
      root = item;
      break;
    }
  }
  ASSERT_NE(root, nullptr);
  bool captured = false;
  for (auto ref : root->prop_instance_refs) {
    if (ref == "leaf") captured = true;
  }
  EXPECT_TRUE(captured);
}

// §F.4.1 step 2 needs the callee's formals to substitute actual arguments.
TEST(PropertyInstanceParsing, FormalArgsCapturedForRewrite) {
  auto r = Parse(
      "module m;\n"
      "  property leaf(x, y);\n"
      "    @(posedge clk) x |-> y;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* leaf = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->prop_formals.size(), 2u);
}

}  // namespace
