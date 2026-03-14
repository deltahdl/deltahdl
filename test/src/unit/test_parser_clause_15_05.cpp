#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §15.5: A single event declaration parses as a variable with kEvent type.
TEST(NamedEventParser, SingleEventDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  event done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item->name, "done");
}

// §15.5: Multiple event declarations in a module.
TEST(NamedEventParser, MultipleEventDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  event done;\n"
      "  event blast;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item0 = r.cu->modules[0]->items[0];
  auto* item1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(item0->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item0->name, "done");
  EXPECT_EQ(item1->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item1->name, "blast");
}

// §15.5: Event assigned null parses.
TEST(NamedEventParser, EventAssignedNull) {
  auto r = Parse(
      "module m;\n"
      "  event empty = null;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(item->init_expr, nullptr);
}

// §15.5: Event declaration inside an initial block.
TEST(NamedEventParser, EventInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
