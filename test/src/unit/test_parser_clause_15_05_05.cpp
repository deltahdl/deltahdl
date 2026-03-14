#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.5.5: Event declaration with initializer from another event parses.
TEST(EventOperationsParser, EventInitializerFromAnotherEvent) {
  auto r = Parse(
      "module m;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item0 = r.cu->modules[0]->items[0];
  auto* item1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(item0->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item1->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item1->name, "done_too");
  EXPECT_NE(item1->init_expr, nullptr);
}

// §15.5.5: Imperative event-to-event assignment parses as blocking assign.
TEST(EventOperationsParser, ImperativeEventAssignment) {
  auto r = Parse(
      "module m;\n"
      "  event a, b;\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

}  // namespace
