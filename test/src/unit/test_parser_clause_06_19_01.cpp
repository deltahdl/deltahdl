// §6.19.1: Defining new data types as enumerated types

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2TypedefEnumWithBase) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserA213, TypedefEnum) {
  auto r = Parse("module m; typedef enum {A, B, C} abc_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
}

}  // namespace
