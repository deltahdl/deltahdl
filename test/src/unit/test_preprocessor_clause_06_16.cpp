// §6.16: String data type

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, AssignCompatibleStringLiteral) {
  auto r = ParseWithPreprocessor("module m;\n"
                                 "  string s;\n"
                                 "  initial s = \"hello\";\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// =========================================================================
// §6.16: String data type
// =========================================================================
TEST(ParserSection6, StringDeclModule) {
  // §6.16: String data type is a dynamic ordered collection of characters.
  auto r = ParseWithPreprocessor("module t;\n"
                                 "  string name;\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(item->name, "name");
}

TEST(ParserSection6, StringDeclWithInit) {
  // §6.16: String variable with initializer.
  auto r = ParseWithPreprocessor("module t;\n"
                                 "  string msg = \"hello\";\n"
                                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  ASSERT_NE(item->init_expr, nullptr);
}

} // namespace
