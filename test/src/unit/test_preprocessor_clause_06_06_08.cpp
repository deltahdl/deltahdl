// §6.6.8: Generic interconnect

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// §6.6.8: Generic interconnect
// =========================================================================
TEST(ParserSection6, InterconnectDeclFlag) {
  // §6.6.8: interconnect declares a typeless generic net.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  interconnect ibus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_EQ(item->name, "ibus");
}

}  // namespace
