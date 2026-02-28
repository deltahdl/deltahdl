// §23.3.2.4: Connecting module instances using wildcard named port connections ( .*)

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA0411, WildcardPortConnection) {
  // . * — wildcard port connection
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

}  // namespace
