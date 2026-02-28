// Annex A.4.1.1: Module instantiation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA0411, OrderedParameterAssignment) {
  auto r = Parse("module m; sub #(8, 4) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);
  // Ordered params have empty name
  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_params[1].first, "");
}

TEST(ParserAnnexA0411, NamedParameterAssignment) {
  // . parameter_identifier ( [ param_expression ] )
  auto r = Parse("module m; sub #(.WIDTH(8), .DEPTH(4)) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_NE(item->inst_params[0].second, nullptr);
  EXPECT_EQ(item->inst_params[1].first, "DEPTH");
  EXPECT_NE(item->inst_params[1].second, nullptr);
}

}  // namespace
