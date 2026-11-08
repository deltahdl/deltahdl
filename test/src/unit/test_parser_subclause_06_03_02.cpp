#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(NetStrengthParsing, ChargeStrengthAttachedToTrireg) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_NE(item->data_type.charge_strength, 0u);
  EXPECT_EQ(item->name, "cap");
}

TEST(NetStrengthParsing, ChargeStrengthOnNonTriregNetRejected) {
  auto r = Parse(
      "module t;\n"
      "  wire (large) w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

}  // namespace
