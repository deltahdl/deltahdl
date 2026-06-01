// Canonical parser tests for §6.3.2 "Strengths".
//
// §6.3.2 restricts charge strength to trireg nets. The parser is where this
// gating is first applied: a parenthesized charge keyword is only consumed as a
// charge strength when the declared net is a trireg, so on any other net type
// the same syntax is refused. This file observes that gating directly on the
// parsed declaration. The charge keyword set and default belong to the
// descendant subclause §6.3.2.1, and the drive-strength rule is observed at the
// elaborator stage.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §6.3.2: a charge strength is accepted on a trireg net, and the parser records
// it on the declared net's data type.
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

// §6.3.2: charge strength shall only be used on a trireg, so the parser refuses
// to read the same parenthesized keyword as a charge strength for another net
// type, leaving it as a syntax error.
TEST(NetStrengthParsing, ChargeStrengthOnNonTriregNetRejected) {
  auto r = Parse(
      "module t;\n"
      "  wire (large) w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
