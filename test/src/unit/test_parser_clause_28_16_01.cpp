// §28.16.1: min:typ:max delays

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// delay3: mintypmax on gate — #(1:2:3) with min:typ:max expression.
TEST(ParserA223, Delay3GateMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #(1:2:3) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
}

TEST(ParserA301, GateInst_DelayWithMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and #(1:2:3, 4:5:6) a1(out, in1, in2);\n"
              "endmodule\n"));
}

}  // namespace
