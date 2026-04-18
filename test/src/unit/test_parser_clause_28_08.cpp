// §28.8

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PassSwitches, SingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, TooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(a, b, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a1, b1, en), t2(a2, b2, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

}  // namespace
