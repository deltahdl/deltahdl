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

// --- Pass/enable switch error for wrong strength/delay combinations ---
TEST(PassSwitches, DelayNotAllowed) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassSwitches, RtranDelayNotAllowed) {
  auto r = Parse(
      "module m;\n"
      "  rtran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
