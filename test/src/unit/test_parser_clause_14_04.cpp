// §14.4: Input and output skews

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// delay_value: 1step — special keyword in clocking context.
TEST(ParserA223, DelayValue1step) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input #1step data;\n"
              "  endclocking\n"
              "endmodule"));
}

}  // namespace
