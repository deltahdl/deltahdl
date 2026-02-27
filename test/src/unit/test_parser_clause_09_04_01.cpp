// §9.4.1: Delay control

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// Statement delay: #delay_value in procedural context.
TEST(ParserA223, DelayValueInStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #10 $display(\"hello\");\n"
              "endmodule"));
}

}  // namespace
