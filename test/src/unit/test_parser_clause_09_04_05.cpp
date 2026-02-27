// §9.4.5: Intra-assignment timing controls

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// Intra-assignment delay: var = #delay expr.
TEST(ParserA223, IntraAssignmentDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg r;\n"
              "  initial r = #5 1'b1;\n"
              "endmodule"));
}

}  // namespace
