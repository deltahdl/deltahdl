#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationParser, MultipleWildcardPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  child u0(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationParser, MixedPositionalAndNamedPortConnectionsRejected) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(a, .b(b));\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
