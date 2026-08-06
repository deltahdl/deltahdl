#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleHeaderDefinition, ImportInHeaderThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m import pkg::*; (input logic a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
