// §23.2.2.1: Non-ANSI style port declarations

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Module with non-ANSI header (list_of_ports).
TEST(SourceText, ModuleNonAnsiHeader) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

}  // namespace
