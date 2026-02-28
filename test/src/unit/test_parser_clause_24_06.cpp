// §24.6: Program-wide space and anonymous programs

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// anonymous_program: program ; { ... } endprogram
TEST(SourceText, AnonymousProgram) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

}  // namespace
