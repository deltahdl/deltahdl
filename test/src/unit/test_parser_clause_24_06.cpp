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

// anonymous_program at file scope (outside package)
TEST(SourceText, AnonymousProgramTopLevel) {
  auto r = Parse(
      "program;\n"
      "  function void f(); endfunction\n"
      "  class C; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
