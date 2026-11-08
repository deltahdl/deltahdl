#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OptionMembers, NameTheStructureDoesNotDeclareIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.foo = 1;\n"
      "    option.strobe = 1;\n"
      "    type_option.at_least = 2;\n"
      "    option.at_least = 2;\n"
      "    type_option.strobe = 1;\n"
      "    coverpoint a { option.bar = 1; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.baz = 2;\n"
      "  initial cg::type_option.qux = 3;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'foo'",
                            4, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "option has no member 'strobe'", 5, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type_option has no member 'at_least'", 6,
                            "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'bar'",
                            9, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'baz'",
                            12, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type_option has no member 'qux'", 13, "19.10"));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

}  // namespace
