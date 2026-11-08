#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FormatSpecifications, UndefinedSpecifierInADisplayLiteralIsAnError) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"%q\", 5);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "undefined format specifier '%q' in a string literal argument",
      2, "21.2.1.1"));
}

TEST(FormatSpecifications, UndefinedSpecifierIsAnErrorInEveryFormatTask) {
  for (const char* call :
       {"$display(\"a %0d\", 1, \" %Q\", 2)", "$write(\"%y\", 1)",
        "$strobeh(\"%j\", 1)", "$monitor(\"%k\", v)", "$fdisplay(1, \"%n\", 1)",
        "$swrite(s, \"%r\", 1)", "$sformat(s, \"%w\", 1)",
        "s = $sformatf(\"%a\", 1)", "$error(\"%i\", 1)",
        "$fatal(1, \"%-3y\", 1)"}) {
    auto r = Parse(std::string("module t;\n"
                               "  string s; int v;\n"
                               "  initial ") +
                   call +
                   ";\n"
                   "endmodule\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "undefined format specifier", 3, "21.2.1.1"))
        << call;
  }
}

TEST(FormatSpecifications, FlaggedIntegerSpecifierIsAnError) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial $display(\"%-3d\", v);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "undefined format specifier '%-3d' in a string "
                            "literal argument of $display",
                            3, "21.2.1.1"));
}

TEST(FormatSpecifications, DefinedSpecifiersAreAccepted) {
  auto r = Parse(
      "module t;\n"
      "  string s; real x; int v;\n"
      "  initial begin\n"
      "    $display(\"%h %x %d %o %b %c %l %v %m %p %s %t %u %z %e %f %g\",\n"
      "             v, v, v, v, v, v, v, v, s, v, v, v, x, x, x);\n"
      "    $display(\"%H %X %D %O %B %C %L %M %S %T %E %F %G\",\n"
      "             v, v, v, v, v, v, s, v, x, x, x);\n"
      "    $display(\"%0d %5d %10.3f %.2e %% 100%\", v, v, x, x);\n"
      "    $display(\"%-10.3f|%+e|%#g|% f|%05.1f\", x, x, x, x, x);\n"
      "    $sformat(s, \"%d\", \"%q\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
