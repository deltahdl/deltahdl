#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §21.2.1.1 (printed page 656): "It shall be an error if an undefined format
// specifier appears in a string literal argument." The literal is in the
// source, so the misuse is reported where the call is parsed, citing the
// subclause. `%q` printed a note on stderr and then itself, and the run went
// on.
TEST(FormatSpecifications, UndefinedSpecifierInADisplayLiteralIsAnError) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"%q\", 5);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "undefined format specifier '%q' in a string literal argument",
      2, "21.2.1.1"));
}

// §21.2.1.1: every string literal argument of a display task is a format, as
// are those of the write, strobe and monitor tasks, their file forms, the
// $swrite family and the severity tasks (§20.10); $sformat's format is its
// second argument and $sformatf's its first (§21.3.3). An undefined letter in
// any of them is an error, uppercase too.
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

// §21.2.1.2 (printed page 659): the field width between the % and an integer
// specifier's letter is a non-negative decimal integer constant, and only
// Table 21-2's real specifiers take C's flags (printed page 658), so `%-3d` is
// a specifier neither table defines, which §21.2.1.1 makes an error. It was
// warned about as a malformed field width alone.
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

// §21.2.1.1 with Table 21-1 and Table 21-2: each defined specifier in either
// case, with the field width §21.2.1.2 allows, a real specifier's precision and
// the C flags a real specifier takes (printed page 658), and `%%`, are all
// accepted. So are the string literal arguments $sformat does not read as its
// format, and a `%` ending the literal.
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
