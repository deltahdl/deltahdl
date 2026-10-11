// §6.18 "User-defined types": a typedef writing unpacked dimensions after its
// name declares an unpacked array type (§7.4), so a variable declared with it
// is an array whose elements are of the type the typedef is written on.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// An array of strings, enumerations or class handles declared through such a
// typedef has the array methods (§7.5, §7.12), not its element's, and its
// element, one select in, has its element type's alone.
TEST(UserDefinedTypeElaboration, TypedefArrayIsNoElementForMemberChecks) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "module m;\n"
      "  typedef string sa_t [2];\n"
      "  typedef enum {A, B} ea_t [2];\n"
      "  typedef C ca_t [2];\n"
      "  sa_t s;\n"
      "  ea_t e;\n"
      "  ca_t c;\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = s.size();\n"
      "    n = e.size();\n"
      "    n = c.size();\n"
      "    s[0].foo();\n"
      "    e[1].bar();\n"
      "    c[0].baz();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 's'", 14, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the enumeration 'e'", 15,
      "6.19.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'C' has no member named 'baz'", 16, "8.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
