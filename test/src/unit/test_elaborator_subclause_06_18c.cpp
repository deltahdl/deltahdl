#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeElaboration, TypedefArrayIsNoElementForMemberChecks) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  typedef string sa_t [2];\n"
      "  typedef enum {A, B} e_t;\n"
      "  typedef e_t ea_t [2];\n"
      "  initial begin\n"
      "    sa_t s;\n"
      "    ea_t e;\n"
      "    s.reverse();\n"
      "    e.reverse();\n"
      "    s[0].foo();\n"
      "    e[1].bar();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the string 's'", 10, "6.16"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the enumeration 'e'", 11,
      "6.19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(UserDefinedTypeElaboration, ClassTypedefArrayIsAnArrayOfHandles) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "module m;\n"
      "  typedef C ca_t [2];\n"
      "  ca_t c;\n"
      "  initial begin\n"
      "    c.reverse();\n"
      "    c[0].baz();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' has no member named 'baz'", 7, "8.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
