#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.19.5: an enumeration has the built-in methods §6.19.5.1 to §6.19.5.6 list
// and no others, nor any member, so a call or select naming anything else
// through an enumeration variable is reported, its type written as a typedef
// name or in the declaration itself.
TEST(EnumMethodElaboration, NameNoEnumMethodIsReported) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  e_t e;\n"
      "  enum {C, D} f;\n"
      "  initial begin\n"
      "    e.foo();\n"
      "    e.h.run();\n"
      "    f.bar();\n"
      "    e.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the enumeration 'e'", 6,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the enumeration 'e'", 7,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the enumeration 'f'", 8,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'rand_mode' is not a built-in method of the enumeration 'e'", 9,
      "6.19.5"));
}

TEST(EnumMethodElaboration, EveryEnumMethodIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {A, B, C} e_t;\n"
             "  e_t e;\n"
             "  int n;\n"
             "  string s;\n"
             "  initial begin\n"
             "    e = e.first();\n"
             "    e = e.last();\n"
             "    e = e.next();\n"
             "    e = e.prev(2);\n"
             "    n = e.num();\n"
             "    s = e.name();\n"
             "  end\n"
             "endmodule\n"));
}

// §18.8: a random property of a class, an enumeration among them, is named in
// a call of its rand_mode by a method of the class.
TEST(EnumMethodElaboration, RandModeOfAnEnumPropertyIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class K;\n"
             "  rand enum {A, B} e;\n"
             "  function void hold();\n"
             "    e.rand_mode(0);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §23.2.2: a port that is an enumeration is an enumeration variable of the
// module.
TEST(EnumMethodElaboration, PortsAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m(input enum {A, B} e);\n"
      "  initial e.foo();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'foo' is not a built-in method of the enumeration 'e'", 2, "6.19.5"));
}

}  // namespace
