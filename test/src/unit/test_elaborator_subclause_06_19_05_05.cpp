// Tests for §6.19.5.5 "Num()", whose whole text is the prototype "function int
// num();" and the sentence "The num() method returns the number of elements in
// the given enumeration." It states no restriction a design can violate, so the
// rejection below is reported under §6.19.3.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.19.5.5 owns no elaborator rule of its own (its normative claims are the
// simulator-stage member-count and int-width behavior). This is a single
// acceptance smoke test that a num() call elaborates; the enum member count
// does not affect elaboration, so no second count-varied case is kept here.
TEST(EnumMethods, NumElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

// §6.19.5.5 declares num() as `function int num()`, which is what separates it
// from the navigation methods of §6.19.5.1 through §6.19.5.4: those return the
// enumeration type, this one returns int. §6.19.3 therefore still requires a
// cast to put a num() result in an enum variable, and the declaration is in
// error without one. This is the control on accepting the navigation methods
// there: an elaborator that waved through any method result would pass the
// cases that accept first/last/next/prev and this one too.
TEST(EnumMethods, NumResultStillNeedsACastToInitializeAnEnumVar) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c = c.num();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
}

}  // namespace
