#include "fixture_elaborator.h"

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

}  // namespace
