#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.5.2 owns no elaboration rule of its own; this observes only that a size()
// call on a dynamic array reaches and passes elaboration. The created-vs-
// uncreated and in-expression variants elaborate identically (elaboration does
// not depend on the runtime creation state), so a single observation suffices.
TEST(DynamicArraySizeValidation, SizeCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int s;\n"
             "  initial s = d.size();\n"
             "endmodule\n"));
}

}  // namespace
