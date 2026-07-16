#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.30.4: the void clear() call elaborates cleanly. The referent value and any
// following get() do not exercise a distinct elaborator path for clear(), so a
// single accepting form covers elaboration of the clear() call.
TEST(ClassConstraintElaboration, WeakRefClearCallOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj strong_obj;\n"
             "    weak_reference #(obj) wr;\n"
             "    strong_obj = new();\n"
             "    wr = new(strong_obj);\n"
             "    wr.clear();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
