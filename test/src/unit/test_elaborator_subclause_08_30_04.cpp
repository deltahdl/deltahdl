#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
