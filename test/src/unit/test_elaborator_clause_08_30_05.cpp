#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefGetIdStaticCallOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj o;\n"
             "    longint id;\n"
             "    o = new();\n"
             "    id = weak_reference#(obj)::get_id(o);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetIdWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    longint id;\n"
             "    id = weak_reference#(obj)::get_id(null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefGetIdInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj o;\n"
             "    o = new();\n"
             "    if (weak_reference#(obj)::get_id(o) != 0)\n"
             "      $display(\"has id\");\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
