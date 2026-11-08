#include <gtest/gtest.h>

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

TEST(ClassConstraintElaboration, WeakRefGetIdDerivedHandleArgOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "class ex_obj extends obj;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    ex_obj my_obj;\n"
             "    longint id;\n"
             "    my_obj = new();\n"
             "    id = weak_reference#(obj)::get_id(my_obj);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
