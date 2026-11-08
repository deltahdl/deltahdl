#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakRefNewWithReferentOk) {
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
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefNewWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(obj) wr;\n"
             "    wr = new(null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakRefTwoInstancesSameReferentOk) {
  EXPECT_TRUE(
      ElabOk("class obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    obj strong_obj;\n"
             "    weak_reference #(obj) wref1, wref2;\n"
             "    strong_obj = new();\n"
             "    wref1 = new(strong_obj);\n"
             "    wref2 = new(strong_obj);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
