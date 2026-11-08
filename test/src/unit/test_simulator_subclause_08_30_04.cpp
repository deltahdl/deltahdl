#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefE2eClearSetsGetToNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearFlipsGetFromReferentToNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  int before_val;\n"
                      "  int after_val;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    before_val = (wr.get() == strong_obj);\n"
                      "    wr.clear();\n"
                      "    after_val = (wr.get() == null);\n"
                      "    result = before_val & after_val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearSetsGetToNullDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static obj strong_obj = new();\n"
                      "    static weak_reference #(obj) wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearOnNullInitSafe) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    weak_reference #(obj) wr;\n"
                      "    wr = new(null);\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearIdempotent) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    wr.clear();\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearDoesNotAffectOtherWeakRefs) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  int first_cleared;\n"
                      "  int second_intact;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wref1;\n"
                      "    weak_reference #(obj) wref2;\n"
                      "    strong_obj = new();\n"
                      "    wref1 = new(strong_obj);\n"
                      "    wref2 = new(strong_obj);\n"
                      "    wref1.clear();\n"
                      "    first_cleared = (wref1.get() == null);\n"
                      "    second_intact = (wref2.get() == strong_obj);\n"
                      "    result = first_cleared & second_intact;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eClearDoesNotAffectReferent) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    obj strong_obj;\n"
                      "    weak_reference #(obj) wr;\n"
                      "    strong_obj = new();\n"
                      "    strong_obj.x = 99;\n"
                      "    wr = new(strong_obj);\n"
                      "    wr.clear();\n"
                      "    result = strong_obj.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

}  // namespace
