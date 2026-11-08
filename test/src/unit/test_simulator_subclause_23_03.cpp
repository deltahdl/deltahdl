#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ModuleInstanceStorage, ChildArrayElementsAreReachedByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  int b[5];\n"
                       "  logic [7:0] pk[4];\n"
                       "  initial begin b[2] = 8; pk[1] = 5; end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child u();\n"
                       "  initial begin\n"
                       "    #1 $display(\"%0d %0d\", u.b[2], u.pk[1]);\n"
                       "    u.b[3] = 9;\n"
                       "    #1 $display(\"%0d\", u.b[3]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "8 5\n9\n");
}

TEST(ModuleInstanceStorage, ClassDeclaredInAnInstantiatedModuleIsItsType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module u;\n"
                 "  int cnt = 17;\n"
                 "  class C;\n"
                 "    int p = 5;\n"
                 "    static int s = 3;\n"
                 "    function int get(); return top.u.cnt; endfunction\n"
                 "    function int getp(); return p; endfunction\n"
                 "    task set(int v); top.u.cnt = v; endtask\n"
                 "  endclass\n"
                 "  C h = new;\n"
                 "  initial $display(\"%0d %0d\", h.p, h.get());\n"
                 "endmodule\n"
                 "module top;\n"
                 "  u u();\n"
                 "  initial begin\n"
                 "    #1 $display(\"%0d %0d %0d %0d\", u.h.p, u.h.getp(), "
                 "u.h.s, u.h.get());\n"
                 "    u.h.set(23);\n"
                 "    $display(\"%0d\", u.cnt);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5 17\n5 5 3 17\n23\n");
}

}  // namespace
