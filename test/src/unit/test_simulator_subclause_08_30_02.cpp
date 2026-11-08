#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakRefE2eNewRecordsReferentProcedural) {
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
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eNewRecordsReferentDeclInit) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static obj strong_obj = new();\n"
                      "    static weak_reference #(obj) wr = new(strong_obj);\n"
                      "    result = (wr.get() == strong_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eNewNullReferentGetsNull) {
  EXPECT_EQ(RunAndGet("class obj;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    weak_reference #(obj) wr;\n"
                      "    wr = new(null);\n"
                      "    result = (wr.get() == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassSim, WeakRefE2eNewNullNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    weak_reference #(obj) wr;\n"
      "    wr = new(null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(ClassSim, WeakRefE2eNewNullReferentDeclInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static weak_reference #(obj) wr = new(null);\n"
      "    result = (wr.get() == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 1u}});
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(ClassSim, WeakRefE2eInstancesUniqueButSameReferent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class obj;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  int distinct;\n"
      "  int same_referent;\n"
      "  initial begin\n"
      "    obj strong_obj;\n"
      "    weak_reference #(obj) wref1, wref2;\n"
      "    strong_obj = new();\n"
      "    wref1 = new(strong_obj);\n"
      "    wref2 = new(strong_obj);\n"
      "    distinct = (wref1 != wref2);\n"
      "    same_referent = (wref1.get() == wref2.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"distinct", 1u}, {"same_referent", 1u}});
}

TEST(ClassSim, WeakRefE2eModuleScopeDeclaratorListRunsEveryMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "class obj; int v = 9; endclass\n"
      "class ex_obj extends obj; endclass\n"
      "module t;\n"
      "  obj strong_obj, got;\n"
      "  weak_reference#(obj) wref1, wref2;\n"
      "  initial begin\n"
      "    strong_obj = new;\n"
      "    wref1 = new(strong_obj); wref2 = new(strong_obj);\n"
      "    $display(\"neq %0d\", wref1 != wref2);\n"
      "    $display(\"same %0d\", wref1.get() == wref2.get());\n"
      "    got = wref1.get();\n"
      "    $display(\"v %0d\", got.v);\n"
      "    wref1.clear();\n"
      "    $display(\"cleared %0d\", wref1.get() == null);\n"
      "    $display(\"id0 %0d\", weak_reference#(obj)::get_id(null));\n"
      "    $display(\"idsame %0d\", weak_reference#(obj)::get_id(strong_obj) "
      "== weak_reference#(ex_obj)::get_id(strong_obj));\n"
      "    $display(\"idnz %0d\", weak_reference#(obj)::get_id(strong_obj) "
      "!= 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "neq 1\nsame 1\nv 9\ncleared 1\nid0 0\nidsame 1\nidnz 1\n");
}

}  // namespace
