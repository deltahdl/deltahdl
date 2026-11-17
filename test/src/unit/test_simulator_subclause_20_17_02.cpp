#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Stacktrace, TaskFormDisplaysNestedCallStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  task inner; $stacktrace; endtask\n"
      "  task outer; inner; endtask\n"
      "  initial outer;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "inner\nouter\n");
}

TEST(Stacktrace, TaskFormAtTopLevelDisplaysEmptyStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $stacktrace;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

TEST(Stacktrace, FunctionFormReturnsCallStackStringForLaterProcessing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  task inner; trace = $stacktrace; endtask\n"
      "  task outer; inner; endtask\n"
      "  initial begin\n"
      "    outer;\n"
      "    $display(\"%s\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "inner\nouter\n");
}

TEST(Stacktrace, FunctionFormAtTopLevelReturnsEmptyString) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  initial begin\n"
      "    trace = $stacktrace;\n"
      "    $display(\"[%s]\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
}

TEST(Stacktrace, MixedFunctionInsideTaskReportsBothFrames) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace;\n"
      "  int unused;\n"
      "  function int probe();\n"
      "    trace = $stacktrace;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  task outer; unused = probe(); endtask\n"
      "  initial begin\n"
      "    outer;\n"
      "    $display(\"%s\", trace);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "probe\nouter\n");
}

TEST(Stacktrace, FunctionFormAsDeclarationInitializerCapturesContext) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string trace = $stacktrace;\n"
      "  initial $display(\"[%s]\", trace);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[]\n");
}

TEST(Stacktrace, TaskAndFunctionFormsAgreeFromSameFrame) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  task probe;\n"
      "    $stacktrace;\n"
      "    $display(\"%s\", $stacktrace);\n"
      "  endtask\n"
      "  initial probe;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "probe\nprobe\n");
}

TEST(Stacktrace, TaskFormInFunctionBodyDisplaysCallStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function void probe;\n"
      "    $stacktrace;\n"
      "  endfunction\n"
      "  initial probe();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "probe\n");
}

TEST(Stacktrace, DISABLED_TheFunctionFormIsAString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial $display(\"%s\", $typename($stacktrace));\n"
                       "endmodule\n",
                       f),
            "string\n");
}

TEST(Stacktrace, TheFunctionFormConcatenatesAsAString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string trace;\n"
                       "  task inner; trace = {$stacktrace, \"|\"}; endtask\n"
                       "  task outer; inner; endtask\n"
                       "  initial begin\n"
                       "    outer;\n"
                       "    $display(\"%s\", trace);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "inner\nouter|\n");
}

TEST(Stacktrace, DISABLED_AClassMethodFrameIsInTheStack) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    static function string cls_trace();\n"
      "      return $stacktrace;\n"
      "    endfunction\n"
      "  endclass\n"
      "  initial $display(\"%s\", C::cls_trace());\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("cls_trace"), std::string::npos) << out;
}

TEST(Stacktrace, APackageFunctionFrameIsInTheStack) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  function string pkg_trace();\n"
      "    return $stacktrace;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  initial $display(\"%s\", pk::pkg_trace());\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("pkg_trace"), std::string::npos) << out;
}

TEST(Stacktrace, AProgramTaskFrameIsInTheStack) {
  SimFixture f;
  std::string out = RunCapture(
      "program p;\n"
      "  task prog_trace;\n"
      "    $stacktrace;\n"
      "  endtask\n"
      "  initial prog_trace;\n"
      "endprogram\n"
      "module t;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("prog_trace"), std::string::npos) << out;
}

TEST(Stacktrace, AnInterfaceFunctionFrameIsInTheStack) {
  SimFixture f;
  std::string out = RunCapture(
      "interface i;\n"
      "  function string intf_trace();\n"
      "    return $stacktrace;\n"
      "  endfunction\n"
      "endinterface\n"
      "module t;\n"
      "  i u();\n"
      "  initial $display(\"%s\", u.intf_trace());\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("intf_trace"), std::string::npos) << out;
}

}  // namespace
