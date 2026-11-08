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

}  // namespace
