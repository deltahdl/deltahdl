#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AssignmentPatternFormat,
     DISABLED_AFixedArrayPropertyPrintsInsideItsOwnMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[2];\n"
                       "    function void show();\n"
                       "      a = '{1, 2};\n"
                       "      $display(\"%p\", a);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial h.show();\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat, AFixedArrayPropertyPrintsThroughAHandle) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[2];\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.a = '{1, 2};\n"
                       "    $display(\"%p\", h.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_ADynamicArrayPropertyPrintsInsideItsOwnMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[];\n"
                       "    function void show();\n"
                       "      a = '{1, 2};\n"
                       "      $display(\"%p\", a);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial h.show();\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat, ADynamicArrayPropertyPrintsThroughAHandle) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[];\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.a = '{1, 2};\n"
                       "    $display(\"%p\", h.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_AQueueArrayPropertyPrintsInsideItsOwnMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[$];\n"
                       "    function void show();\n"
                       "      a = {1, 2};\n"
                       "      $display(\"%p\", a);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial h.show();\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat, AQueueArrayPropertyPrintsThroughAHandle) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    int a[$];\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.a = {1, 2};\n"
                       "    $display(\"%p\", h.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{1, 2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_ATypedAssignmentPatternPrintsAsAPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial $display(\"%p\", s_t'{1, 2});\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_ATypedAssignmentPatternPrintsAsAPatternThroughSformatfAndWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial begin\n"
                       "    $write(\"%p|\", s_t'{1, 2});\n"
                       "    $display(\"%s\", $sformatf(\"%p\", s_t'{1, 2}));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}|'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat, DISABLED_ACastPrintsAsAPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial $display(\"%p\", s_t'(v));\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_ACastPrintsAsAPatternThroughSformatfAndWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial begin\n"
                       "    $write(\"%p|\", s_t'(v));\n"
                       "    $display(\"%s\", $sformatf(\"%p\", s_t'(v)));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}|'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat, DISABLED_AFunctionCallPrintsAsAPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial $display(\"%p\", mk());\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_AFunctionCallPrintsAsAPatternThroughSformatfAndWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial begin\n"
                       "    $write(\"%p|\", mk());\n"
                       "    $display(\"%s\", $sformatf(\"%p\", mk()));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}|'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat, DISABLED_AConditionalPrintsAsAPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int a; int b;} s_t;\n"
                       "  function s_t mk();\n"
                       "    return '{1, 2};\n"
                       "  endfunction\n"
                       "  s_t v = '{1, 2};\n"
                       "  bit c = 1;\n"
                       "  initial $display(\"%p\", c ? v : mk());\n"
                       "endmodule\n",
                       f),
            "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_AConditionalPrintsAsAPatternThroughSformatfAndWrite) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct {int a; int b;} s_t;\n"
                 "  function s_t mk();\n"
                 "    return '{1, 2};\n"
                 "  endfunction\n"
                 "  s_t v = '{1, 2};\n"
                 "  bit c = 1;\n"
                 "  initial begin\n"
                 "    $write(\"%p|\", c ? v : mk());\n"
                 "    $display(\"%s\", $sformatf(\"%p\", c ? v : mk()));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "'{a:1, b:2}|'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat,
     DISABLED_AnExpressionAggregatePrintsAsAPatternThroughFdisplay) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t21020106b_fdisplay.txt";
  RunCapture(
      "module t;\n"
      "  typedef struct {int a; int b;} s_t;\n"
      "  function s_t mk();\n"
      "    return '{1, 2};\n"
      "  endfunction\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          path +
          "\", \"w\");\n"
          "    $fdisplay(fd, \"%p\", mk());\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  std::ifstream ifs(path);
  std::string text((std::istreambuf_iterator<char>(ifs)),
                   std::istreambuf_iterator<char>());
  std::remove(path.c_str());
  EXPECT_EQ(text, "'{a:1, b:2}\n");
}

TEST(AssignmentPatternFormat, AnUnpackedUntaggedUnionPrintsItsFirstMember) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  union { int a; shortint b; } u;\n"
                       "  initial begin\n"
                       "    u.a = 7;\n"
                       "    $display(\"%p\", u);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{a:7}\n");
}

TEST(AssignmentPatternFormat, DISABLED_APackedUnionPrintsUnformatted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  union packed { byte a; byte b; } u;\n"
                       "  initial begin\n"
                       "    u.a = 8'd5;\n"
                       "    $display(\"%p\", u);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(AssignmentPatternFormat,
     OutputOverTheLimitIsWholeOrTruncatedWithAWarning) {
  for (const char* spec : {"%p", "%0p"}) {
    SimFixture f;
    std::string out =
        RunCapture(std::string("module t;\n"
                               "  int a[400];\n"
                               "  initial begin\n"
                               "    foreach (a[i]) a[i] = 1000000 + i;\n"
                               "    $display(\"") +
                       spec +
                       "\", a);\n"
                       "  end\n"
                       "endmodule\n",
                   f);
    bool whole = out.find("1000399") != std::string::npos;
    bool truncated = out.size() >= 1024 && f.diag.WarningCount() > 0;
    EXPECT_TRUE(whole || truncated) << spec << " " << out.size();
    EXPECT_GT(out.size(), 1024u) << spec;
  }
}

TEST(AssignmentPatternFormat, DISABLED_AStringLiteralPrintsQuoted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial $display(\"%p\", \"hi\");\n"
                       "endmodule\n",
                       f),
            "\"hi\"\n");
}

TEST(AssignmentPatternFormat, DISABLED_ANullEventPrintsNull) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  event e;\n"
                       "  initial begin\n"
                       "    e = null;\n"
                       "    $display(\"%p\", e);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "null\n");
}

TEST(AssignmentPatternFormat, ANullInterfaceClassHandlePrintsNull) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  interface class I;\n"
                       "  endclass\n"
                       "  I h;\n"
                       "  initial $display(\"%p\", h);\n"
                       "endmodule\n",
                       f),
            "null\n");
}

}  // namespace
