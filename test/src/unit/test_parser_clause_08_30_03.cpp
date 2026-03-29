#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakRefGetCallParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj strong_obj;\n"
              "    weak_reference #(obj) wr;\n"
              "    obj result;\n"
              "    strong_obj = new();\n"
              "    wr = new(strong_obj);\n"
              "    result = wr.get();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefGetNullComparisonParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(obj) wr;\n"
              "    wr = new(null);\n"
              "    if (wr.get() == null)\n"
              "      $display(\"null\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefGetInWaitParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(obj) wr;\n"
              "    wr = new(null);\n"
              "    wait (wr.get() == null);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
