#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakRefClearCallParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj strong_obj;\n"
              "    weak_reference #(obj) wr;\n"
              "    strong_obj = new();\n"
              "    wr = new(strong_obj);\n"
              "    wr.clear();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefClearAsStandaloneStatementParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(obj) wr;\n"
              "    wr = new(null);\n"
              "    wr.clear();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefClearThenGetParses) {
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
              "    wr.clear();\n"
              "    result = wr.get();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
