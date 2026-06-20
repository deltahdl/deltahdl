#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakRefNewWithReferent) {
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
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefNewWithNull) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(obj) wr;\n"
              "    wr = new(null);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakRefTwoInstancesSameReferent) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj strong_obj;\n"
              "    weak_reference #(obj) weak1, weak2;\n"
              "    strong_obj = new();\n"
              "    weak1 = new(strong_obj);\n"
              "    weak2 = new(strong_obj);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
