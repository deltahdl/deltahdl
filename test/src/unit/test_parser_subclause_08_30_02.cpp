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
  // NOTE: weak0/weak1/strong0/strong1 are reserved drive-strength keywords
  // (Annex B / Table B.1), so they cannot name variables here.
  EXPECT_TRUE(
      ParseOk("class obj;\n"
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
