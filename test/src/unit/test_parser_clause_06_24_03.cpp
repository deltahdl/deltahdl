#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, BitstreamCastStructToInt) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [15:0] hi; logic [15:0] lo; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    int x;\n"
      "    x = int'(p);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(DataTypeParsing, BitstreamCastIntToStruct) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  initial begin\n"
      "    ab_t s;\n"
      "    s = ab_t'(16'hABCD);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(DataTypeParsing, BitStreamCastToType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    p = pair_t'(8'hAB);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(DataTypeParsing, BitStreamCastFromStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    logic [7:0] flat;\n"
      "    flat = logic [7:0]'(p);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(DataTypeParsing, BitstreamCastStructToStruct) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  typedef struct packed { logic [3:0] w; logic [3:0] x;\n"
      "                          logic [3:0] y; logic [3:0] z; } wxyz_t;\n"
      "  initial begin\n"
      "    ab_t src;\n"
      "    wxyz_t dst;\n"
      "    dst = wxyz_t'(src);\n"
      "  end\n"
      "endmodule\n"));
}

TEST(DataTypeParsing, BitstreamCastStringType) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef bit [$bits(int)-1:0] tagbits;\n"
              "  int x;\n"
              "  tagbits t_val;\n"
              "  initial t_val = tagbits'(x);\n"
              "endmodule\n"));
}

}  // namespace
