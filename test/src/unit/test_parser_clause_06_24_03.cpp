// §6.24.3: Bit-stream casting

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =========================================================================
// §6.24.3: Bit-stream casting
// =========================================================================
TEST(ParserSection6, BitstreamCastStructToInt) {
  // §6.24.3: Cast between bit-stream types (struct to int).
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

TEST(ParserSection6, BitstreamCastIntToStruct) {
  // §6.24.3: Cast from int to packed struct (bit-stream).
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  initial begin\n"
      "    ab_t s;\n"
      "    s = ab_t'(16'hABCD);\n"
      "  end\n"
      "endmodule\n"));
}
// =========================================================================
// §6.24.3 -- Bit-stream casting
// =========================================================================
TEST(ParserSection6, BitStreamCastToType) {
  auto r = Parse("module t;\n"
                 "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
                 "  initial begin\n"
                 "    pair_t p;\n"
                 "    p = pair_t'(8'hAB);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastFromStruct) {
  auto r = Parse("module t;\n"
                 "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
                 "  initial begin\n"
                 "    pair_t p;\n"
                 "    logic [7:0] flat;\n"
                 "    flat = logic [7:0]'(p);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

} // namespace
