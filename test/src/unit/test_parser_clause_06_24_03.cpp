// §6.24.3: Bit-stream casting

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

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

}  // namespace
