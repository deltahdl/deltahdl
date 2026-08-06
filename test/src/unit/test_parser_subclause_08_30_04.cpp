#include "fixture_parser.h"

using namespace delta;

namespace {

// §8.30.4: the void clear() method is a legal standalone statement call. The
// referent value and any following statement do not change what the parser
// accepts, so a single accepting form covers the parse of the clear() call.
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

}  // namespace
