#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, ClassWithMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "  function int get_data();\n"
             "    return data;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, MethodCallOnInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function int current_status();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    automatic int s;\n"
             "    s = p.current_status();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
