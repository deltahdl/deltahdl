#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA609, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §8.6: Class with methods elaborates successfully.
TEST(ElabA86, ClassWithMethodElaborates) {
  EXPECT_TRUE(ElabOk(
      "class Packet;\n"
      "  int data;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "endmodule\n"));
}

// §8.6: Method call on class instance elaborates.
TEST(ElabA86, MethodCallOnInstanceElaborates) {
  EXPECT_TRUE(ElabOk(
      "class Packet;\n"
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
