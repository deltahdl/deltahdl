#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StaticClassPropertyElaboration, BasicStaticPropertyOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  static integer fileID;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(StaticClassPropertyElaboration, StaticPropertyWithInitializerOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  static int count = 0;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(StaticClassPropertyElaboration, MixedStaticAndInstanceOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int shared_val;\n"
             "  int inst_val;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(StaticClassPropertyElaboration, AccessViaInstanceOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  static int fileID;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    p = new;\n"
             "    p.fileID = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StaticClassPropertyElaboration, AccessViaScopeOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  static int fileID;\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial begin\n"
             "    x = Packet::fileID;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StaticClassPropertyElaboration, MultipleStaticDeclaratorsOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int a, b;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

}  // namespace
