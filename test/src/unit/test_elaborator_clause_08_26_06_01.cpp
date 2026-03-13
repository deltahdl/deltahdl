// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodConflict, SingleImplResolvesConflict) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase1;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfBase2;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "class ClassExt implements IntfBase1, IntfBase2;\n"
             "  virtual function bit funcBase();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ExtendsImplementsConflict, ExtendsAndImplementsConflictOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IntfBase1;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfBase2;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "virtual class ClassBase;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "class ClassExt extends ClassBase implements IntfBase1, IntfBase2;\n"
      "  virtual function bit funcBase();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
