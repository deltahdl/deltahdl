#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassExtendElaboration, VirtualClassPartialImplOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassExtendElaboration, ConcreteClassCompletesPartialOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "  virtual function bit funcA();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "class ClassB extends ClassA;\n"
             "  virtual function bit funcB();\n"
             "    return 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassExtendElaboration, VirtualClassNoImplOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfClass;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "virtual class ClassA implements IntfClass;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
