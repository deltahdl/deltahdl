#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.6.1: Single implementation resolves same-name methods from two
// interfaces — OK.
TEST(ElabA82661, SingleImplResolvesConflictOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IntfBase1;\n"
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

// §8.26.6.1: Extends abstract + implements interface — single impl OK.
TEST(ElabA82661, ExtendsAndImplementsConflictOk) {
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

// §8.26.6.1: Inherited method from base class satisfies interface — OK.
TEST(ElabA82661, InheritedMethodSatisfiesInterfaceOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IntfClass;\n"
      "  pure virtual function bit funcBase();\n"
      "  pure virtual function bit funcExt();\n"
      "endclass\n"
      "class BaseClass;\n"
      "  virtual function bit funcBase();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class ExtClass extends BaseClass implements IntfClass;\n"
      "  virtual function bit funcExt();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
