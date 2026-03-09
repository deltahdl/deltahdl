

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA8263, TypesInheritedByExtendingInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfA;\n"
             "  typedef int my_t;\n"
             "  pure virtual function void funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfA;\n"
             "  pure virtual function void funcB();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8263, ImplementingClassScopeResOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfC;\n"
             "  pure virtual function void funcC();\n"
             "endclass\n"
             "class ClassA implements IntfC;\n"
             "  virtual function void funcC();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
