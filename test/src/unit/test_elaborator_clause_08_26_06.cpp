// §8.26.6

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Req: When a class implements multiple interface classes, identifiers are
// merged from different name spaces into a single name space.

TEST(InterfaceClassNameMerging, ImplementsMultipleMergesDistinctMethods) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "class C implements IA, IB;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Req: When an interface class extends multiple interface classes, identifiers
// are merged from different name spaces into a single name space.

TEST(InterfaceClassNameMerging, ExtendsMultipleMergesDistinctMethods) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "endclass\n"
             "class D implements IC;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassNameMerging, TransitiveMergeViaExtendsChain) {
  EXPECT_TRUE(
      ElabOk("interface class IA;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class IB;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class IC extends IA, IB;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "class D implements IC;\n"
             "  virtual function void fa();\n"
             "  endfunction\n"
             "  virtual function void fb();\n"
             "  endfunction\n"
             "  virtual function void fc();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
