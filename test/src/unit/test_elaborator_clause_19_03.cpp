#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §19.3 (footnote 29): the extends specification of a covergroup is allowed
// only within a class. The Annex A grammar accepts `covergroup extends base ;`
// in any scope, so the restriction is applied at elaboration. A derived
// covergroup declared at module scope has no enclosing class and is illegal.
TEST(CovergroupExtendsScope, ExtendsInModuleError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  covergroup cg extends base_cg;\n"
             "  endgroup\n"
             "endmodule\n"));
}

// §19.3 (footnote 29): the named `covergroup child extends parent ;` spelling
// is the same extends form and is likewise illegal outside a class.
TEST(CovergroupExtendsScope, NamedExtendsInModuleError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  covergroup child extends parent;\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "endmodule\n"));
}

// §19.3 (footnote 29): a covergroup that does NOT use extends is legal at
// module scope, so the check must not reject an ordinary covergroup.
TEST(CovergroupExtendsScope, NonExtendsCovergroupInModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [2:0] addr;\n"
             "  covergroup cg @(addr);\n"
             "    coverpoint addr;\n"
             "  endgroup\n"
             "endmodule\n"));
}

// §19.3 (footnote 29): the extends form is permitted within a class. The base
// covergroup is defined in a superclass, so the derived embedded covergroup
// elaborates without the "outside class" error.
TEST(CovergroupExtendsScope, ExtendsInsideClassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "  covergroup cg @(posedge clk);\n"
             "    coverpoint x;\n"
             "  endgroup\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  covergroup cg extends cg;\n"
             "  endgroup\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
