#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.11: naming a property in randomize()'s inline argument list changes that
// property's random mode. The random mode of a local member may only be changed
// from a scope that can reach the member, so naming it through an external
// class handle is illegal.
TEST(InlineRandomControlVisibility, LocalMemberArgRejectedFromOutside) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  local rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    obj.randomize(x);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.11: a protected member is reachable only within its class hierarchy, so
// naming it as a randomize() argument through an external handle is rejected on
// the same basis.
TEST(InlineRandomControlVisibility, ProtectedMemberArgRejectedFromOutside) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  protected rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    obj.randomize(x);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.11: a public property carries no access restriction, so naming it as a
// randomize() argument through an external handle is allowed. This source
// matches the rejected cases with only the visibility qualifier changed, so the
// difference in outcome isolates the random-mode access rule.
TEST(InlineRandomControlVisibility, PublicMemberArgAcceptedFromOutside) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    obj.randomize(x);\n"
             "  end\n"
             "endmodule\n"));
}

// 18.11: the random mode of a local member may be changed by a randomize()
// argument list from a scope that can reach that member -- namely from within
// the class in which the local member is declared. Naming the local member in a
// randomize() call inside one of the class's own methods therefore elaborates
// cleanly, in contrast to the same name being rejected through an external
// handle. This is the accepting side of the access rule, with the member's
// visibility unchanged from the rejected case and only the calling scope moved
// inside the class.
TEST(InlineRandomControlVisibility, LocalMemberArgAcceptedWithinClassScope) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local rand int x;\n"
             "  function int roll();\n"
             "    return this.randomize(x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  int r;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    r = obj.roll();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
