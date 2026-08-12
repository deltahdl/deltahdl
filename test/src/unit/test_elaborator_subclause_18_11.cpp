#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §18.11 states "The random mode of local class members can only be changed
// when the call to randomize() has access to those properties, that is, within
// the scope of the class in which the local members are declared." Naming a
// property in randomize()'s inline argument list changes that property's random
// mode, so naming a local member through an external class handle is illegal.
TEST(InlineRandomControlVisibility, LocalMemberArgRejectedFromOutside) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  local rand int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    obj.randomize(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(
      f, "cannot change random mode of local member from outside its class");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "18.11");
}

// §18.11 conditions the change of random mode on the call having "access to
// those properties". A protected member is reachable only within its class
// hierarchy, so naming it as a randomize() argument through an external handle
// is rejected under the same sentence.
TEST(InlineRandomControlVisibility, ProtectedMemberArgRejectedFromOutside) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  protected rand int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    obj.randomize(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f,
               "cannot change random mode of protected member from outside its "
               "class hierarchy");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "18.11");
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
