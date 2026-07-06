#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DataHidingElaboration, PublicMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMemberAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.hidden = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMethodAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  local function int get_id();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.get_id();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, PublicMethodAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function void show(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.show();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMethodAccessError) {
  EXPECT_FALSE(
      ElabOk("class Packet;\n"
             "  protected function void secret(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.secret();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorLocalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorProtectedAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.18: local members are not visible within subclasses.
// A base-class local accessed through a derived handle is still rejected.
TEST(DataHidingElaboration, LocalNotVisibleViaDerivedHandle) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    d = new;\n"
             "    d.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.18: a protected member has all the characteristics of a local member
// except that it is inherited / visible to subclasses. A subclass method
// may reference an inherited protected property.
TEST(DataHidingElaboration, ProtectedAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int read_hidden();\n"
             "    return hidden;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: the visible-to-subclasses characteristic of a protected member applies
// to methods as well as properties. A subclass method may call an inherited
// protected method — the method form of the preceding property test.
TEST(DataHidingElaboration, ProtectedMethodAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected function int secret();\n"
             "    return 7;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int reveal();\n"
             "    return secret();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: within a class, a local property of the same class may be
// referenced even if it is in a different instance of the same class.
TEST(DataHidingElaboration, SameClassInstanceLocalAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

// §8.18: a protected member has all the characteristics of a local member
// (differing only in being inheritable). The same-class cross-instance
// reference permitted for a local property is therefore equally permitted for a
// protected one: a method may read a protected property of another instance of
// its own class.
TEST(DataHidingElaboration, SameClassInstanceProtectedAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  protected int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

}  // namespace
