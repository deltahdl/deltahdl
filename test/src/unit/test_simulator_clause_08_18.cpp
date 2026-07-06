#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// §8.18 Data hiding and encapsulation — runtime facet.
//
// Access control (local/protected/public) is enforced entirely at compile time
// (parse + elaborate); the simulator never re-checks it. What §8.18 states
// about runtime is therefore indirect but real: because the restriction is
// compile-time only, a local or protected member is an ordinary, fully
// functioning property at run time, and the same-class cross-instance access
// the clause permits actually evaluates and returns the comparison result.
// These tests build each scenario from the dependency subclauses' real syntax —
// §8.5 properties, §8.6 methods, §8.13 inheritance — and drive it through the
// full pipeline (parse → elaborate → lower → run), observing the value produced
// rather than hand-building runtime type info.

namespace {

// A plain (unqualified) property is public and, at run time, is ordinary
// read/write storage reached through the object handle.
TEST(DataHidingSimulation, PublicPropertyReadWriteAtRuntime) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.x = 7;\n"
                      "    result = p.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

// A local property is only a compile-time visibility restriction: at run time
// it is normal storage. A public method of the same class writes it and another
// reads it back, so the value survives the round trip.
TEST(DataHidingSimulation, LocalPropertyIsRealRuntimeStorage) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int secret;\n"
                      "  function void store(int v);\n"
                      "    secret = v;\n"
                      "  endfunction\n"
                      "  function int fetch();\n"
                      "    return secret;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    p.store(42);\n"
                      "    result = p.fetch();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §8.18: within a class, a local member of the same class may be referenced
// through a different instance. The clause's compare example states that
// this.i shall be compared to other.i and the logical result returned. With two
// packets holding the same value, the equality yields 1.
TEST(DataHidingSimulation, CrossInstanceLocalCompareEqualReturnsOne) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int i;\n"
                      "  function void set_i(int v);\n"
                      "    i = v;\n"
                      "  endfunction\n"
                      "  function int compare(Packet other);\n"
                      "    return (this.i == other.i);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet a;\n"
                      "    Packet b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.set_i(5);\n"
                      "    b.set_i(5);\n"
                      "    result = a.compare(b);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// The negative counterpart of the compare example: the same cross-instance
// local access reads the differing values of the two packets and returns 0.
// This observes that other.i is truly read (not ignored) at run time.
TEST(DataHidingSimulation, CrossInstanceLocalCompareUnequalReturnsZero) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  local int i;\n"
                      "  function void set_i(int v);\n"
                      "    i = v;\n"
                      "  endfunction\n"
                      "  function int compare(Packet other);\n"
                      "    return (this.i == other.i);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet a;\n"
                      "    Packet c;\n"
                      "    a = new;\n"
                      "    c = new;\n"
                      "    a.set_i(5);\n"
                      "    c.set_i(9);\n"
                      "    result = a.compare(c);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §8.18: a protected member has all the characteristics of a local member
// except that it is inherited and visible to subclasses. At run time the
// inherited protected property is a single real storage location on the derived
// object: a base method writes it, a derived method reads it back.
TEST(DataHidingSimulation, ProtectedMemberInheritedRuntime) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  protected int hidden;\n"
                      "  function void set_hidden(int v);\n"
                      "    hidden = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function int read_hidden();\n"
                      "    return hidden;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.set_hidden(99);\n"
                      "    result = d.read_hidden();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §8.18: a nonlocal (public) method that accesses a local member can be
// inherited and works properly as a method of the subclass. Base's public
// store/fetch touch the base local; a Derived that redefines nothing inherits
// them, and calling the inherited methods on a Derived object round-trips the
// local value. Built from §8.13 extends + §8.5 local property + §8.6 methods.
TEST(DataHidingSimulation, InheritedPublicMethodAccessesBaseLocal) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  local int secret;\n"
                      "  function void store(int v);\n"
                      "    secret = v;\n"
                      "  endfunction\n"
                      "  function int fetch();\n"
                      "    return secret;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    d.store(33);\n"
                      "    result = d.fetch();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

// §8.18: a protected method, being visible to subclasses, can be invoked from a
// subclass method and works at run time. Base's protected secret() is called by
// Derived's public reveal(); calling reveal() on a Derived object returns the
// protected method's result. This is the method-form runtime counterpart of the
// inherited protected property test. Built from §8.13 extends + §8.6 methods.
TEST(DataHidingSimulation, InheritedProtectedMethodCalledFromSubclass) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  protected function int secret();\n"
                      "    return 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function int reveal();\n"
                      "    return secret();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = d.reveal();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

}  // namespace
